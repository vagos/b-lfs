#!/usr/bin/env python3

from __future__ import annotations

import argparse
import os
import subprocess
from dataclasses import dataclass
from pathlib import Path

try:
    from libdash import parser as libdash_parser
except ImportError as exc:
    raise SystemExit(
        "libdash is not installed. Create a virtualenv and run "
        "`pip install -r requirements.txt` from the repo root."
    ) from exc


class TranslationError(Exception):
    pass


@dataclass(frozen=True)
class PathSpec:
    components: tuple[str, ...]


@dataclass(frozen=True)
class Operation:
    kind: str
    line: int
    text: str
    path: PathSpec | None = None
    src: PathSpec | None = None
    dest_parent: PathSpec | None = None
    name: str | None = None


SPECIAL_COMPONENTS = {".", ".."}


def decode_word(word: list[object], line: int) -> str:
    chars: list[str] = []
    for fragment in word:
        chars.extend(decode_fragment(fragment, line))
    return "".join(chars)


def decode_fragment(fragment: object, line: int) -> list[str]:
    if not isinstance(fragment, list) or not fragment:
        raise TranslationError(f"line {line}: unexpected libdash fragment: {fragment!r}")

    tag = fragment[0]
    if tag in {"C", "E"}:
        return [chr(fragment[1])]
    if tag == "Q":
        return list(decode_word(fragment[1], line))

    names = {
        "V": "parameter expansion",
        "B": "command substitution",
        "A": "arithmetic expansion",
        "T": "tilde expansion",
    }
    detail = names.get(tag, f"fragment kind {tag!r}")
    raise TranslationError(f"line {line}: unsupported shell feature: {detail}")


def flatten_command_ast(node: object, line: int) -> list[object]:
    if not isinstance(node, list) or len(node) != 2:
        raise TranslationError(f"line {line}: unexpected AST node shape: {node!r}")

    tag, payload = node
    if tag == "Command":
        return [node]
    if tag == "Semi":
        left, right = payload
        return flatten_command_ast(left, line) + flatten_command_ast(right, line)

    raise TranslationError(f"line {line}: unsupported shell syntax node {tag!r}")


def parse_path(raw: str, line: int, role: str) -> PathSpec:
    if raw == "":
        raise TranslationError(f"line {line}: empty {role} path is not supported")

    if raw == "/":
        return PathSpec(())

    components = tuple(part for part in raw.split("/") if part != "")
    return PathSpec(components)


def split_parent_and_name(raw: str, line: int, role: str) -> tuple[PathSpec, str]:
    spec = parse_path(raw, line, role)
    if not spec.components:
        raise TranslationError(f"line {line}: {role} path {raw!r} does not name an entry")

    name = spec.components[-1]
    if name in SPECIAL_COMPONENTS:
        raise TranslationError(
            f"line {line}: {role} path {raw!r} must end in a concrete name, not {name!r}"
        )

    return PathSpec(spec.components[:-1]), name


def parse_rm(argv: list[str], line: int, text: str) -> Operation:
    recursive = False
    target: str | None = None

    for arg in argv[1:]:
        if target is None and arg.startswith("-") and len(arg) > 1:
            flags = set(arg[1:])
            if not flags <= {"r", "R", "f"}:
                raise TranslationError(f"line {line}: unsupported rm flags in {arg!r}")
            if "r" in flags or "R" in flags:
                recursive = True
            continue

        if target is not None:
            raise TranslationError(f"line {line}: only one rm target is supported")
        target = arg

    if target is None:
        raise TranslationError(f"line {line}: rm needs exactly one target")

    return Operation(
        kind="rmr" if recursive else "rm",
        line=line,
        text=text,
        path=parse_path(target, line, "rm target"),
    )


def parse_operation(argv: list[str], line: int, text: str) -> Operation:
    command = argv[0]

    if command == "mkdir":
        if len(argv) != 2:
            raise TranslationError(f"line {line}: mkdir needs exactly one path")
        parent, name = split_parent_and_name(argv[1], line, "mkdir")
        return Operation("mkdir", line, text, dest_parent=parent, name=name)

    if command == "touch":
        if len(argv) != 2:
            raise TranslationError(f"line {line}: touch needs exactly one path")
        parent, name = split_parent_and_name(argv[1], line, "touch")
        return Operation("touch", line, text, dest_parent=parent, name=name)

    if command == "rm":
        return parse_rm(argv, line, text)

    if command == "mv":
        if len(argv) != 3:
            raise TranslationError(f"line {line}: mv needs a source and destination")
        parent, name = split_parent_and_name(argv[2], line, "mv destination")
        return Operation(
            "mv",
            line,
            text,
            src=parse_path(argv[1], line, "mv source"),
            dest_parent=parent,
            name=name,
        )

    if command == "cp":
        if len(argv) != 3:
            raise TranslationError(f"line {line}: cp needs a source and destination")
        parent, name = split_parent_and_name(argv[2], line, "cp destination")
        return Operation(
            "cp",
            line,
            text,
            src=parse_path(argv[1], line, "cp source"),
            dest_parent=parent,
            name=name,
        )

    raise TranslationError(f"line {line}: unsupported command {command!r}")


def parse_script(script_path: Path) -> list[Operation]:
    operations: list[Operation] = []
    for ast, parsed_text, line_start, _line_end in libdash_parser.parse(str(script_path)):
        line = line_start + 1
        text = (parsed_text or "").strip() or f"<command on line {line}>"
        for command_node in flatten_command_ast(ast, line):
            _tag, payload = command_node
            _lineno, assigns, args, redirs = payload
            if assigns:
                raise TranslationError(f"line {line}: variable assignments are not supported")
            if redirs:
                raise TranslationError(f"line {line}: redirections are not supported")

            argv = [decode_word(word, line) for word in args]
            if not argv:
                raise TranslationError(f"line {line}: empty commands are not supported")

            operations.append(parse_operation(argv, line, text))

    if not operations:
        raise TranslationError("the shell script did not contain any supported commands")

    return operations


def register_name(name: str, name_atoms: dict[str, str]) -> None:
    if name not in name_atoms:
        name_atoms[name] = f"GeneratedName{len(name_atoms)}"


def collect_symbols(operations: list[Operation]) -> tuple[dict[str, str], dict[str, str], dict[PathSpec, str]]:
    name_atoms: dict[str, str] = {}
    comp_atoms: dict[str, str] = {}
    path_atoms: dict[PathSpec, str] = {}

    def register_path(spec: PathSpec | None) -> None:
        if spec is None or spec in path_atoms:
            return
        path_atoms[spec] = f"GeneratedPath{len(path_atoms)}"
        for component in spec.components:
            if component in SPECIAL_COMPONENTS:
                continue
            register_name(component, name_atoms)
            if component not in comp_atoms:
                comp_atoms[component] = f"GeneratedComp{len(comp_atoms)}"

    for op in operations:
        register_path(op.path)
        register_path(op.src)
        register_path(op.dest_parent)
        if op.name is not None:
            register_name(op.name, name_atoms)

    return name_atoms, comp_atoms, path_atoms


def component_ref(component: str, comp_atoms: dict[str, str]) -> str:
    if component == ".":
        return "Dot"
    if component == "..":
        return "DotDot"
    return comp_atoms[component]


def render_path_binding(path_atom: str, spec: PathSpec, comp_atoms: dict[str, str]) -> str:
    if not spec.components:
        return f"    no {path_atom}.segs"

    parts = [
        f"({index} -> {component_ref(component, comp_atoms)})"
        for index, component in enumerate(spec.components)
    ]
    return f"    {path_atom}.segs = " + " + ".join(parts)


def render_operation(op: Operation, index: int, name_atoms: dict[str, str], path_atoms: dict[PathSpec, str]) -> str:
    if op.kind == "mkdir":
        return (
            f"some dir{index}: Dir | "
            f"mkdirPath[Root, {path_atoms[op.dest_parent]}, {name_atoms[op.name]}, dir{index}]"
        )
    if op.kind == "touch":
        return (
            f"some file{index}: File | "
            f"touchPath[Root, {path_atoms[op.dest_parent]}, {name_atoms[op.name]}, file{index}]"
        )
    if op.kind == "rm":
        return f"rmPath[Root, {path_atoms[op.path]}]"
    if op.kind == "rmr":
        return f"rmrPath[Root, {path_atoms[op.path]}]"
    if op.kind == "mv":
        return (
            f"mvPath[Root, {path_atoms[op.src]}, {path_atoms[op.dest_parent]}, {name_atoms[op.name]}]"
        )
    if op.kind == "cp":
        return (
            f"some file{index}: File | "
            f"cpPath[Root, {path_atoms[op.src]}, {path_atoms[op.dest_parent]}, "
            f"{name_atoms[op.name]}, file{index}]"
        )
    raise AssertionError(f"unreachable operation kind: {op.kind}")


def render_operation_sequence(
    operations: list[Operation],
    name_atoms: dict[str, str],
    path_atoms: dict[PathSpec, str],
    index: int = 0,
    indent: str = "    ",
) -> list[str]:
    line = indent + render_operation(operations[index], index, name_atoms, path_atoms)
    if index == len(operations) - 1:
        return [line]

    return [
        line,
        indent + "next_state {",
        *render_operation_sequence(operations, name_atoms, path_atoms, index + 1, indent + "    "),
        indent + "}",
    ]


def compute_scopes(
    operations: list[Operation],
    name_atoms: dict[str, str],
    comp_atoms: dict[str, str],
    path_atoms: dict[PathSpec, str],
) -> dict[str, int]:
    dir_creations = sum(1 for op in operations if op.kind == "mkdir")
    file_creations = sum(1 for op in operations if op.kind in {"touch", "cp"})
    dir_scope = 1 + dir_creations
    file_scope = max(1, file_creations)
    path_scope = len(path_atoms)

    return {
        "FsObj": dir_scope + file_scope,
        "Dir": dir_scope,
        "File": file_scope,
        "Name": len(name_atoms),
        "Component": len(comp_atoms) + 2,
        "Path": path_scope,
        "PathEval": dir_scope * path_scope,
    }


def render_model(
    operations: list[Operation],
    script_path: Path,
    output_path: Path,
    base_model_path: Path,
    expected_result: str,
) -> str:
    name_atoms, comp_atoms, path_atoms = collect_symbols(operations)
    scopes = compute_scopes(operations, name_atoms, comp_atoms, path_atoms)
    base_ref = os.path.relpath(base_model_path, output_path.parent).replace(os.sep, "/")

    lines = [
        "#lang forge/temporal",
        "",
        f'open "{base_ref}"',
        "",
        f"-- Generated from {script_path.as_posix()} by scripts/shell_to_forge.py",
        "",
    ]

    for atom in name_atoms.values():
        lines.append(f"one sig {atom} extends Name {{}}")
    if name_atoms:
        lines.append("")

    for atom in comp_atoms.values():
        lines.append(f"one sig {atom} extends NameComp {{}}")
    if comp_atoms:
        lines.append("")

    for atom in path_atoms.values():
        lines.append(f"one sig {atom} extends Path {{}}")
    lines.append("")

    lines.append("pred generatedPaths {")
    if not comp_atoms and not path_atoms:
        lines.append("    true")
    else:
        for name, atom in comp_atoms.items():
            lines.append(f"    {atom}.label = {name_atoms[name]}")
        for spec, atom in path_atoms.items():
            lines.append(render_path_binding(atom, spec, comp_atoms))
    lines.append("}")
    lines.append("")

    lines.append("pred generatedScript {")
    lines.append("    trace")
    lines.append("    generatedPaths")
    lines.extend(render_operation_sequence(operations, name_atoms, path_atoms))
    lines.append("}")
    lines.append("")

    lines.append("test expect generatedScriptTests {")
    lines.append(f"    generatedScript{expected_result.capitalize()}: {{")
    lines.append("        generatedScript")
    lines.append(
        "    } for "
        f"{scopes['FsObj']} FsObj, {scopes['Dir']} Dir, {scopes['File']} File, "
        f"{scopes['Name']} Name, {scopes['Component']} Component, "
        f"{scopes['Path']} Path, {scopes['PathEval']} PathEval is {expected_result}"
    )
    lines.append("}")
    lines.append("")

    return "\n".join(lines)


def generate(
    script_path: Path,
    output_path: Path,
    base_model_path: Path,
    expected_result: str,
) -> str:
    operations = parse_script(script_path)
    return render_model(operations, script_path, output_path, base_model_path, expected_result)


def default_output_path(script_path: Path) -> Path:
    return script_path.with_name(f"{script_path.stem}.model.frg")


def run_racket(output_path: Path) -> int:
    proc = subprocess.run(
        ["racket", output_path.name, "-O", "run_sterling", "off"],
        cwd=output_path.parent,
    )
    return proc.returncode


def main() -> int:
    cli = argparse.ArgumentParser(
        description="Parse a shell script with libdash and emit a Forge model."
    )
    cli.add_argument("script", type=Path, help="shell script to translate")
    cli.add_argument(
        "-o",
        "--output",
        type=Path,
        help="generated Forge output path; defaults to {script_name}.model.frg",
    )
    cli.add_argument(
        "--base-model",
        type=Path,
        default=Path("file-system.frg"),
        help="Forge base model that the generated file opens",
    )
    cli.add_argument(
        "--no-run",
        action="store_true",
        help="only generate the Forge file",
    )
    cli.add_argument(
        "--expect",
        choices=("sat", "unsat"),
        default="sat",
        help="expected satisfiability of the generated script trace",
    )
    args = cli.parse_args()

    script_path = args.script.resolve()
    output_path = (
        args.output.resolve()
        if args.output is not None
        else default_output_path(script_path).resolve()
    )
    base_model_path = args.base_model.resolve()

    if not script_path.exists():
        raise SystemExit(f"script not found: {script_path}")
    if not base_model_path.exists():
        raise SystemExit(f"base model not found: {base_model_path}")

    try:
        model = generate(script_path, output_path, base_model_path, args.expect)
    except TranslationError as exc:
        raise SystemExit(str(exc)) from exc

    output_path.write_text(model)
    print(f"wrote {output_path}", flush=True)

    if args.no_run:
        return 0

    return run_racket(output_path)


if __name__ == "__main__":
    raise SystemExit(main())
