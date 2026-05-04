# Modeling a UNIX-Style File System with Path Resolution

## Overview
This project studies a simplified UNIX-style file system in Forge. It will model the file-system tree and several commands as state transitions. The model will include named paths, including nonlinear path components such as `.` and `..`.
Filesystem bugs are ubiquitous and often involve edge cases in path resolution, so this project will use modeling to explore how path semantics can lead to surprising behaviors, especially around destructive operations like recursive removal.

## Goals
Our goal is to use modeling to expose edge cases in path-based command semantics.

### Foundation
The basic model is a rooted file-system tree with files, directories, liveness, parent pointers, and command transitions for `touch`, `mkdir`, `rm`, `rmr`, `mv`, and `cp`.
The main leap between this model and the one we implemented for our midterm is that this will be implemented using _temporal forge_.

Scope at this level:

- Core: rooted tree structure, live/dead objects, trace-based command execution, structural invariants, and tests for command preconditions and postconditions
- Closely related: small trace exploration and custom visualization of state changes
- Unrelated / left out: names, paths, `.` and `..`, permissions, links, file contents, concurrency, and large scopes

The intended outcome at this level is a stable Forge model with tests showing that each predicate behaves as intended and that the baseline commands preserve well-formedness.

### Target
The project we plan to hand in extends the baseline model with names and explicit path objects. Commands should resolve paths relative to a base directory rather than operating on objects directly.

Scope at this level:

- Core: named children, path components, path resolution, normalization, and path-based versions of the filesystem commands
- Closely related: equivalence or mismatch tests comparing raw-path behavior with normalized-path behavior on edge cases such as `a/b/..`
- Unrelated / left out: symbolic links, permission semantics, file contents, shell parsing, and realistic filesystem scale

The intended outcome at this level is a tested model that can explain at least one nontrivial path-resolution bug or semantic surprise, especially around destructive operations like recursive removal.

### Reach
The stretch goal is to go beyond basic path resolution and analyze higher-level semantic questions that are interesting but may be difficult to complete cleanly in scope.

Possible reach directions:

- model limited permission constraints
- study equivalence or non-equivalence between different command sequences over paths
- improve the visualization so traces show not just state differences, but also which command and path were used at each step

The intended outcome at this level is not just more features, but a sharper claim about what normalization or path semantics changes in the model.

We have used the model to derive some equivalence analysis for sequences of command invocations on paths:

- `touch p; rm p` is checked as a no-op
- `mv p q; rm q` is checked against direct `rm p`
- `rm -r a/b/..` is checked as equivalent to `rm -r a`
- `rm -r a/b/..` is also checked as non-equivalent to `rm -r a/b`

At all three levels, testing is part of the goal. We are not only checking high-level properties; we are also testing that predicates such as resolution, normalization, and command transitions behave the way we intend on small examples and edge cases.

## Current Model
The temporal Forge model is in `file-system.frg`.

The base model uses:

- `FsObj`, `File`, and `Dir` to represent abstract file-system objects
- `State` to represent a snapshot of the system
- `live` to track which objects exist in a state
- `parent` to encode the directory tree
- `root` for the unique root directory
- `next` to build a linear trace of command executions

The baseline invariants require that:

- the root is always live
- the root has no parent
- every live non-root object has a live parent
- the parent relation is acyclic
- every live object is reachable from the root

The transition predicates model `touch`, `mkdir`, `rm`, `rmr`, `mv`, and `cp` as pre/post-state relations. The trace model starts from an `init` state and requires every `next` step to satisfy one of those command predicates.

## Testing and Checking
The Forge model includes:

- satisfiability tests for initialization, well-formed states, and traces
- precondition tests for each command
- preservation checks showing that each command maintains well-formedness
- trace-level tests for valid and invalid command sequences
- assertions that the root never changes and is always live

These checks let us distinguish behaviors that should be possible, such as `touch` followed by `rm`, from behaviors that should be impossible, such as deleting an object and then moving it later in the same trace.

## Shell-To-Forge CLI
This project also supports verification and visualization of a narrow class of, but otherwise unmodified, shell programs.

The CLI in `scripts/shell_to_forge.py` parses a shell script and emits a small generated Forge harness into `{script_name}.model.frg` that opens `../file-system.frg`. By default it then invokes `racket ... -O run_sterling off` so Forge executes the generated `test expect` block, checking whether the filesystem modification commands in the script can be satisfied by the model.

With `--viz`, the harness instead contains a `run` block and Sterling is left enabled, so the trace renders using the spytial-core spec in `file-system.cnd`. Adding `--buggy` to a `--viz` invocation swaps each `rm -r` for the model's raw recursive rmr semantics (re-resolving the path on every step), exhibiting the `rmr a/b/..` bug in Sterling.

Setup:

- `python3 -m venv .venv`
- `.venv/bin/pip install -r requirements.txt`

Run (verification mode):

- `.venv/bin/python scripts/shell_to_forge.py examples/demo.sh`
- `.venv/bin/python scripts/shell_to_forge.py examples/wrong.sh --expect unsat`

Run (visualization mode):

- `.venv/bin/python scripts/shell_to_forge.py examples/demo.sh --viz` — correct semantics; the trace removes the `a` subtree cleanly.
- `.venv/bin/python scripts/shell_to_forge.py examples/demo.sh --viz --buggy` — same script with raw recursive rmr; the trace gets stuck mid-deletion with `a` orphaned.

Other flags:

- `--no-run` — generate the `.model.frg` without invoking racket.
- `--expect {sat,unsat}` — expected satisfiability for verification mode (default `sat`). `--viz` requires `--expect sat`; combining with `unsat` is rejected up front since there is no witness trace to render.
- `--buggy` — render `rm -r` using raw recursive rmr semantics. Requires `--viz`. The script must contain exactly one `rm -r` and it must be the last command, since the buggy semantics consumes the rest of the trace.

The translator supports simple literal-path uses of `mkdir`, `touch`, `rm`, `rm -r`, `mv`, and `cp`, and rejects redirections, substitutions, and shell control flow.

## Planned Path Extension
The next version of the model introduces names and path components:

```forge
abstract sig FsObj {}
sig File, Dir extends FsObj {}
sig Name {}

abstract sig Component {}
sig NameComp extends Component { name: one Name }
one sig Dot, DotDot extends Component {}

sig Path {
  segs: pfunc Int -> Component
}
```

Instead of resolving commands directly against objects, commands will take paths. Resolution will be modeled inductively from a base directory:

- `NameComp(n)` looks up a named child
- `Dot` keeps the current object unchanged
- `DotDot` moves to the parent, except that root stays at root

The main motivating edge case is:

`rmr a/b/..`

After normalization, this path should behave like `rmr a/.`, so both should delete the same directory. If recursive removal is instead modeled by walking the raw path while mutation is already in progress, deleting `b` too early can make `a/b/..` stop resolving. That would incorrectly prevent the command from removing everything in `a`.

This is the main modeling payoff of the extension: normalization should happen at the level of path meaning, not be left implicit inside destructive command execution.


## Design Check 1
> Great choice of topic! Filesystem semantics are a classic source of subtle bugs, and Forge is well-suited for exploring them. What specific surprising behaviors or edge cases are you hoping to surface? Having a concrete example or two in mind early will help focus your modeling.

Our main motivating edge case is `rmr a/b/..`. After normalization, this path should behave like `rmr a/.`, so both commands should delete the same directory. If recursive removal is instead modeled by walking the raw path while mutation is already in progress, deleting `b` too early can make `a/b/..` stop resolving. That would incorrectly prevent the command from removing everything in `a`.

The model is intended to surface exactly this kind of semantic mismatch: normalization should determine the meaning of the path before destructive effects begin.

> The three-bucket breakdown is very clear and well-scoped. One thing to think about is how you will represent "liveness" of files/directories as a boolean field, or via some other mechanism. Make sure you have a clear answer to this before design check 1, since it affects everything else.

We plan to represent liveness with an explicit set of live filesystem objects:

```forge
one sig FS {
  var live: set FsObj,
  ...
}
```

This makes transitions straightforward to express. For example, removal can update liveness by subtracting the removed object:

```forge
pred rm[x: FsObj] {
  ...,
  live' = live - x,
  ...
}
```

## Collaborators
- Alexander Lee
- Evangelos Lamprou
- Zekai Li
