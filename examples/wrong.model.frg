#lang forge/temporal

open "../file-system.frg"

one sig GeneratedName0 extends Name {}

one sig GeneratedComp0 extends NameComp {}

one sig GeneratedPath0 extends Path {}

pred generatedPaths {
    GeneratedComp0.label = GeneratedName0
    GeneratedPath0.segs = (0 -> GeneratedComp0)
}

pred generatedScript {
    trace
    generatedPaths
    rmPath[Root, GeneratedPath0]
    next_state {
        rmPath[Root, GeneratedPath0]
    }
}

test expect generatedScriptTests {
    generatedScriptSat: {
        generatedScript
    } for 2 FsObj, 1 Dir, 1 File, 1 Name, 3 Component, 1 Path, 1 PathEval is sat
}
