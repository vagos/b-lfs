#lang forge/temporal

open "../file-system.frg"

option max_tracelength 6

one sig GeneratedName0 extends Name {}

one sig GeneratedComp0 extends NameComp {}

one sig GeneratedPath0 extends Path {}
one sig GeneratedPath1 extends Path {}

pred generatedPaths {
    GeneratedComp0.label = GeneratedName0
    no GeneratedPath0.segs
    GeneratedPath1.segs = (0 -> GeneratedComp0)
}

pred generatedScript {
    trace
    generatedPaths
    some file0: File | touchPath[Root, GeneratedPath0, GeneratedName0, file0]
    next_state {
        rmPath[Root, GeneratedPath1]
        next_state {
            rmPath[Root, GeneratedPath1]
        }
    }
}

run {
    generatedScript
} for 2 FsObj, 1 Dir, 1 File, 1 Name, 3 Component, 2 Path, 2 PathEval
