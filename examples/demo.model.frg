#lang forge/temporal

open "../file-system.frg"

option max_tracelength 8

-- Generated from /Users/vagozino/wrk/csci1710/project/examples/demo.sh by scripts/shell_to_forge.py

one sig GeneratedName0 extends Name {}
one sig GeneratedName1 extends Name {}
one sig GeneratedName2 extends Name {}
one sig GeneratedName3 extends Name {}

one sig GeneratedComp0 extends NameComp {}
one sig GeneratedComp1 extends NameComp {}
one sig GeneratedComp2 extends NameComp {}

one sig GeneratedPath0 extends Path {}
one sig GeneratedPath1 extends Path {}
one sig GeneratedPath2 extends Path {}
one sig GeneratedPath3 extends Path {}
one sig GeneratedPath4 extends Path {}

pred generatedPaths {
    GeneratedComp0.label = GeneratedName0
    GeneratedComp1.label = GeneratedName1
    GeneratedComp2.label = GeneratedName2
    no GeneratedPath0.segs
    GeneratedPath1.segs = (0 -> GeneratedComp0)
    GeneratedPath2.segs = (0 -> GeneratedComp0) + (1 -> GeneratedComp1)
    GeneratedPath3.segs = (0 -> GeneratedComp0) + (1 -> GeneratedComp1) + (2 -> GeneratedComp2)
    GeneratedPath4.segs = (0 -> GeneratedComp0) + (1 -> GeneratedComp1) + (2 -> DotDot)
}

pred generatedScript {
    trace
    generatedPaths
    some dir0: Dir | mkdirPath[Root, GeneratedPath0, GeneratedName0, dir0]
    next_state {
        some dir1: Dir | mkdirPath[Root, GeneratedPath1, GeneratedName1, dir1]
        next_state {
            some file2: File | touchPath[Root, GeneratedPath2, GeneratedName2, file2]
            next_state {
                some file3: File | touchPath[Root, GeneratedPath0, GeneratedName3, file3]
                next_state {
                    rmPath[Root, GeneratedPath3]
                    next_state {
                        rmrPath[Root, GeneratedPath4]
                    }
                }
            }
        }
    }
}

run {
    generatedScript
} for 5 FsObj, 3 Dir, 2 File, 4 Name, 5 Component, 5 Path, 15 PathEval
