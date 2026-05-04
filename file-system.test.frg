#lang forge/temporal

open "file-system.frg"

-- Foundation-level tests.
test expect foundationTests {
    initSat: {
        init
        stateOK
    } for 4 FsObj, 3 Dir, 1 File, 2 Name, 4 Component, 2 Path, 6 PathEval is sat

    traceSat: {
        trace
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 3 Path, 6 PathEval is sat

    traceCanCreateFile: {
        traceEventuallyCreatesFile
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 3 Path, 6 PathEval is sat

    rootAlwaysLiveCheck: {
        rootAlwaysLive
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 3 Path, 6 PathEval is checked

    traceWellformedCheck: {
        traceAlwaysWellformed
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 3 Path, 6 PathEval is checked
}

-- Named-child and .. resolution checks.
test expect namingTests {
    duplicateSiblingNameUnsat: {
        trace
        some n: Name, d1, d2: Dir | {
            mkdir[d1, Root, n]
            next_state mkdir[d2, Root, n]
        }
    } for 5 FsObj, 4 Dir, 1 File, 2 Name, 5 Component, 3 Path, 6 PathEval is unsat

    dotdotRootSat: {
        dotdotAtRootStaysAtRoot
    } for 4 FsObj, 2 Dir, 2 File, 2 Name, 4 Component, 2 Path, 4 PathEval is sat

    dotdotParentSat: {
        dotdotReturnsParent
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 2 Path, 6 PathEval is sat

}

-- Normalization behavior checks.
test expect normalizationTests {
    dotdotNormalizationSat: {
        dotdotPathNormalizesToParentName
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 2 Path, 6 PathEval is sat

    normalizedDotDotRmrSat: {
        normalizedDotDotRmrDeletesParentDirectory
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 2 Path, 6 PathEval is sat

    normalizationPreservesResolutionCheck: {
        normalizationPreservesResolution
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 2 Path, 6 PathEval is checked
}

-- Full-run checks for raw recursive rmr.
test expect rawRecursiveRmrRunTests {
    linearRunCanMatchRmrSpec: {
        linearRawRecursiveRmrCanMatchRmrSpec
    } for 4 FsObj, 3 Dir, 1 File, 2 Name, 4 Component, 1 Path, 3 PathEval is sat

    unrestrictedRunCanViolateRmrSpec: {
        rawRecursiveRmrViolatesRmrSpec
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 2 Path, 6 PathEval is sat

    noDotRunCanViolateRmrSpec: {
        noDotRawRecursiveRmrViolatesRmrSpec
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 2 Path, 6 PathEval is sat
}

-- Reach-level equivalence and non-equivalence checks for path command sequences.
test expect pathSequenceEquivalenceTests {
    touchThenRmNoOpSat: {
        touchThenRmPathIsNoOp
    } for 3 FsObj, 2 Dir, 1 File, 2 Name, 3 Component, 2 Path, 4 PathEval is sat

    moveThenRemoveMatchesDirectRemoveSat: {
        moveThenRemoveMatchesDirectRemove
    } for 3 FsObj, 2 Dir, 1 File, 3 Name, 4 Component, 3 Path, 6 PathEval is sat

    dotdotRmrMatchesParentRmrSat: {
        dotdotRmrMatchesParentRmr
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 2 Path, 6 PathEval is sat

    dotdotRmrDiffersFromChildRmrSat: {
        dotdotRmrDiffersFromChildRmr
    } for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 2 Path, 6 PathEval is sat
}

-- Without .., raw recursive path-rmr should match rmr spec.
noDotDotRawRecursiveRmrMatchesSpecAssertion:
    assert noDotDotRawRecursiveRmrViolatesRmrSpec is unsat
    for 4 FsObj, 3 Dir, 1 File, 2 Name, 4 Component, 1 Path, 3 PathEval

-- For name-only paths, raw recursive path-rmr should match rmr spec.
linearRawRecursiveRmrMatchesSpecAssertion:
    assert linearRawRecursiveRmrViolatesRmrSpec is unsat
    for 4 FsObj, 3 Dir, 1 File, 2 Name, 4 Component, 1 Path, 3 PathEval

-- Expected witness: a raw-path recursive-rmr violating trace.
rawRecursiveRmrMatchesSpecAssertion:
    assert rawRecursiveRmrViolatesRmrSpec is sat
    for 5 FsObj, 3 Dir, 2 File, 3 Name, 5 Component, 2 Path, 6 PathEval