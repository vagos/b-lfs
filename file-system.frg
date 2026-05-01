#lang forge/temporal

option max_tracelength 6

abstract sig FsObj {}
sig File extends FsObj {}
sig Dir extends FsObj {}
one sig Root extends Dir {}

sig Name {}

abstract sig Component {}
sig NameComp extends Component {
    label: one Name
}
one sig Dot, DotDot extends Component {}

sig Path {
    segs: pfunc Int -> Component
}

sig PathEval {
    evalBase: one Dir,
    evalPath: one Path,
    var walk: pfunc Int -> FsObj,
    var resolved: lone FsObj
}

one sig FS {
    var live: set FsObj,
    var parent: pfunc FsObj -> Dir,
    var entryName: pfunc FsObj -> Name
}

-- Stores the reference rmr post-state for a raw recursive run.
one sig RmrSpec {
    var liveAfter: set FsObj,
    var parentAfter: pfunc FsObj -> Dir,
    var entryNameAfter: pfunc FsObj -> Name
}

pred isLive[obj: FsObj] {
    obj in FS.live
}

pred isDead[obj: FsObj] {
    obj not in FS.live
}

pred childNamed[d: Dir, n: Name, obj: FsObj] {
    obj in FS.live
    FS.parent[obj] = d
    FS.entryName[obj] = n
}

fun subtree[d: Dir]: set FsObj {
    d + {obj: FsObj | obj in FS.live and reachable[d, obj, FS.parent]}
}

pred noChildNamed[d: Dir, n: Name] {
    no obj: FsObj | childNamed[d, n, obj]
}

-- Static constraints for path syntax and evaluator allocation.
pred pathModelWellformed {
    -- Paths are finite sequences: nonnegative, contiguous indices.
    all p: Path, i: Int | {
        some p.segs[i] implies i >= 0
        (some p.segs[i] and i > 0) implies some p.segs[subtract[i, 1]]
    }

    -- PathEval is a derived cache. Scopes must leave enough PathEval atoms
    -- for one evaluator per possible base-directory/path pair.
    all d: Dir, p: Path | one e: PathEval | {
        e.evalBase = d
        e.evalPath = p
    }
}

-- State constraints for a rooted, named filesystem tree.
pred wellformed {
    -- Root exists and has no parent/name.
    Root in FS.live
    no FS.parent[Root]
    no FS.entryName[Root]

    -- Dead objects have no filesystem metadata.
    all obj: FsObj | obj not in FS.live implies {
        no FS.parent[obj]
        no FS.entryName[obj]
    }

    -- Every live non-root object has a live parent and a name.
    all obj: FS.live - Root | {
        one FS.parent[obj]
        one FS.entryName[obj]
        FS.parent[obj] in FS.live
    }

    -- The live parent relation is an acyclic tree rooted at Root.
    all obj: FS.live | not reachable[obj, obj, FS.parent]
    all obj: FS.live - Root | reachable[Root, obj, FS.parent]

    -- Sibling names are unique: same parent and same name means same object.
    all disj x, y: FS.live - Root | {
        FS.parent[x] = FS.parent[y]
        FS.entryName[x] = FS.entryName[y]
    } implies x = y
}

pred init {
    FS.live = Root
    no FS.parent
    no FS.entryName
}

pred unchangedResolution {
    -- Resolution is derived, so command predicates intentionally leave it
    -- unconstrained; trace-level invariants recompute it in each state.
    true
}

pred touch[f: File, d: Dir, n: Name] {
    isDead[f]
    isLive[d]
    noChildNamed[d, n]

    FS.live' = FS.live + f
    FS.parent' = FS.parent + f -> d
    FS.entryName' = FS.entryName + f -> n
    unchangedResolution
}

pred mkdir[d: Dir, p: Dir, n: Name] {
    isDead[d]
    isLive[p]
    noChildNamed[p, n]

    FS.live' = FS.live + d
    FS.parent' = FS.parent + d -> p
    FS.entryName' = FS.entryName + d -> n
    unchangedResolution
}

pred rm[f: File] {
    isLive[f]

    FS.live' = FS.live - f
    FS.parent' = FS.parent - f -> Dir
    FS.entryName' = FS.entryName - f -> Name
    unchangedResolution
}

-- Deletes exactly one live non-root object.
pred deleteOne[obj: FsObj] {
    isLive[obj]
    obj != Root

    FS.live' = FS.live - obj
    FS.parent' = FS.parent - obj -> Dir
    FS.entryName' = FS.entryName - obj -> Name
    unchangedResolution
}

-- True when a directory currently has at least one live child.
pred hasLiveChild[d: Dir] {
    some child: FS.live | FS.parent[child] = d
}

-- A recursive rmr step may delete only a file or an empty directory.
pred recursiveRmrLeaf[target: Dir, victim: FsObj] {
    victim in subtree[target] - target
    {
        victim in File
        or
        (some victimDir: Dir | {
            victim = victimDir
            not hasLiveChild[victimDir]
        })
    }
}

-- One nondeterministic recursive rmr step under target.
pred recursiveRmrStep[target: Dir] {
    isLive[target]
    target != Root

    hasLiveChild[target] implies {
        some victim: FsObj | {
            recursiveRmrLeaf[target, victim]
            deleteOne[victim]
        }
    }

    not hasLiveChild[target] implies {
        deleteOne[target]
    }
}

-- Reference semantics for recursive removal: delete the whole subtree at once.
pred rmr[d: Dir] {
    isLive[d]
    d != Root

    FS.live' = FS.live - subtree[d]
    FS.parent' = FS.parent - subtree[d] -> Dir
    FS.entryName' = FS.entryName - subtree[d] -> Name
    unchangedResolution
}

pred mv[obj: FsObj, newParent: Dir, newName: Name] {
    isLive[obj]
    isLive[newParent]
    obj != Root
    no sibling: FS.live - obj | {
        FS.parent[sibling] = newParent
        FS.entryName[sibling] = newName
    }
    obj in Dir implies {
        obj != newParent
        not reachable[obj, newParent, FS.parent]
    }

    FS.live' = FS.live
    FS.parent' = (FS.parent - obj -> Dir) + obj -> newParent
    FS.entryName' = (FS.entryName - obj -> Name) + obj -> newName
    unchangedResolution
}

pred cp[src: File, dest: File, d: Dir, n: Name] {
    isLive[src]
    isDead[dest]
    isLive[d]
    noChildNamed[d, n]

    FS.live' = FS.live + dest
    FS.parent' = FS.parent + dest -> d
    FS.entryName' = FS.entryName + dest -> n
    unchangedResolution
}

pred stutter {
    FS.live' = FS.live
    FS.parent' = FS.parent
    FS.entryName' = FS.entryName
    unchangedResolution
}

pred step {
    (some f: File, d: Dir, n: Name | touch[f, d, n])
    or
    (some d: Dir, p: Dir, n: Name | mkdir[d, p, n])
    or
    (some f: File | rm[f])
    or
    (some d: Dir | rmr[d])
    or
    (some obj: FsObj, d: Dir, n: Name | mv[obj, d, n])
    or
    (some src: File, dest: File, d: Dir, n: Name | cp[src, dest, d, n])
}

-- Resolves one path component from a live directory.
pred stepComponent[from: Dir, c: Component, to: FsObj] {
    from in FS.live
    to in FS.live

    (c = Dot and to = from)
    or
    (c = DotDot and {
        (from = Root and to = Root)
        or
        (from != Root and to = FS.parent[from])
    })
    or
    (some nc: NameComp | {
        c = nc
        childNamed[from, nc.label, to]
    })
}

-- Constrains the first cached path-resolution step.
pred firstStep[e: PathEval] {
    all target: FsObj | {
        stepComponent[e.evalBase, e.evalPath.segs[0], target] iff e.walk[0] = target
    }
}

-- Constrains later cached path-resolution steps.
pred nextStep[e: PathEval, i: Int] {
    let prevIdx = subtract[i, 1] | {
        {
            some prev: Dir | {
                e.walk[prevIdx] = prev
                some target: FsObj | stepComponent[prev, e.evalPath.segs[i], target]
            }
        }
        iff
        some e.walk[i]

        all target: FsObj | {
            some prev: Dir | {
                e.walk[prevIdx] = prev
                stepComponent[prev, e.evalPath.segs[i], target]
            }
        } implies e.walk[i] = target
    }
}

-- Defines resolution for one base/path evaluator in the current state.
pred resolutionFor[e: PathEval] {
    e.evalBase in FS.live implies {
        no e.evalPath.segs implies {
            e.resolved = e.evalBase
            no e.walk
        }

        some e.evalPath.segs implies {
            all i: Int | {
                no e.evalPath.segs[i] implies no e.walk[i]

                some e.evalPath.segs[i] implies {
                    i = 0 implies firstStep[e]
                    i > 0 implies nextStep[e, i]
                }

                (some e.evalPath.segs[i] and no e.evalPath.segs[add[i, 1]]) implies {
                    e.resolved = e.walk[i]
                }
            }
        }
    }

    e.evalBase not in FS.live implies {
        no e.resolved
        no e.walk
    }
}

-- Applies path-resolution semantics to every evaluator.
pred resolutionSemantics {
    all e: PathEval | resolutionFor[e]
}

pred stateOK {
    pathModelWellformed
    wellformed
    resolutionSemantics
}

pred trace {
    init
    stateOK
    always {
        stateOK
        step or stutter
    }
}

-- Convenience predicate for object-valued path resolution.
pred resolvesTo[base: Dir, p: Path, obj: FsObj] {
    some e: PathEval | {
        e.evalBase = base
        e.evalPath = p
        e.resolved = obj
    }
}

-- Convenience predicate for directory-valued path resolution.
pred resolvesToDir[base: Dir, p: Path, d: Dir] {
    resolvesTo[base, p, d]
}

-- True for ordinary name components.
pred nameComponent[c: Component] {
    some nc: NameComp | c = nc
}

-- A normalized path contains only name components.
pred normalizedPath[p: Path] {
    all i: Int | some p.segs[i] implies nameComponent[p.segs[i]]
}

-- Excludes explicit current-directory components.
pred noDot[p: Path] {
    all i: Int | some p.segs[i] implies p.segs[i] != Dot
}

-- Excludes explicit parent-directory components.
pred noDotDot[p: Path] {
    all i: Int | some p.segs[i] implies p.segs[i] != DotDot
}

-- Requires at least one parent-directory component.
pred containsDotDot[p: Path] {
    some i: Int | p.segs[i] = DotDot
}

-- Two paths have the same meaning when they resolve to the same object.
pred samePathMeaning[base: Dir, p1, p2: Path] {
    some obj: FsObj | {
        resolvesTo[base, p1, obj]
        resolvesTo[base, p2, obj]
    }
}

-- Relates a raw path to a name-only path with the same meaning.
pred normalizesTo[base: Dir, raw, norm: Path] {
    normalizedPath[norm]
    samePathMeaning[base, raw, norm]
}

-- Path-based touch resolves the parent path first.
pred touchPath[base: Dir, parentPath: Path, n: Name, f: File] {
    some d: Dir | {
        resolvesToDir[base, parentPath, d]
        touch[f, d, n]
    }
}

-- Path-based mkdir resolves the parent path first.
pred mkdirPath[base: Dir, parentPath: Path, n: Name, d: Dir] {
    some p: Dir | {
        resolvesToDir[base, parentPath, p]
        mkdir[d, p, n]
    }
}

-- Path-based rm resolves the target path first.
pred rmPath[base: Dir, p: Path] {
    some f: File | {
        resolvesTo[base, p, f]
        rm[f]
    }
}

-- Path-based rmr resolves once, then applies the reference rmr relation.
pred rmrPath[base: Dir, p: Path] {
    some d: Dir | {
        resolvesToDir[base, p, d]
        rmr[d]
    }
}

-- Correct normalized rmr resolves the normalized path.
pred rmrNormalizedPath[base: Dir, raw, norm: Path] {
    normalizesTo[base, raw, norm]
    rmrPath[base, norm]
}

-- Records the rmr reference post-state for target.
pred recordRmrSpec[target: Dir] {
    RmrSpec.liveAfter' = FS.live - subtree[target]
    RmrSpec.parentAfter' = FS.parent - subtree[target] -> Dir
    RmrSpec.entryNameAfter' = FS.entryName - subtree[target] -> Name
}

-- Carries the recorded rmr reference post-state across recursive steps.
pred keepRmrSpec {
    RmrSpec.liveAfter' = RmrSpec.liveAfter
    RmrSpec.parentAfter' = RmrSpec.parentAfter
    RmrSpec.entryNameAfter' = RmrSpec.entryNameAfter
}

-- True when the current filesystem equals the recorded rmr reference state.
pred matchesRmrSpec {
    FS.live = RmrSpec.liveAfter
    FS.parent = RmrSpec.parentAfter
    FS.entryName = RmrSpec.entryNameAfter
}

-- Starts raw recursive rmr and records the reference rmr result.
pred startRawRecursiveRmrPath[base: Dir, raw: Path] {
    some target: Dir | {
        resolvesToDir[base, raw, target]
        recursiveRmrStep[target]
        recordRmrSpec[target]
    }
}

-- Raw recursive rmr re-resolves the path at each recursive step.
pred rawRecursiveRmrPathStep[base: Dir, raw: Path] {
    some target: Dir | {
        resolvesToDir[base, raw, target]
        recursiveRmrStep[target]
    }
}

-- Continues raw recursive rmr while preserving the reference result.
pred continueRawRecursiveRmrPath[base: Dir, raw: Path] {
    rawRecursiveRmrPathStep[base, raw]
    keepRmrSpec
}

-- True when the raw path can still name a non-root directory to remove.
pred rawRecursiveRmrCanStep[base: Dir, raw: Path] {
    some target: Dir | {
        resolvesToDir[base, raw, target]
        target != Root
    }
}

-- Terminal mismatch: raw recursion cannot step and has not reached rmr spec.
pred rawRecursiveRmrStuckBeforeRmrSpec[base: Dir, raw: Path] {
    not matchesRmrSpec
    not rawRecursiveRmrCanStep[base, raw]
}

-- Full raw recursive run: start once, then repeat re-resolution until terminal.
pred rawRecursiveRmrRun[base: Dir, raw: Path] {
    startRawRecursiveRmrPath[base, raw]

    next_state always {
        matchesRmrSpec implies {
            stutter
            keepRmrSpec
        }

        rawRecursiveRmrStuckBeforeRmrSpec[base, raw] implies {
            stutter
            keepRmrSpec
        }

        (not matchesRmrSpec and rawRecursiveRmrCanStep[base, raw]) implies {
            continueRawRecursiveRmrPath[base, raw]
        }
    }
}

-- Path-based mv resolves source and destination parent paths first.
pred mvPath[base: Dir, srcPath: Path, destParentPath: Path, newName: Name] {
    some obj: FsObj, d: Dir | {
        resolvesTo[base, srcPath, obj]
        resolvesToDir[base, destParentPath, d]
        mv[obj, d, newName]
    }
}

-- Path-based cp resolves source and destination parent paths first.
pred cpPath[base: Dir, srcPath: Path, destParentPath: Path, newName: Name, dest: File] {
    some src: File, d: Dir | {
        resolvesTo[base, srcPath, src]
        resolvesToDir[base, destParentPath, d]
        cp[src, dest, d, newName]
    }
}

-- Helper for a one-component path.
pred pathIs1[p: Path, c0: Component] {
    p.segs = 0 -> c0
}

-- Helper for a two-component path.
pred pathIs2[p: Path, c0, c1: Component] {
    p.segs = (0 -> c0) + (1 -> c1)
}

-- Helper for a three-component path.
pred pathIs3[p: Path, c0, c1, c2: Component] {
    p.segs = (0 -> c0) + (1 -> c1) + (2 -> c2)
}

-- Helper for the empty path.
pred emptyPath[p: Path] {
    no p.segs
}

pred traceEventuallyCreatesFile {
    trace
    eventually { some f: File | isLive[f] }
}

pred traceAlwaysWellformed {
    trace implies always { wellformed }
}

pred rootAlwaysLive {
    trace implies always { Root in FS.live }
}

-- Checks that .. at root resolves back to root.
pred dotdotAtRootStaysAtRoot {
    trace
    some p: Path | {
        pathIs1[p, DotDot]
        resolvesTo[Root, p, Root]
    }
}

-- Checks that a/b/.. resolves to a.
pred dotdotReturnsParent {
    trace
    some aName, bName: Name, aComp, bComp: NameComp, p: Path, dA, dB: Dir | {
        aComp.label = aName
        bComp.label = bName
        pathIs3[p, aComp, bComp, DotDot]

        mkdir[dA, Root, aName]
        next_state {
            mkdir[dB, dA, bName]
            next_state {
                resolvesTo[Root, p, dA]
            }
        }
    }
}

-- Shows that a/b/.. and a have the same path meaning.
pred dotdotPathNormalizesToParentName {
    trace
    some aName, bName: Name, aComp, bComp: NameComp, raw, norm: Path, dA, dB: Dir | {
        raw != norm
        aComp.label = aName
        bComp.label = bName
        pathIs3[raw, aComp, bComp, DotDot]
        pathIs1[norm, aComp]

        mkdir[dA, Root, aName]
        next_state {
            mkdir[dB, dA, bName]
            next_state {
                normalizesTo[Root, raw, norm]
                resolvesTo[Root, raw, dA]
                resolvesTo[Root, norm, dA]
            }
        }
    }
}

-- Shows that normalized rmr deletes the intended parent subtree.
pred normalizedDotDotRmrDeletesParentDirectory {
    trace
    some aName, bName: Name, aComp, bComp: NameComp, raw, norm: Path, dA, dB: Dir | {
        raw != norm
        aComp.label = aName
        bComp.label = bName
        pathIs3[raw, aComp, bComp, DotDot]
        pathIs1[norm, aComp]

        mkdir[dA, Root, aName]
        next_state {
            mkdir[dB, dA, bName]
            next_state {
                rmrNormalizedPath[Root, raw, norm]
                next_state {
                    dA not in FS.live
                    dB not in FS.live
                }
            }
        }
    }
}

-- Property: normalization preserves object-level resolution.
pred normalizationPreservesResolution {
    trace implies always {
        all base: Dir, raw, norm: Path | {
            normalizesTo[base, raw, norm] implies samePathMeaning[base, raw, norm]
        }
    }
}

-- A full raw recursive rmr run can stop before reaching rmr spec.
pred rawRecursiveRmrViolatesRmrSpecForPath[p: Path] {
    rawRecursiveRmrRun[Root, p]
    eventually rawRecursiveRmrStuckBeforeRmrSpec[Root, p]
}

-- Discover any raw-path recursive-rmr violation of rmr spec.
pred rawRecursiveRmrViolatesRmrSpec {
    trace
    eventually {
        some p: Path | rawRecursiveRmrViolatesRmrSpecForPath[p]
    }
}

-- Discover an rmr-spec violation while disallowing explicit . components.
pred noDotRawRecursiveRmrViolatesRmrSpec {
    trace
    eventually {
        some p: Path | {
            noDot[p]
            rawRecursiveRmrViolatesRmrSpecForPath[p]
        }
    }
}

-- Discover an rmr-spec violation while disallowing explicit .. components.
pred noDotDotRawRecursiveRmrViolatesRmrSpec {
    trace
    eventually {
        some p: Path | {
            noDotDot[p]
            rawRecursiveRmrViolatesRmrSpecForPath[p]
        }
    }
}

-- Discover an rmr-spec violation for pure name-only paths.
pred linearRawRecursiveRmrViolatesRmrSpec {
    trace
    eventually {
        some p: Path | {
            noDot[p]
            noDotDot[p]
            rawRecursiveRmrViolatesRmrSpecForPath[p]
        }
    }
}

-- A plain path can complete the full recursive run and match rmr spec.
pred linearRawRecursiveRmrCanMatchRmrSpec {
    trace
    eventually {
        some p: Path | {
            noDot[p]
            noDotDot[p]
            rawRecursiveRmrRun[Root, p]
            eventually matchesRmrSpec
        }
    }
}

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
