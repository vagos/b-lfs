#lang forge/temporal

open "file-system.frg"

// Stores reference post-states for path-sequence equivalence checks.
one sig PathSeqSpec {
    var seqLiveAfter: set FsObj,
    var seqParentAfter: pfunc FsObj -> Dir,
    var seqEntryNameAfter: pfunc FsObj -> Name
}

// Records the current filesystem as a reference state.
pred recordCurrentFsSpec {
    PathSeqSpec.seqLiveAfter' = FS.live
    PathSeqSpec.seqParentAfter' = FS.parent
    PathSeqSpec.seqEntryNameAfter' = FS.entryName
}

// Records the rm-path post-state from the current filesystem.
pred recordRmPathSpec[base: Dir, p: Path] {
    some f: File | {
        resolvesTo[base, p, f]
        PathSeqSpec.seqLiveAfter' = FS.live - f
        PathSeqSpec.seqParentAfter' = FS.parent - f -> Dir
        PathSeqSpec.seqEntryNameAfter' = FS.entryName - f -> Name
    }
}

// Records the rmr-path post-state from the current filesystem.
pred recordRmrPathSpec[base: Dir, p: Path] {
    some d: Dir | {
        resolvesToDir[base, p, d]
        PathSeqSpec.seqLiveAfter' = FS.live - subtree[d]
        PathSeqSpec.seqParentAfter' = FS.parent - subtree[d] -> Dir
        PathSeqSpec.seqEntryNameAfter' = FS.entryName - subtree[d] -> Name
    }
}

// Carries a recorded path-sequence reference state across later steps.
pred keepPathSeqSpec {
    PathSeqSpec.seqLiveAfter' = PathSeqSpec.seqLiveAfter
    PathSeqSpec.seqParentAfter' = PathSeqSpec.seqParentAfter
    PathSeqSpec.seqEntryNameAfter' = PathSeqSpec.seqEntryNameAfter
}

// True when the current filesystem matches the recorded path-sequence reference state.
pred matchesPathSeqSpec {
    FS.live = PathSeqSpec.seqLiveAfter
    FS.parent = PathSeqSpec.seqParentAfter
    FS.entryName = PathSeqSpec.seqEntryNameAfter
}

// Reach goal: touching a fresh path and then removing it is a no-op.
pred touchThenRmPathIsNoOp {
    trace
    some n: Name, c: NameComp, parentPath, targetPath: Path, f: File | {
        c.label = n
        emptyPath[parentPath]
        pathIs1[targetPath, c]

        touchPath[Root, parentPath, n, f]
        recordCurrentFsSpec
        next_state {
            rmPath[Root, targetPath]
            keepPathSeqSpec
            next_state {
                matchesPathSeqSpec
            }
        }
    }
}

// Reach goal: mv src dst; rm dst matches direct rm src.
pred moveThenRemoveMatchesDirectRemove {
    trace
    some srcName, destName: Name, srcComp, destComp: NameComp,
         srcPath, destPath, destParentPath: Path, f: File | {
        srcName != destName
        srcComp.label = srcName
        destComp.label = destName
        pathIs1[srcPath, srcComp]
        pathIs1[destPath, destComp]
        emptyPath[destParentPath]

        touch[f, Root, srcName]
        next_state {
            mvPath[Root, srcPath, destParentPath, destName]
            recordRmPathSpec[Root, srcPath]
            next_state {
                rmPath[Root, destPath]
                keepPathSeqSpec
                next_state {
                    matchesPathSeqSpec
                }
            }
        }
    }
}

// Reach goal: rm -r a/b/.. is equivalent to rm -r a.
pred dotdotRmrMatchesParentRmr {
    trace
    some aName, bName: Name, aComp, bComp: NameComp, raw, parent: Path, dA, dB: Dir | {
        raw != parent
        aComp.label = aName
        bComp.label = bName
        pathIs3[raw, aComp, bComp, DotDot]
        pathIs1[parent, aComp]

        mkdir[dA, Root, aName]
        next_state {
            mkdir[dB, dA, bName]
            next_state {
                rmrPath[Root, raw]
                recordRmrPathSpec[Root, parent]
                next_state {
                    matchesPathSeqSpec
                }
            }
        }
    }
}

// Reach goal: rm -r a/b/.. is not equivalent to rm -r a/b.
pred dotdotRmrDiffersFromChildRmr {
    trace
    some aName, bName: Name, aComp, bComp: NameComp, raw, child: Path, dA, dB: Dir | {
        raw != child
        aComp.label = aName
        bComp.label = bName
        pathIs3[raw, aComp, bComp, DotDot]
        pathIs2[child, aComp, bComp]

        mkdir[dA, Root, aName]
        next_state {
            mkdir[dB, dA, bName]
            next_state {
                rmrPath[Root, raw]
                recordRmrPathSpec[Root, child]
                next_state {
                    not matchesPathSeqSpec
                    dA not in FS.live
                    dB not in FS.live
                }
            }
        }
    }
}
