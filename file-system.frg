#lang forge/froglet
option run_sterling "vis.js"

abstract sig FsObj {}
sig File extends FsObj {}
sig Dir  extends FsObj {}
one sig Unit {}

sig State {
    live: pfunc FsObj -> Unit,
    parent: pfunc FsObj -> Dir,
    root: one Dir,
    next: lone State
}


pred isLive[s: State, obj: FsObj] { some s.live[obj] }
pred isDead[s: State, obj: FsObj] { no s.live[obj] }

pred wellformed[s: State] {
    -- root is live
    isLive[s, s.root]

    -- root has no parent
    no s.parent[s.root]

    -- every live non-root object has a live parent
    all obj: FsObj | (isLive[s, obj] and obj != s.root) implies {
        some s.parent[obj]
        isLive[s, s.parent[obj]]
    }

    -- file system is a tree
    -- no cycles
    all obj: FsObj | isLive[s, obj] implies not reachable[obj, obj, s.parent]

    -- root is reachable from every live object
    all obj: FsObj | (isLive[s, obj] and obj != s.root) implies reachable[s.root, obj, s.parent]
}

pred init[s: State] {
    -- only root is live
    all obj: FsObj | isLive[s, obj] implies obj = s.root

    wellformed[s]
}

pred touch[pre: State, post: State, f: File, d: Dir] {
    -- preconditions
    isDead[pre, f]
    isLive[pre, d]

    -- only f becomes live
    all obj: FsObj | isLive[post, obj] iff (isLive[pre, obj] or obj = f)

    -- only f gets parent d
    post.parent[f] = d
    all obj: FsObj | (obj != f) implies post.parent[obj] = pre.parent[obj]

    -- root unchanged
    post.root = pre.root
}

pred mkdir[pre: State, post: State, d: Dir, p: Dir] {
    -- preconditions
    isDead[pre, d]
    isLive[pre, p]

    -- only d becomes live
    all obj: FsObj | isLive[post, obj] iff (isLive[pre, obj] or obj = d)

    -- only d gets parent p
    post.parent[d] = p
    all obj: FsObj | (obj != d) implies post.parent[obj] = pre.parent[obj]

    -- root unchanged
    post.root = pre.root
}

pred rm[pre: State, post: State, f: File] {
    -- preconditions
    isLive[pre, f]

    -- only f becomes dead
    all obj: FsObj | isLive[post, obj] iff (isLive[pre, obj] and obj != f)

    -- parent unchanged
    all obj: FsObj | post.parent[obj] = pre.parent[obj]

    -- root unchanged
    post.root = pre.root
}

pred rmr[pre: State, post: State, d: Dir] {
    -- preconditions
    isLive[pre, d]
    d != pre.root

    -- only d and all descendants die
    all obj: FsObj | isLive[post, obj] iff {
        isLive[pre, obj] and obj != d and not reachable[d, obj, pre.parent]
    }

    -- parent unchanged
    all obj: FsObj | post.parent[obj] = pre.parent[obj]

    -- root unchanged
    post.root = pre.root
}

pred mv[pre: State, post: State, obj: FsObj, newParent: Dir] {
    -- preconditions
    isLive[pre, obj]
    isLive[pre, newParent]
    obj != pre.root
    -- cannot move a directory into its own subtree
    obj != newParent
    not reachable[obj, newParent, pre.parent]

    -- every file and directory keeps its liveness
    all x: FsObj | isLive[post, x] iff isLive[pre, x]

    -- only obj gets new parent
    post.parent[obj] = newParent
    all x: FsObj | (x != obj) implies post.parent[x] = pre.parent[x]

    -- root unchanged
    post.root = pre.root
}

pred cp[pre: State, post: State, src: File, dest: File, d: Dir] {
    -- preconditions
    isLive[pre, src]
    isDead[pre, dest]
    isLive[pre, d]

    -- only dest becomes live
    all obj: FsObj | isLive[post, obj] iff (isLive[pre, obj] or obj = dest)

    -- only dest gets parent d
    post.parent[dest] = d
    all obj: FsObj | (obj != dest) implies post.parent[obj] = pre.parent[obj]

    -- root unchanged
    post.root = pre.root
}

pred step[pre: State, post: State] {
    (some f: File, d: Dir | touch[pre, post, f, d])
    or
    (some d: Dir, p: Dir | mkdir[pre, post, d, p])
    or
    (some f: File | rm[pre, post, f])
    or
    (some d: Dir | rmr[pre, post, d])
    or
    (some obj: FsObj, d: Dir | mv[pre, post, obj, d])
    or
    (some src: File, dest: File, d: Dir | cp[pre, post, src, dest, d])
}

-- trace should be linear
pred trace {
    some s0: State | {
        init[s0]
        no s: State | s.next = s0
        all s: State | some s.next implies step[s, s.next]
        all s: State | s = s0 or reachable[s, s0, next]
        no s: State | reachable[s, s, next]
    }
}

test expect fileSystemTests {
    initSat: { some s: State | init[s] } is sat
    traceSat: { trace } for exactly 5 State is sat
    traceWithFileSat: {
        trace
        some s: State | some f: File | isLive[s, f]
    } for exactly 5 State is sat

    wellformedWithFileSat: {
        some s: State | {
            wellformed[s]
            some f: File | isLive[s, f]
            some d: Dir  | isLive[s, d] and d != s.root
        }
    } is sat

    -- a wellformed file system has a live root
    noRootUnsat: {
        some s: State | wellformed[s] and isDead[s, s.root]
    } is unsat

    cycleUnsat: {
        some s: State, d1: Dir, d2: Dir, d3: Dir | {
            wellformed[s]
            isLive[s, d1] and isLive[s, d2] and isLive[s, d3]
            s.parent[d1] = d2
            s.parent[d2] = d3
            s.parent[d3] = d1
        }
    } is unsat
}

test expect transitionTests {
    touchSat: { some pre, post: State, f: File, d: Dir | wellformed[pre] and touch[pre, post, f, d] } is sat
    mkdirSat: { some pre, post: State, d: Dir, p: Dir | wellformed[pre] and mkdir[pre, post, d, p] } is sat
    rmSat: { some pre, post: State, f: File | wellformed[pre] and rm[pre, post, f] } is sat
    rmrSat: { some pre, post: State, d: Dir | wellformed[pre] and rmr[pre, post, d] } is sat
    mvSat: { some pre, post: State, obj: FsObj, d: Dir | wellformed[pre] and mv[pre, post, obj, d] } is sat
    cpSat: { some pre, post: State, s: File, d: File, p: Dir | wellformed[pre] and cp[pre, post, s, d, p] } is sat

    touchLiveUnsat: { some pre, post: State, f: File, d: Dir | wellformed[pre] and isLive[pre, f] and touch[pre, post, f, d] } is unsat
    mkdirLiveUnsat: { some pre, post: State, d: Dir, p: Dir | wellformed[pre] and isLive[pre, d] and mkdir[pre, post, d, p] } is unsat
    rmDeadUnsat: { some pre, post: State, f: File | wellformed[pre] and isDead[pre, f] and rm[pre, post, f] } is unsat
    rmrRootUnsat: { some pre, post: State | wellformed[pre] and rmr[pre, post, pre.root] } is unsat
    mvRootUnsat: { some pre, post: State, d: Dir | wellformed[pre] and mv[pre, post, pre.root, d] } is unsat
}


pred touchPreserves {
    all pre, post: State, f: File, d: Dir |
        (wellformed[pre] and touch[pre, post, f, d]) implies wellformed[post]
}

pred mkdirPreserves {
    all pre, post: State, d: Dir, p: Dir |
        (wellformed[pre] and mkdir[pre, post, d, p]) implies wellformed[post]
}

pred rmPreserves {
    all pre, post: State, f: File |
        (wellformed[pre] and rm[pre, post, f]) implies wellformed[post]
}

pred rmrPreserves {
    all pre, post: State, d: Dir |
        (wellformed[pre] and rmr[pre, post, d]) implies wellformed[post]
}

pred mvPreserves {
    all pre, post: State, obj: FsObj, d: Dir |
        (wellformed[pre] and mv[pre, post, obj, d]) implies wellformed[post]
}

pred cpPreserves {
    all pre, post: State, src: File, dest: File, d: Dir |
        (wellformed[pre] and cp[pre, post, src, dest, d]) implies wellformed[post]
}

-- only touch, mkdir, cp can create live objects
pred noOtherCreation {
    trace implies {
        all s: State | some s.next implies {
            all obj: FsObj | (isDead[s, obj] and isLive[s.next, obj]) implies {
                (some f: File, d: Dir | obj = f and touch[s, s.next, f, d])
                or
                (some d: Dir, p: Dir | obj = d and mkdir[s, s.next, d, p])
                or
                (some src: File, dest: File, d: Dir | obj = dest and cp[s, s.next, src, dest, d])
            }
        }
    }
}


-- only rm, rmr can kill live objects
pred noOtherDeath {
    trace implies {
        all s: State | some s.next implies {
            all obj: FsObj | (isLive[s, obj] and isDead[s.next, obj]) implies {
                (some f: File | obj = f and rm[s, s.next, f])
                or
                (some d: Dir | rmr[s, s.next, d] and (obj = d or reachable[d, obj, s.parent]))
            }
        }
    }
}

test expect propertyTests {
    touchPreservesCheck: { touchPreserves } is checked
    mkdirPreservesCheck: { mkdirPreserves } is checked
    rmPreservesCheck: { rmPreserves } is checked
    rmrPreservesCheck: { rmrPreserves } is checked
    mvPreservesCheck: { mvPreserves } is checked
    cpPreservesCheck: { cpPreserves } is checked

    noOtherCreationCheck:
        { noOtherCreation }
        for 6 State is checked

    noOtherDeathCheck:
        { noOtherDeath }
        for 6 State is checked
}

-- traces that should be impossible
test expect traceUnsat {
    -- cannot rmr the same directory twice
    rmrTwiceUnsat: {
        trace
        some s1, s2, s3: State, d: Dir | {
            s2 = s1.next
            s3 = s2.next
            rmr[s1, s2, d]
            rmr[s2, s3, d]
        }
    } for 6 State is unsat

    -- cannot mv a file after rm it
    rmThenMvUnsat: {
        trace
        some s1, s2, s3: State, f: File, d: Dir | {
            s2 = s1.next
            s3 = s2.next
            rm[s1, s2, f]
            mv[s2, s3, f, d]
        }
    } for 6 State is unsat

    -- cannot cp from a file after rm it
    rmThenCpUnsat: {
        trace
        some s1, s2, s3: State, f: File, dest: File, d: Dir | {
            s2 = s1.next
            s3 = s2.next
            rm[s1, s2, f]
            cp[s2, s3, f, dest, d]
        }
    } for 6 State is unsat

    -- cannot mv into a dead directory
    mvToDeadDirUnsat: {
        trace
        some s1, s2, s3: State, d1: Dir, d2: Dir | {
            s2 = s1.next
            s3 = s2.next
            rmr[s1, s2, d1]
            mv[s2, s3, d2, d1]
        }
    } for 6 State is unsat
}

test expect traceSat {
    -- touch a file then rm it
    touchThenRmSat: {
        trace
        some s1, s2, s3: State, f: File, d: Dir | {
            s2 = s1.next
            s3 = s2.next
            touch[s1, s2, f, d]
            rm[s2, s3, f]
        }
    } for 6 State is sat

    -- mkdir then touch a file inside it then mv the file
    mkdirTouchMvSat: {
        trace
        some s1, s2, s3, s4: State, d: Dir, p: Dir, f: File | {
            s2 = s1.next
            s3 = s2.next
            s4 = s3.next
            mkdir[s1, s2, d, p]
            touch[s2, s3, f, d]
            mv[s3, s4, f, p]
        }
    } for 6 State is sat

    -- mkdir then rmr
    mkdirThenRmrSat: {
        trace
        some s1, s2, s3, s4: State, d1: Dir, d2: Dir, p: Dir | {
            s2 = s1.next
            s3 = s2.next
            s4 = s3.next
            mkdir[s1, s2, d1, p]
            mkdir[s2, s3, d2, d1]
            rmr[s3, s4, d1]
        }
    } for 6 State is sat

    -- touch a file then cp it
    touchThenCpSat: {
        trace
        some s1, s2, s3: State, f: File, dest: File, d: Dir | {
            s2 = s1.next
            s3 = s2.next
            touch[s1, s2, f, d]
            cp[s2, s3, f, dest, d]
        }
    } for 6 State is sat
}

-- every state on the trace is well-formed
pred wellformedIsAnInvariant {
    all s: State | wellformed[s]
}

-- the root never changes across states
pred rootIsForever {
    all s1, s2: State | s1.root = s2.root
}

-- the root is always live
pred rootAlwaysLive {
    all s: State | isLive[s, s.root]
}

wellformedIsAnInvariantAssertion: assert trace is sufficient for wellformedIsAnInvariant

rootIsForeverAssertion: assert trace is sufficient for rootIsForever

rootAlwaysLiveAssertion: assert trace is sufficient for rootAlwaysLive