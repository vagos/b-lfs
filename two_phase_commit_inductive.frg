#lang forge

/*
 * Two-Phase Commit Protocol — Transition System (Non-Temporal)
 *
 * Models 2PC as an explicit state-based delta system.
 * Proves safety invariants via INDUCTION:
 *   - Base case:      init[s] => inv[s]
 *   - Inductive step: inv[s] and delta[s, s'] => inv[s']
 *
 * No temporal operators (#lang forge, not forge/temporal).
 */

-- ============================================================
-- State enumerations
-- ============================================================

abstract sig CoordState {}
one sig CWaiting, CCommit, CAbort extends CoordState {}

abstract sig ParticipantState {}
one sig PWorking, PReady, PCommitted, PAborted extends ParticipantState {}

abstract sig Vote {}
one sig VoteYes, VoteNo extends Vote {}

-- ============================================================
-- Processes (fixed, not part of state)
-- ============================================================

sig Participant {}

-- ============================================================
-- State: a snapshot of the entire system at one point in time
-- ============================================================

sig State {
    cstate:  one CoordState,                     -- coordinator state
    pstate:  pfunc Participant -> ParticipantState,  -- per-participant state
    pvote:   pfunc Participant -> Vote               -- per-participant vote
}

-- ============================================================
-- Wellformedness: every participant has a state in every State
-- ============================================================

pred wellformed[s: State] {
    all p: Participant | one s.pstate[p]
}

-- ============================================================
-- Initial state
-- ============================================================

pred init[s: State] {
    s.cstate = CWaiting
    all p: Participant | {
        s.pstate[p] = PWorking
        no s.pvote[p]
    }
}

-- ============================================================
-- Transitions
-- ============================================================

-- A participant votes
pred participantVotes[pre: State, post: State, p: Participant, v: Vote] {
    -- GUARD
    pre.pstate[p] = PWorking
    pre.cstate = CWaiting

    -- EFFECT
    post.pstate[p] = PReady
    post.pvote[p] = v

    -- FRAME: coordinator
    post.cstate = pre.cstate

    -- FRAME: other participants
    all other: Participant | other != p implies {
        post.pstate[other] = pre.pstate[other]
        post.pvote[other] = pre.pvote[other]
    }
}

-- Coordinator decides to commit (all voted yes)
pred coordinatorCommit[pre: State, post: State] {
    -- GUARD
    pre.cstate = CWaiting
    all p: Participant | pre.pstate[p] = PReady and pre.pvote[p] = VoteYes

    -- EFFECT
    post.cstate = CCommit

    -- FRAME
    all p: Participant | {
        post.pstate[p] = pre.pstate[p]
        post.pvote[p] = pre.pvote[p]
    }
}

-- Coordinator decides to abort (some voted no)
pred coordinatorAbort[pre: State, post: State] {
    -- GUARD
    pre.cstate = CWaiting
    some p: Participant | pre.pstate[p] = PReady and pre.pvote[p] = VoteNo

    -- EFFECT
    post.cstate = CAbort

    -- FRAME
    all p: Participant | {
        post.pstate[p] = pre.pstate[p]
        post.pvote[p] = pre.pvote[p]
    }
}

-- Participant commits (follows coordinator's commit decision)
pred participantCommits[pre: State, post: State, p: Participant] {
    -- GUARD
    pre.pstate[p] = PReady
    pre.cstate = CCommit

    -- EFFECT
    post.pstate[p] = PCommitted

    -- FRAME
    post.pvote[p] = pre.pvote[p]
    post.cstate = pre.cstate
    all other: Participant | other != p implies {
        post.pstate[other] = pre.pstate[other]
        post.pvote[other] = pre.pvote[other]
    }
}

-- Participant aborts (follows coordinator's abort decision)
pred participantAborts[pre: State, post: State, p: Participant] {
    -- GUARD
    pre.pstate[p] = PReady
    pre.cstate = CAbort

    -- EFFECT
    post.pstate[p] = PAborted

    -- FRAME
    post.pvote[p] = pre.pvote[p]
    post.cstate = pre.cstate
    all other: Participant | other != p implies {
        post.pstate[other] = pre.pstate[other]
        post.pvote[other] = pre.pvote[other]
    }
}

-- Participant spontaneously aborts
pred participantSpontaneousAbort[pre: State, post: State, p: Participant] {
    -- GUARD
    pre.pstate[p] = PWorking

    -- EFFECT
    post.pstate[p] = PAborted
    post.pvote[p] = VoteNo

    -- FRAME
    post.cstate = pre.cstate
    all other: Participant | other != p implies {
        post.pstate[other] = pre.pstate[other]
        post.pvote[other] = pre.pvote[other]
    }
}

-- Stutter (no change)
pred stutter[pre: State, post: State] {
    post.cstate = pre.cstate
    all p: Participant | {
        post.pstate[p] = pre.pstate[p]
        post.pvote[p] = pre.pvote[p]
    }
}

-- ============================================================
-- Overall delta relation
-- ============================================================

pred delta[pre: State, post: State] {
    (some p: Participant, v: Vote | participantVotes[pre, post, p, v])
    or coordinatorCommit[pre, post]
    or coordinatorAbort[pre, post]
    or (some p: Participant | participantCommits[pre, post, p])
    or (some p: Participant | participantAborts[pre, post, p])
    or (some p: Participant | participantSpontaneousAbort[pre, post, p])
    or stutter[pre, post]
}

-- ============================================================
-- INVARIANTS
-- ============================================================

-- Inv1: Agreement — no participant committed while another aborted
pred agreement[s: State] {
    all disj p1, p2: Participant |
        not (s.pstate[p1] = PCommitted and s.pstate[p2] = PAborted)
}

-- Inv2: Commit validity — committed participants imply coordinator committed
pred commitValidity[s: State] {
    (some p: Participant | s.pstate[p] = PCommitted)
        implies s.cstate = CCommit
}

-- Inv3: Abort validity — if a participant aborted, coordinator did NOT commit
pred abortValidity[s: State] {
    (some p: Participant | s.pstate[p] = PAborted)
        implies s.cstate != CCommit
}

-- Inv4: Commit means all voted yes
pred commitMeansAllYes[s: State] {
    s.cstate = CCommit implies {
        all p: Participant | s.pvote[p] = VoteYes
    }
}

-- Inv5 (STRENGTHENING): If coordinator committed, no participant is still PWorking.
-- (Abort can happen while some are still PWorking, but commit requires all PReady first.)
pred commitMeansAllVoted[s: State] {
    s.cstate = CCommit implies {
        all p: Participant | s.pstate[p] != PWorking
    }
}

-- Inv6 (STRENGTHENING): If coordinator committed, no participant is PAborted.
pred commitMeansNoAbort[s: State] {
    s.cstate = CCommit implies {
        all p: Participant | s.pstate[p] = PReady or s.pstate[p] = PCommitted
    }
}

-- Inv7 (STRENGTHENING): If coordinator aborted, no participant is PCommitted.
pred abortMeansNoCommit[s: State] {
    s.cstate = CAbort implies {
        all p: Participant | s.pstate[p] != PCommitted
    }
}

-- Inv8 (STRENGTHENING): PReady participants have a vote recorded
pred readyMeansVoted[s: State] {
    all p: Participant | {
        s.pstate[p] = PReady implies some s.pvote[p]
        s.pstate[p] = PCommitted implies some s.pvote[p]
    }
}

-- ============================================================
-- Strengthened inductive invariant (conjunction of all invariants)
-- A single invariant may not be inductive on its own, so we
-- combine them into a strengthened invariant.
-- ============================================================

pred safetyInvariant[s: State] {
    wellformed[s]
    agreement[s]
    commitValidity[s]
    abortValidity[s]
    commitMeansAllYes[s]
    commitMeansAllVoted[s]
    commitMeansNoAbort[s]
    abortMeansNoCommit[s]
    readyMeansVoted[s]
}


-- ============================================================
-- INDUCTIVE PROOFS
-- ============================================================

/*
 * To prove an invariant Inv holds for ALL reachable states:
 *
 *   BASE CASE:      init[s] => Inv[s]
 *   INDUCTIVE STEP: Inv[s] ∧ delta[s, s'] => Inv[s']
 *
 * We use `assert ... is necessary for` for each.
 */

-- Helper predicates for assertions
pred initPred[s: State] {
    init[s]
}

pred inductiveStepPre[pre: State, post: State] {
    safetyInvariant[pre]
    delta[pre, post]
}

-- ============================================================
-- BASE CASE: init => safetyInvariant
-- ============================================================

baseCaseCheck:
    assert all s: State |
        safetyInvariant[s] is necessary for initPred[s]
    for exactly 1 State, exactly 3 Participant

-- ============================================================
-- INDUCTIVE STEP: safetyInvariant[pre] ∧ delta[pre, post]
--                  => safetyInvariant[post]
-- ============================================================

inductiveStepCheck:
    assert all pre, post: State |
        safetyInvariant[post] is necessary for inductiveStepPre[pre, post]
    for exactly 2 State, exactly 3 Participant

-- ============================================================
-- INDIVIDUAL INVARIANT INDUCTIVE CHECKS
-- (Useful to pinpoint which invariant breaks if one fails)
-- ============================================================

inductiveAgreement:
    assert all pre, post: State |
        agreement[post] is necessary for inductiveStepPre[pre, post]
    for exactly 2 State, exactly 3 Participant

inductiveCommitValidity:
    assert all pre, post: State |
        commitValidity[post] is necessary for inductiveStepPre[pre, post]
    for exactly 2 State, exactly 3 Participant

inductiveAbortValidity:
    assert all pre, post: State |
        abortValidity[post] is necessary for inductiveStepPre[pre, post]
    for exactly 2 State, exactly 3 Participant

inductiveCommitYes:
    assert all pre, post: State |
        commitMeansAllYes[post] is necessary for inductiveStepPre[pre, post]
    for exactly 2 State, exactly 3 Participant

inductiveWF:
    assert all pre, post: State |
        wellformed[post] is necessary for inductiveStepPre[pre, post]
    for exactly 2 State, exactly 3 Participant

-- ============================================================
-- SATISFIABILITY: make sure the model isn't vacuously true
-- ============================================================

test expect {
    -- init states exist
    initSat: {
        some s: State | init[s]
    } for exactly 1 State, exactly 3 Participant is sat

    -- transitions from init are possible
    canStep: {
        some pre, post: State | {
            init[pre]
            delta[pre, post]
            pre != post
        }
    } for exactly 2 State, exactly 3 Participant is sat

    -- can reach commit
    canReachCommit: {
        some pre, post: State | {
            safetyInvariant[pre]
            delta[pre, post]
            post.cstate = CCommit
        }
    } for exactly 2 State, exactly 3 Participant is sat

    -- can reach abort
    canReachAbort: {
        some pre, post: State | {
            safetyInvariant[pre]
            delta[pre, post]
            post.cstate = CAbort
        }
    } for exactly 2 State, exactly 3 Participant is sat

    -- invariant is not trivially unsatisfiable
    invSat: {
        some s: State | safetyInvariant[s] and s.cstate = CCommit
    } for exactly 1 State, exactly 3 Participant is sat

    -- invariant with abort is satisfiable
    invAbortSat: {
        some s: State | safetyInvariant[s] and s.cstate = CAbort
    } for exactly 1 State, exactly 3 Participant is sat
}

-- ============================================================
-- RUN: visualize an example transition
-- ============================================================

exampleCommitStep: run {
    some pre, post: State | {
        safetyInvariant[pre]
        coordinatorCommit[pre, post]
        safetyInvariant[post]
    }
} for exactly 2 State, exactly 3 Participant

exampleAbortStep: run {
    some pre, post: State | {
        safetyInvariant[pre]
        coordinatorAbort[pre, post]
        safetyInvariant[post]
    }
} for exactly 2 State, exactly 3 Participant
