#lang forge/temporal

/*
 * Two-Phase Commit Protocol
 *
 * Models the classic distributed consensus protocol where a Coordinator
 * orchestrates a set of Participants to atomically commit or abort a
 * distributed transaction.
 *
 * Phase 1 (Voting):   Coordinator asks participants to vote.
 *                     Each participant votes Yes or No.
 * Phase 2 (Decision): If ALL voted Yes → Commit; otherwise → Abort.
 *                     Participants follow the coordinator's decision.
 */

-- ============================================================
-- State enumerations
-- ============================================================

-- Coordinator states
abstract sig CoordState {}
one sig CWaiting, CCommit, CAbort extends CoordState {}

-- Participant states
abstract sig ParticipantState {}
one sig PWorking, PReady, PCommitted, PAborted extends ParticipantState {}

-- Votes
abstract sig Vote {}
one sig VoteYes, VoteNo extends Vote {}

-- ============================================================
-- Process sigs
-- ============================================================

one sig Coordinator {
    var cstate: one CoordState
}

sig Participant {
    var pstate: one ParticipantState,
    var pvote:  lone Vote
}

-- ============================================================
-- Initial state
-- ============================================================

pred init {
    Coordinator.cstate = CWaiting
    all p: Participant | {
        p.pstate = PWorking
        no p.pvote
    }
}

-- ============================================================
-- Transition: a participant casts its vote
-- ============================================================

pred participantVotes[p: Participant, v: Vote] {
    -- GUARD
    p.pstate = PWorking
    Coordinator.cstate = CWaiting

    -- EFFECT on this participant
    p.pstate' = PReady
    p.pvote'  = v

    -- FRAME: coordinator unchanged
    Coordinator.cstate' = Coordinator.cstate

    -- FRAME: other participants unchanged
    all other: Participant | other != p implies {
        other.pstate' = other.pstate
        other.pvote'  = other.pvote
    }
}

-- ============================================================
-- Transition: coordinator collects votes and decides COMMIT
-- ============================================================

pred coordinatorCommit {
    -- GUARD: coordinator is still waiting
    Coordinator.cstate = CWaiting
    -- GUARD: all participants have voted Yes
    all p: Participant | p.pstate = PReady and p.pvote = VoteYes

    -- EFFECT
    Coordinator.cstate' = CCommit

    -- FRAME: participants unchanged
    all p: Participant | {
        p.pstate' = p.pstate
        p.pvote'  = p.pvote
    }
}

-- ============================================================
-- Transition: coordinator collects votes and decides ABORT
-- ============================================================

pred coordinatorAbort {
    -- GUARD: coordinator is still waiting
    Coordinator.cstate = CWaiting
    -- GUARD: at least one participant voted No (or some still working,
    --        but all ready ones include at least one No)
    some p: Participant | p.pstate = PReady and p.pvote = VoteNo

    -- EFFECT
    Coordinator.cstate' = CAbort

    -- FRAME: participants unchanged
    all p: Participant | {
        p.pstate' = p.pstate
        p.pvote'  = p.pvote
    }
}

-- ============================================================
-- Transition: participant learns coordinator committed
-- ============================================================

pred participantCommits[p: Participant] {
    -- GUARD
    p.pstate = PReady
    Coordinator.cstate = CCommit

    -- EFFECT
    p.pstate' = PCommitted

    -- FRAME
    p.pvote' = p.pvote
    Coordinator.cstate' = Coordinator.cstate
    all other: Participant | other != p implies {
        other.pstate' = other.pstate
        other.pvote'  = other.pvote
    }
}

-- ============================================================
-- Transition: participant learns coordinator aborted
-- ============================================================

pred participantAborts[p: Participant] {
    -- GUARD
    p.pstate = PReady
    Coordinator.cstate = CAbort

    -- EFFECT
    p.pstate' = PAborted

    -- FRAME
    p.pvote' = p.pvote
    Coordinator.cstate' = Coordinator.cstate
    all other: Participant | other != p implies {
        other.pstate' = other.pstate
        other.pvote'  = other.pvote
    }
}

-- ============================================================
-- Transition: participant spontaneously aborts (votes No itself)
-- A participant still in PWorking can unilaterally abort
-- ============================================================

pred participantSpontaneousAbort[p: Participant] {
    -- GUARD
    p.pstate = PWorking

    -- EFFECT: participant goes directly to Aborted with a No vote
    p.pstate' = PAborted
    p.pvote'  = VoteNo

    -- FRAME
    Coordinator.cstate' = Coordinator.cstate
    all other: Participant | other != p implies {
        other.pstate' = other.pstate
        other.pvote'  = other.pvote
    }
}

-- ============================================================
-- Stutter (nothing changes — needed for lasso traces)
-- ============================================================

pred stutter {
    Coordinator.cstate' = Coordinator.cstate
    all p: Participant | {
        p.pstate' = p.pstate
        p.pvote'  = p.pvote
    }
}

-- ============================================================
-- Overall transition relation
-- ============================================================

pred step {
    (some p: Participant, v: Vote | participantVotes[p, v])
    or coordinatorCommit
    or coordinatorAbort
    or (some p: Participant | participantCommits[p])
    or (some p: Participant | participantAborts[p])
    or (some p: Participant | participantSpontaneousAbort[p])
    or stutter
}

-- ============================================================
-- Trace predicate: ties it all together
-- ============================================================

pred traces {
    init
    always step
}

-- ============================================================
-- SAFETY PROPERTIES
-- ============================================================

-- Agreement: no participant commits while another aborts
pred agreement {
    always {
        all disj p1, p2: Participant |
            not (p1.pstate = PCommitted and p2.pstate = PAborted)
    }
}

-- Commit validity: if any participant committed, coordinator decided commit
pred commitValidity {
    always {
        (some p: Participant | p.pstate = PCommitted)
            implies Coordinator.cstate = CCommit
    }
}

-- Abort validity: if any participant committed, all must have voted Yes
pred abortValidity {
    always {
        (some p: Participant | p.pstate = PCommitted)
            implies (all p: Participant | p.pvote = VoteYes or p.pstate = PWorking)
    }
}

-- No commit after abort decision: coordinator never changes its decision
pred decisionStable {
    always {
        Coordinator.cstate = CCommit implies
            always Coordinator.cstate = CCommit
        Coordinator.cstate = CAbort implies
            always Coordinator.cstate = CAbort
    }
}

-- ============================================================
-- VERIFICATION: assert safety properties
-- ============================================================

-- Each safety property is necessary for any valid trace.
-- Forge searches for counterexamples; if none found, the assertion holds.

agreementHolds:
    assert agreement is necessary for traces
    for exactly 3 Participant

commitValidityHolds:
    assert commitValidity is necessary for traces
    for exactly 3 Participant

abortValidityHolds:
    assert abortValidity is necessary for traces
    for exactly 3 Participant

decisionStableHolds:
    assert decisionStable is necessary for traces
    for exactly 3 Participant

-- Verify that properties are non-vacuous (the protocol can actually run)
agreementNonVacuous:
    assert agreement is consistent with traces
    for exactly 3 Participant

-- ============================================================
-- LIVENESS & SATISFIABILITY TESTS
-- ============================================================

test expect {
    -- The model is satisfiable (can produce traces)
    traceSat: { traces } is sat

    -- It's possible for the protocol to commit
    canCommit: {
        traces
        eventually Coordinator.cstate = CCommit
    } is sat

    -- It's possible for the protocol to abort
    canAbort: {
        traces
        eventually Coordinator.cstate = CAbort
    } is sat

    -- It's possible for all participants to reach committed state
    allCommitted: {
        traces
        eventually { all p: Participant | p.pstate = PCommitted }
    } is sat

    -- It's possible for all participants to reach aborted state
    allAborted: {
        traces
        eventually { all p: Participant | p.pstate = PAborted }
    } is sat

    -- If all participants vote yes, eventually commit is possible
    unanimousYesMeansCommit: {
        traces
        eventually { all p: Participant | p.pvote = VoteYes }
        eventually Coordinator.cstate = CCommit
    } is sat

    -- Agreement cannot be violated (same as check above, but as test expect)
    agreementNeverViolated: {
        traces
        eventually { some disj p1, p2: Participant |
            p1.pstate = PCommitted and p2.pstate = PAborted }
    } is unsat
}

-- ============================================================
-- RUN: generate an example trace that ends in commit
-- ============================================================

commitTrace: run {
    traces
    eventually Coordinator.cstate = CCommit
    eventually { all p: Participant | p.pstate = PCommitted }
} for exactly 3 Participant

-- Generate an example trace that ends in abort
abortTrace: run {
    traces
    eventually Coordinator.cstate = CAbort
    eventually { all p: Participant | p.pstate = PAborted }
} for exactly 3 Participant
