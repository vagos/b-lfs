# Curiosity Modeling: Modeling the UNIX Filesystem and Filesystem-manipulating Commands

Prompt template used:

```
A student in Brown's CSCI 1710, a lightweight formal-methods course using Forge, is starting their midterm project. They have lots of freedom to explore a domain that's interesting to them, but are also looking for ways that their work on the project can support their goals in the course. Provide feedback on the following idea(s), given the following student profile. Keep the feedback fact-based, concise and natural. Remember that the student has not been using Forge for long, and can seek further advice from course staff. Feedback should focus on (1) helping to make the idea technically well-defined; (2) potential modeling pitfalls and places to seek advice; and (3) advice on potential, easily implemented, project enhancements tailored to the student's interests.  Do not provide Forge code or documentation.

PROJECT IDEA: Modelling the UNIX filesystem and commands interacting with it, such as `cat`, `rm`, `cp`, and `mv`.

STUDENT PROFILE: 

Vagos' profile:
My avatar is a researcher interested in applying formal methods to verify key properties of the practical systems they are developing.
In addition, they want to be able to understand concepts from the CSCI 1710 course to the point where they can teach parts relevant to courses they are helping develop (for example, Distributed Systems).

Zekai's profile:
The avatar I developed is students who are preparing to apply for a PhD in formal methods and wants to build a stronger, more complete foundation before stepping into deeper research.
They already have experience closely tied to formal methods and programming languages, but they suspect there are still gaps in their knowledge. Their learning goals include 1) solidifying their understanding of formal methods, 2) having more understanding on logic constraint programming and model checking and 3) learning how to communicate formal methods ideas with others. Course 1710 will help them by offering them structured practice designing and iterating on formal models, making them familiar with Forge (and potentially the design ideas and choices behind it), and giving them opportunities to discuss the topics with peers and instructors.
```

ChatGPT's response:

```
Modeling a UNIX filesystem and core commands is a well-scoped project that highlights state invariants, transition semantics, and safety properties. Define a minimal abstraction: a hierarchical tree with directories and files, deterministic path resolution, and a clear notion of identity. Treat commands (cat, rm, cp, mv) as state transitions with explicit preconditions and postconditions, and specify invariants such as tree acyclicity, absence of dangling references, preservation of identity under mv, and non-aliasing under cp. Starting with a small scope (e.g., no recursive deletion or permissions) will keep the model analyzable and help clarify correctness properties.

Key pitfalls include path-resolution complexity, confusing file identity with content, handling deletion semantics, and state explosion from deep trees or copying. Seek staff guidance on representing hierarchy and transitions cleanly and on controlling scope. If time allows, enhancements aligned with systems and formal-methods interests include checking command commutativity, modeling failure atomicity, adding inode/link abstractions, or exploring simple concurrent interleavings. Documenting abstraction choices and tradeoffs will strengthen both pedagogical value and formal rigor.
```
# Main Response

## Project Objective
This project models a simplified UNIX-style file system and command behavior over time.
The goal is to verify both structure (the file system remains a rooted tree) and behavior (each command changes only what it should).
Ideally, the model should be able to verify incorrect command compositions.
For example, invoking `rm f; rm f` is invalid (file `f` is deleted twice), while `cp f g; rm f` is valid (file `f` is copied to `g`, then `f` is deleted).

## Model Design and Visualization
The model uses a `State` signature with relations for object liveness (`live`), hierarchy (`parent`), root directory (`root`), and trace progression (`next`).

The `trace` enforces a linear history.
It starts from `init`,
each transition satisfies `step`, and
there are no cycles in `next`
`step` is a choice among command predicates: `touch`, `mkdir`, `rm`, `rmr`, `mv`, and `cp`.

We developed a custom visualization for Sterling.
Each state is shown as a filesystem tree (root, directories, and files), and each card includes the `FsObj`s involved in the transition from the previous state (`added`, `removed`, and `moved`).
One improvement we plan to make is to propagate the information about which command is invoked at each transition, in order for the visualization to have a clearer one-to-one mapping to the command sequence under test.

## Signatures and Predicates
The `FsObj` type describes the abstract file-system object type; `File` and `Dir` extend it.
A `State` represents one snapshot of the system.
The `isLive`/`isDead` predicates describe whether an object can exist or not across states.
The `wellformed` predicate encodes our core invariants: live root, root has no parent, every live non-root object has a live parent, no parent cycles, and that the root directory is reachable from every live object.
We also developed six transition predicates define command preconditions and postconditions which specify how a command invocation would affect the filesystem topology across two consecutive (`pre` and `post`) states. 

## Testing
The model is tested with five test instances:
1.`fileSystemTests`: baseline sat/unsat sanity checks for structure
2.`transitionTests`: command precondition and transition validity
3.`propertyTests`: preservation and trace-level invariant checks
4.`traceUnsat`: behavior that must be impossible, i.e., a buggy command composition
5.`traceSat`: behavior that must be possible, i.e., a valid command composition

## Documentation
The Forge file includes comments for invariants, transitions, and test groups.  
