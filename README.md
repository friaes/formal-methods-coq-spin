# Coq & SPIN

Coursework for the **Systems Verification** course at the **University of Fribourg**, taken as part of my Master's in Computer Science. The course is an introduction to **formal methods** — mathematically proving that systems behave correctly — through the two dominant, complementary approaches:

- **Interactive theorem proving** with **Coq**, where you construct machine-checked proofs of program correctness.
- **Model checking** with **SPIN/Promela**, where a tool automatically explores all reachable states of a concurrent system to check whether it satisfies a specification.

The repository is split into a `coq/` half and a `spin/` half.

## Coq — interactive theorem proving

A sequence of tutorials building up from functional-programming foundations to formal verification of a real system, largely following the *Software Foundations* curriculum (Pierce et al.). Each tutorial is a literate `.v` Coq script mixing explanation, definitions, and proofs.

| Tutorial | Topic |
|----------|-------|
| `tut1` | **Pattern matching** — inductive types and destructuring |
| `tut2` | **Recursion** — inductively defined types (e.g. `nat` as `O`/`S n`) and recursive functions |
| `tut3` | **Polymorphism** — generic types and functions |
| `tut4` | **`Prop` and types** — propositions as types, the Curry–Howard correspondence, writing proofs |
| `tut5` | **Higher-order functions** — `map`/`fold`-style abstractions and reasoning about them |
| `tut6` | **Case study: Instruction Set Architectures** — formally modelling parts of the **AVR ISA** (8-bit binary numbers, instructions, and CPU execution semantics) in Coq |

The progression is deliberate: the functional-programming tutorials teach you to *define* things precisely, the logic tutorial teaches you that in Coq **a proof is a program and a proposition is a type**, and the capstone applies both to specify and reason about how a CPU executes assembly — a genuine systems-verification target.

## SPIN — model checking with Promela

A series of exercises using **SPIN** and its modelling language **Promela** to verify properties of concurrent systems. SPIN explores the entire reachable state space of a model and either proves a property holds or produces a concrete counterexample trace. The exercises walk through the core concepts:

- **Assertions & safety** (`series02`) — modelling processes and checking invariants with `assert`, and expressing safety violations as **never claims**. Explores how process **interleaving** in concurrent execution can violate properties that look fine sequentially.
- **Liveness, progress & fairness** (`series03`) — **progress labels**, **non-progress cycles** (a process being starved forever), and how **weak fairness** constraints change what the checker reports.
- **Modelling with data structures** (`series04`) — the classic **wolf–goat–cabbage river-crossing puzzle**, modelled two ways: with **arrays** and with **message-passing channels**. Neatly, the "safe" states are encoded as guards and the goal state as an assertion, so the model checker *solves the puzzle for you*: the counterexample trace it produces to violate `assert(!FINAL)` **is** the valid seven-crossing solution.
- **Temporal logic** (`series05`) — **Linear Temporal Logic (LTL)**: which temporal equivalences are valid (e.g. `[]p /\ []q ⇔ [](p /\ q)`), translating LTL formulae into **never claims / Büchi automata**, and expressing English requirements as LTL.
- Further series (`06`, `07`) with additional model-checking exercises, plus lecture material on mutual exclusion, Promela channels, and temporal logic.

Written answers and reasoning for the exercises are in the per-series `.md` and PDF files.

## Requirements

- **Coq** — via the [Coq Platform](https://github.com/coq/platform), `opam` (`vscoq-language-server` + the `maximedenes.vscoq` VS Code extension), CoqIDE, or the browser-based [jsCoq](https://jscoq.github.io/wa/scratchpad.html). `tut1` also ships a `Dockerfile` for a containerised setup.
- **SPIN** — the [Spin model checker](https://spinroot.com/) (`spin`), plus a C compiler (SPIN generates a C verifier that you compile and run).

## Usage

**Coq:** open a `.v` file in your Coq environment and step through it interactively, or check it in batch:

```bash
coqc coq/tut2/tutorial_02_recursion_sol.v
```

**SPIN:** simulate a model, or run full verification by generating and compiling the verifier:

```bash
cd spin/series04

# random/guided simulation
spin series04-channels.pml

# exhaustive verification
spin -a series04-channels.pml     # generate pan.c
gcc -o pan pan.c
./pan -a                          # explore the state space

# replay the counterexample trace SPIN found
spin -t -p series04-channels.pml
```

For the river-crossing model this reports an assertion violation — and the replayed trace spells out the sequence of crossings that gets everyone across safely.

## Repository layout

```
.
├── coq/
│   ├── tut1/  pattern matching        (+ Dockerfile, setup README)
│   ├── tut2/  recursion               (+ study agreement)
│   ├── tut3/  polymorphism
│   ├── tut4/  Prop & types
│   ├── tut5/  higher-order functions
│   └── tut6/  case study — AVR ISA
└── spin/
    ├── series01 … series07/   Promela models (.pml), write-ups (.md), sheets (PDF)
    └── *.pdf                  lecture notes: mutex, channels, temporal logic
```

## Notes

The tutorials and exercise sheets were course-provided scaffolding; the graded work is the completed Coq proofs/definitions in the `_sol`/`tpv` files and the Promela models plus the written reasoning in the `.md` files
