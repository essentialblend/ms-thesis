# Type-theoretic Proofs for the Ring Axioms of the Integers

This research project was submitted as part of requirements for my MS. The objective was to prove the existence of a certain mathematical construct called a _Ring_. This was achieved with the help of a computer-aided proof-assistant called _Agda_, a programming language based on intuitionistic type theory, also called Martin-Löf type theory (MLTT).

This research project was supervised by Prof. Thorsten Altenkirch and I’m forever grateful for his time, expertise, and empathy towards my journey into this fantastic subject. 

I'm lucky to have Dan from over at the Univalent Agda Discord server for a close friend who spent countless hours just so I get to feel less clueless with each passing day.

## Build Instructions

### Prereqs

- Git, CMake 3.10 or higher, Agda 2.7.0.1 or higher
- Please check https://agda.readthedocs.io/en/stable/getting-started/installation.html for platform-specific Agda installation instructions

### Build & Verify 

```bash
git clone https://github.com/essentialblend/ms-thesis.git
cd ms-thesis
cmake -B build -S .
cmake --build build
```

## Details

This project develops a fully constructive, machine-verified formalization of the commutative ring of integers in Agda. Beginning from an entirely independent definition of the natural numbers (ℕ) and integers (ℤ), the development proceeds in four major phases:

### Core Definitions
- We define the naturals as an inductive datatype with constructors `zero` and `suc`.
- Then, we extend the naturals to the integers as a record with two fields, a sign and a (natural) magnitude respectively.
- None of these constructions rely on Agda’s standard library; they're built from first principles.

### Basic Operations and Properties over the Naturals
- We implement all necessary binary operations inducting over the constructors.
- We prove key lemmas (assoc, comm, identities, etc.) for the naturals.
- These proofs serve as a pedagogical warmup. Anyone wanting a self-contained library-independent introduction to reasoning in Agda may follow this section.

### Operations and Properties of the Integers
- Using the naturals, we define integer addition, multiplication, negation, etc.
- We prove every property needed to show the ring axioms, similar to the naturals.
- Modular records are instantiated for the integers, certifying the _final_ Ring object in Agda.

### Extensibility and Documentation
- The codebase totals 34 Agda modules and ~900 lines of Agda code (as measured by `cloc`).
- Nearly 100 specialized lemmas and proofs encapsulated into  generic, reusable, extensible interfaces--- i.e., extend to other number systems and/or abstract algebraic structures.
- Each module begins with a declaration, followed by necessary imports, lemmas, and concluding with the proofs. The entire development compiles in a single step with `agda --ignore-interfaces -i .`.

## Results

### Complete, Standalone Formalization
We deliver a self-contained library of 34 modules (~900 lines) that formalizes and verifies the commutative-ring axioms for the integers in MLTT. No part of Agda's STL is used, _all proofs are written by hand._

### Machine-Checked Rigor
Computer aided proof assistants rigorously verify every module, guaranteeing total correctness via Agda's type checker.

### Modularity and Extensibility
This repo includes almost **100 lemmas** organized into small, reusable modules. Anyone can import these to build fields, polynomial rings, or experiment with more complex properties which critically necessitate robust constructions. 

### Pedagogical Value
By reconstructing number systems and building more complex structures over them without external dependencies, this development doubles as a tutorial in _constructive logic_.

### Maintainability
Verification takes mere seconds on a modern computer. The library is easy to navigate: each top-level record lives in `integers/comm-ring/records.agda` and all supporting lemmas are grouped under `integers/props`.
