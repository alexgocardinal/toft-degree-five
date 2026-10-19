# Toft's degree-five question

An explicit 15-vertex, 30-edge counterexample to the question
in Jensen and Toft, Graph Coloring Problems (1995), Section 5.5,
pp. 101–102.

Author: Alex Chan, Harvard University and NBER.

## Build the Lean proof

Install Lean through elan, then run from this directory:

    lake build

The exact Lean version is recorded in lean-toolchain.
No Mathlib dependency is required.

The main theorem is ToftDegreeFive.counterexample, in
ToftDegreeFive.lean. It establishes full 4-criticality,
a vertex with exactly five neighbors, a nonconstant forbidden
assignment, and the absence of a three-coloring of the
vertex-deleted graph avoiding that assignment.

The graph is represented by an explicit finite edge list.
The proof includes all 30 edge-deletion coloring witnesses.

## Verification scope

The main theorem depends only on Lean's standard axioms:
propext, Classical.choice, and Quot.sound.
It does not use sorry or native computation axioms.

The infinite family obtained by Hajós extensions is not
formalized in this Lean project. No minimum-order or
publication-priority claim is made.

## Computational certificates

The original base graph data, readable proof, and independent
Python checks are in certificates/base.

Run:

    python3 certificates/base/verify_certificate.py
    python3 certificates/base/verify_rup.py
