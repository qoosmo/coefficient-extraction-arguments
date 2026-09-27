# Lean Phase 1 status

Commit: `6abd864`

## Formalized interface

- table coefficient encoding and bijectivity;
- coefficient-vector reversal and involution;
- middle-coefficient identity for arbitrary inner products;
- public linear functionals and hypercube sums;
- coefficient-form universal split construction and selected coefficient theorem.

## Proof policy

The source contains no `sorry`, `admit`, or `axiom` in the Phase 1 modules.
`AxiomAudit.lean` prints the axioms of the main declarations during CI.

## Validation status

Static placeholder checks were run in the artifact environment. The artifact environment does not contain Lean/Lake, so `lake build` could not be executed here. The repository pins Lean/Mathlib v4.33.1 and includes GitHub Actions plus `scripts/check-lean.sh` so the first local/GitHub build will give the authoritative type-check result.

## Next milestone

Add a Mathlib `Polynomial` bridge identifying the coefficient-level formalization with the paper's `F[X]_{<N}` notation, then formalize the table MLE kernel and virtual Reed--Solomon reversal.
