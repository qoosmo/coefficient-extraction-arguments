# Lean formalization

This directory mirrors the mathematical dependency order of the paper.  The
formalization is intentionally coefficient-first: Sections 3--4 are first
proved on finite coefficient vectors, which avoids importing cryptographic or
coding-theoretic machinery before the algebraic interface is frozen.  A later
bridge module will identify these definitions with `Mathlib`'s `Polynomial`
representation.

## Toolchain

- Lean 4.33.1
- Mathlib tag `v4.33.1`

## Phase 1: algebraic kernel

| Paper result | Lean file | Lean declaration |
|---|---|---|
| Table-form coefficients | `Basic.lean` | `tableCoeffs` |
| Table encoding is bijective | `Basic.lean` | `tableCoeffs_injective`, `tableCoeffs_surjective` |
| Reversal | `Reversal.lean` | `reverse` |
| Reversal involution | `Reversal.lean` | `reverse_reverse` |
| Middle coefficient / inner product | `CoefficientIdentity.lean` | `middleCoeff_reverse_eq_dot` |
| Public linear functional | `CoefficientIdentity.lean` | `publicLinearFunctional` |
| Hypercube sum | `CoefficientIdentity.lean` | `hypercubeSum` |
| Universal split, coefficient form | `UniversalSplit.lean` | `universalSplitCoeff` |
| Selected coefficient in split | `UniversalSplit.lean` | `splitValue_eq` |

No theorem in Phase 1 uses `sorry`, `admit`, or an axiom.

## Build

```bash
cd lean
lake update
lake build
```

The repository CI runs the same build and also rejects `sorry`, `admit`, or
`axiom` in `lean/CoeffExtract`.

## Next formalization milestone

1. Polynomial bridge to `F[X]_{<N}`.
2. Table-form multilinear evaluation kernel.
3. Virtual reversal on Reed--Solomon words.
4. Generic coefficient-extraction protocol.
5. Inner product and Hadamard arguments.
