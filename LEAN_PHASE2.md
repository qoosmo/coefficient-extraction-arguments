# Lean Phase 2 — polynomial bridge and table-MLE kernel

## Added

- `CoeffExtract/PolynomialBridge.lean`
  - Mathlib `Polynomial` realization `tablePolynomial` of the paper's table polynomial `V_t`.
  - coefficient recovery theorem;
  - injectivity;
  - direct evaluation bridge;
  - polynomial realization of coefficient reversal.

- `CoeffExtract/MLEKernel.lean`
  - Boolean equality weights using the fixed binary index convention;
  - MLE weight table;
  - reversed public kernel coefficients;
  - Mathlib polynomial kernel object;
  - coefficient-extraction theorem reducing table-MLE evaluation to the Phase-1 middle-coefficient identity.

- `CoeffExtract/VirtualReversal.lean`
  - packages `revIndex` as a `Fin N ≃ Fin N` equivalence;
  - reusable word permutation abstraction;
  - involution theorem for word permutations;
  - identifies coefficient reversal with the reversal position permutation.

## Formalization boundary

This phase deliberately separates two facts:

1. the table-MLE evaluation functional is already proved as a middle-coefficient identity; and
2. the paper's *product-form* kernel
   `∏ᵢ (zᵢ + (1-zᵢ) X^(2^i))`
   still needs a theorem identifying it with `mleKernelPolynomial`.

Likewise, the field-valued virtual RS identity
`w*(ξ) = ξ^(N-1) w(ξ⁻¹)`
will be proved after the polynomial-product/reversal bridge, rather than being introduced as an axiom.

## Verification

The source contains no `sorry`, `admit`, or user-declared `axiom`.  The repository CI remains configured to run `lake build` and `AxiomAudit.lean` with Mathlib/Lean `v4.33.1`.

This container does not provide Lean/Lake, so compilation must be certified by the GitHub Actions job or a local `./scripts/check-lean.sh` run.
