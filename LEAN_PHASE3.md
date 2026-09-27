# Lean Phase 3A — product kernel interface and exact RS reversal

This update adds two independent bridges needed by the protocol layer.

## Product-form kernel

`CoeffExtract/MLEProduct.lean` defines the paper's public kernel

`∏ᵢ (zᵢ + (1-zᵢ) X^(2^i))`

as a Mathlib polynomial and proves its evaluation formula.

The remaining Phase 3B theorem is the binary-coefficient identification

`mleKernelProduct n z = mleKernelPolynomial n z`.

That theorem contains the real binary subset/bit-index combinatorics and is
kept separate so it is proved explicitly rather than hidden behind an axiom.

## Virtual Reed–Solomon reversal

`CoeffExtract/RSReversal.lean` proves the exact fixed-length identity

`V*(ξ) = ξ^(N-1) V(ξ⁻¹)`

for nonzero `ξ`, and then lifts it to an inversion-closed indexed RS domain:

`RS(V*, ξ_i) = ξ_i^(N-1) RS(V, ξ_{σ(i)})`

whenever the public permutation `σ` satisfies
`ξ_{σ(i)} = ξ_i⁻¹`.

No new axioms or placeholders are introduced.
