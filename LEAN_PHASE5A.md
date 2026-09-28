# Lean Phase 5A — committed inner-product algebraic interface

This phase packages the polynomial machinery into the exact algebraic
interface used by Section 8 of the paper.

It adds:

- `innerProductPolynomial = V_a * V_b^*`;
- canonical low/high split witnesses `A` and `H`;
- the claimed opening polynomial
  `A + S X^N + X^(N+1) H`;
- proof that the split value is `dot a b`;
- the canonical opening identity
  `X V_a V_b^* = A + <a,b> X^N + X^(N+1) H`;
- extraction of the middle coefficient from both sides;
- algebraic binding: any claimed `S` satisfying the canonical opening identity
  equals `dot a b`;
- the final iff characterization.

No Merkle, Reed--Solomon proximity, or FRI soundness is introduced in this
phase.  Those remain protocol/backend layers.
