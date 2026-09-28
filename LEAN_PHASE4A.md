# Lean Phase 4A — polynomial coefficient-extraction identities

This phase moves the already-proved table-level coefficient identities into
Mathlib's actual `Polynomial` multiplication interface.

It adds:

- `coeff_tablePolynomial_mul_eq_middleCoeff`;
- the polynomial inner-product identity
  `[X^(N-1)] V_a(X) V_b*(X) = dot a b`;
- polynomial public-linear-functional extraction;
- polynomial hypercube-sum extraction.

This is the algebraic bridge needed before formalizing the committed
inner-product protocol layer.
