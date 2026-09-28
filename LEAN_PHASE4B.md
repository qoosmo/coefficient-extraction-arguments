# Lean Phase 4B — polynomial universal split

This phase lifts the universal coefficient-sequence split to Mathlib
polynomials.

Target identity:

`X * P = A + v * X^N + X^(N+1) * H`.

It adds:

- polynomial low/high split components;
- `coeff_X_mul_eq_xShift`;
- coefficient correctness for the reconstructed split polynomial;
- `universalSplitPolynomial`;
- the product-support theorem for two length-`N` table polynomials;
- specialization to `tablePolynomial u * tablePolynomial k`;
- identification of the selected split value with the middle coefficient.

This closes the polynomial algebra needed before the committed inner-product
protocol layer.
