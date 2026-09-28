# Lean Phase 3B2B — final MLE product/table bridge

This subphase closes the product-form MLE kernel proof.

It adds:

- even/odd coefficient lemmas for `Polynomial.expand F 2`;
- coefficient formulas for a linear factor times a doubled-exponent polynomial;
- even/odd recursion for `productWeight`;
- `mleKernelProduct_coeff_fin`;
- `mleKernelProduct_eq_productWeightPolynomial`;
- the final theorem

  `mleKernelProduct n z = mleKernelPolynomial n z`.

Combined with the Phase 2 middle-coefficient theorem, this formally identifies
the paper's product kernel with the reversed Boolean-equality coefficient
table used for multilinear evaluation.
