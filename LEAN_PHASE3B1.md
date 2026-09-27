# Lean Phase 3B1 — binary coefficient bridge

This subphase proves the binary combinatorics hidden behind the product-form
MLE kernel.

Added:

- `productWeight`: coefficient weight selected directly by the product
  `∏ᵢ (zᵢ + (1-zᵢ) X^(2^i))`;
- `maskSub_bit`: arithmetic complement for `(n+1)`-bit `Nat.bit` values;
- `maskSub_testBit`: for `j < 2^n`, the bits of `2^n - 1 - j` are the Boolean
  complements of the bits of `j`;
- `revIndex_testBit`: the same fact packaged for the paper's `revIndex`;
- `mleKernelCoeffs_eq_productWeightTable`: the reversed MLE equality-weight
  table is exactly the coefficient table expected from the product-form kernel.

The remaining Phase 3B2 theorem is purely polynomial expansion:
`mleKernelProduct n z = tablePolynomial (productWeightTable n z)`.
Combined with this file, it yields
`mleKernelProduct n z = mleKernelPolynomial n z`.
