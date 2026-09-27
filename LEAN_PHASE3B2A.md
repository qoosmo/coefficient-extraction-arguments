# Lean Phase 3B2A — recursive product expansion

This subphase rewrites the product-form MLE kernel recursively.

For `z : Fin (n+1) → F` it proves

`mleKernelProduct (n+1) z
 = (C (z 0) + C (1-z 0) * X)
   * expand F 2 (mleKernelProduct n (fun i => z i.succ))`.

Mathematically, the first Boolean coordinate controls parity of the
coefficient index, while all remaining coordinates contribute powers with
doubled exponents.  `Polynomial.expand F 2` is therefore exactly the
substitution `X ↦ X²`.

This is the polynomial-side recursion needed for the final Phase 3B2
coefficient induction.
