import CoeffExtract.MLEKernel
import Mathlib.Algebra.Polynomial.Eval.Defs

open scoped BigOperators
open Polynomial

namespace CoeffExtract

/-- The product-form public MLE kernel appearing in the paper:
`∏ᵢ (zᵢ + (1-zᵢ) X^(2^i))`. -/
noncomputable def mleKernelProduct {F : Type*} [CommRing F] (n : Nat)
    (z : Fin n → F) : Polynomial F :=
  ∏ i : Fin n,
    (Polynomial.C (z i) +
      Polynomial.C (1 - z i) * Polynomial.X ^ (2 ^ i.1))

/-- Evaluation of the product-form kernel is the corresponding product of
scalar affine factors.  This isolates the easy algebraic part of the product
representation from the binary-coefficient combinatorics. -/
@[simp] theorem eval_mleKernelProduct
    {F : Type*} [CommRing F] (n : Nat)
    (z : Fin n → F) (x : F) :
    (mleKernelProduct n z).eval x =
      ∏ i : Fin n, (z i + (1 - z i) * x ^ (2 ^ i.1)) := by
  classical
  simp [mleKernelProduct, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]

end CoeffExtract
