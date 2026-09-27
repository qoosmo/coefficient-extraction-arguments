import CoeffExtract.BinaryKernelBridge
import Mathlib.Algebra.Polynomial.Expand

open scoped BigOperators
open Polynomial

namespace CoeffExtract

/-- Base case for the product-form MLE kernel. -/
@[simp] theorem mleKernelProduct_zero
    {F : Type*} [CommRing F] :
    mleKernelProduct (F := F) 0 (fun i => Fin.elim0 i) = 1 := by
  simp [mleKernelProduct]

/-- Recursive decomposition of the product-form MLE kernel.

The least-significant Boolean coordinate contributes the linear factor
`z₀ + (1-z₀)X`.  Every remaining exponent is doubled, so the tail kernel is
obtained by `Polynomial.expand F 2`, i.e. by substituting `X²` for `X`. -/
theorem mleKernelProduct_succ
    {F : Type*} [CommRing F] (n : Nat)
    (z : Fin (n + 1) → F) :
    mleKernelProduct (n + 1) z =
      (Polynomial.C (z 0) +
        Polynomial.C (1 - z 0) * Polynomial.X) *
      Polynomial.expand F 2
        (mleKernelProduct n (fun i => z i.succ)) := by
  classical
  unfold mleKernelProduct
  rw [Fin.prod_univ_succ]
  congr 1
  · simp
  · rw [map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [map_add, Polynomial.expand_C, map_mul, map_pow,
      Polynomial.expand_X, Fin.val_succ]
    rw [pow_succ]
    simp [pow_mul, mul_comm, mul_left_comm, mul_assoc]

end CoeffExtract
