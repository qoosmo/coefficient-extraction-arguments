import CoeffExtract.MLEProduct
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace CoeffExtract

/-- Coefficient weight naturally produced by the product-form kernel:
bit `1` selects `(1-zᵢ)` and bit `0` selects `zᵢ`. -/
def productWeight {F : Type*} [CommRing F] {n : Nat}
    (z : Fin n → F) (j : Fin (2 ^ n)) : F :=
  ∏ i : Fin n, if Nat.testBit j.1 i.1 then 1 - z i else z i

def productWeightTable {F : Type*} [CommRing F] (n : Nat)
    (z : Fin n → F) : Table F (2 ^ n) :=
  fun j => productWeight z j

/-- Arithmetic complement of an `(n+1)`-bit number written with `Nat.bit`.
This is the low-level binary fact behind coefficient reversal. -/
lemma maskSub_bit (n q : Nat) (b : Bool) (hq : q < 2 ^ n) :
    2 ^ (n + 1) - 1 - Nat.bit b q =
      Nat.bit (!b) (2 ^ n - 1 - q) := by
  cases b <;>
    simp only [Nat.bit_val, Bool.toNat_false, Bool.toNat_true,
      Bool.not_false, Bool.not_true] <;>
    rw [pow_succ] <;>
    omega

/-- On the first `n` bits, `2^n - 1 - j` is the bitwise complement of `j`. -/
theorem maskSub_testBit (n j i : Nat)
    (hj : j < 2 ^ n) (hi : i < n) :
    Nat.testBit (2 ^ n - 1 - j) i = !(Nat.testBit j i) := by
  induction n generalizing j i with
  | zero =>
      omega
  | succ n ih =>
      by_cases hi0 : i = 0
      · subst i
        rw [← Nat.bit_bodd_div2 j]
        have hq : Nat.div2 j < 2 ^ n := by
          rw [Nat.div2_val]
          rw [pow_succ] at hj
          omega
        rw [maskSub_bit n (Nat.div2 j) (Nat.bodd j) hq]
        simp only [Nat.testBit_bit_zero]
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        rw [← Nat.bit_bodd_div2 j]
        have hq : Nat.div2 j < 2 ^ n := by
          rw [Nat.div2_val]
          rw [pow_succ] at hj
          omega
        rw [maskSub_bit n (Nat.div2 j) (Nat.bodd j) hq]
        simp only [Nat.testBit_bit_succ]
        apply ih
        · exact hq
        · omega

/-- `revIndex` on a `2^n`-entry table complements exactly the `n` binary
coordinate bits. -/
theorem revIndex_testBit
    {n : Nat} (j : Fin (2 ^ n)) (i : Fin n) :
    Nat.testBit (revIndex j).1 i.1 = !(Nat.testBit j.1 i.1) := by
  apply maskSub_testBit
  · exact j.2
  · exact i.2

/-- The reversed equality-weight table is exactly the coefficient table
naturally produced by the product-form kernel. -/
theorem mleKernelCoeffs_eq_productWeightTable
    {F : Type*} [CommRing F] (n : Nat) (z : Fin n → F) :
    mleKernelCoeffs n z = productWeightTable n z := by
  funext j
  unfold mleKernelCoeffs productWeightTable productWeight
  simp only [reverse_apply, mleWeightTable, mleWeight]
  apply Finset.prod_congr rfl
  intro i hi
  rw [revIndex_testBit]
  cases h : Nat.testBit j.1 i.1 <;> simp

end CoeffExtract
