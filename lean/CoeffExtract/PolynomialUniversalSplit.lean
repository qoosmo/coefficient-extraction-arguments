import CoeffExtract.UniversalSplit
import CoeffExtract.PolynomialCoefficientIdentity
import Mathlib.Algebra.Polynomial.Coeff

open scoped BigOperators
open Polynomial

namespace CoeffExtract

noncomputable def splitLowPolynomial {F : Type*} [Semiring F]
    (N : Nat) (c : Nat → F) : Polynomial F :=
  tablePolynomial (splitLow N c)

noncomputable def splitHighPolynomial {F : Type*} [Semiring F]
    (N : Nat) (c : Nat → F) : Polynomial F :=
  tablePolynomial (splitHigh N c)

noncomputable def recombineSplitPolynomial {F : Type*} [Semiring F]
    (N : Nat) (c : Nat → F) : Polynomial F :=
  splitLowPolynomial N c +
    Polynomial.C (splitValue N c) * Polynomial.X ^ N +
    Polynomial.X ^ (N + 1) * splitHighPolynomial N c

/-- Multiplication by `X` has coefficient sequence `xShift`. -/
theorem coeff_X_mul_eq_xShift
    {F : Type*} [Semiring F] (p : Polynomial F) (r : Nat) :
    (Polynomial.X * p).coeff r = xShift p.coeff r := by
  cases r with
  | zero =>
      simp [xShift, Polynomial.coeff_X_mul_zero]
  | succ r =>
      simp [xShift, Polynomial.coeff_X_mul]

/-- Under the same support hypothesis as `universalSplitCoeff`, the polynomial
reconstruction has coefficient sequence `recombineSplit`. -/
theorem coeff_recombineSplitPolynomial
    {F : Type*} [Semiring F] (N : Nat) (c : Nat → F)
    (hsupp : ∀ r, 2 * N - 1 ≤ r → c r = 0) (r : Nat) :
    (recombineSplitPolynomial N c).coeff r =
      recombineSplit N (splitLow N c) (splitValue N c) (splitHigh N c) r := by
  classical
  by_cases hN0 : N = 0
  · subst N
    simp [recombineSplitPolynomial, splitLowPolynomial, splitHighPolynomial,
      tablePolynomial, splitLow, splitHigh, splitValue, xShift, recombineSplit]
  unfold recombineSplitPolynomial splitLowPolynomial splitHighPolynomial
  by_cases hA : r < N
  · have hNle : ¬ N ≤ r := Nat.not_le.mpr hA
    have hN1le : ¬ N + 1 ≤ r := by omega
    have hNr : ¬ N < r := by omega
    have hrN : r ≠ N := by omega
    let i : Fin N := ⟨r, hA⟩
    rw [Polynomial.coeff_add, Polynomial.coeff_add]
    rw [show r = i.1 by rfl, tablePolynomial_coeff_fin]
    rw [Polynomial.coeff_C_mul_X_pow, if_neg hrN]
    rw [Polynomial.coeff_X_pow_mul']
    simp [hN1le, hNr, recombineSplit, hA, i]
  by_cases hV : r = N
  · subst r
    have hN1le : ¬ N + 1 ≤ N := by omega
    simp [recombineSplit, hA, hN1le,
      tablePolynomial_coeff_eq_zero_of_ge,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow_mul']
  by_cases hH : r < 2 * N
  · have hN1 : N + 1 ≤ r := by omega
    have htail : r - (N + 1) < N := by omega
    let i : Fin N := ⟨r - (N + 1), htail⟩
    have hlow : N ≤ r := by omega
    rw [Polynomial.coeff_add, Polynomial.coeff_add]
    rw [tablePolynomial_coeff_eq_zero_of_ge _ hlow]
    rw [Polynomial.coeff_C_mul_X_pow, if_neg hV]
    rw [Polynomial.coeff_X_pow_mul']
    simp only [hN1, if_true, zero_add, zero_add]
    rw [show r - (N + 1) = i.1 by rfl, tablePolynomial_coeff_fin]
    simp [recombineSplit, hA, hV, hH, i]
  · have h2N : 2 * N ≤ r := Nat.le_of_not_gt hH
    have hlow : N ≤ r := by omega
    have hN1 : N + 1 ≤ r := by omega
    have hhigh :
        (tablePolynomial (splitHigh N c)).coeff (r - (N + 1)) = 0 := by
      by_cases hd : r - (N + 1) < N
      · let i : Fin N := ⟨r - (N + 1), hd⟩
        have hs :
            2 * N - 1 ≤ (N + 1 + i.1) - 1 := by
          dsimp [i]
          omega
        have hc := hsupp ((N + 1 + i.1) - 1) hs
        have heq : (N + 1 + i.1) - 1 = N + i.1 := by omega
        have hc' : c (N + i.1) = 0 := by
          simpa [heq] using hc
        rw [show r - (N + 1) = i.1 by rfl, tablePolynomial_coeff_fin]
        simp [splitHigh, xShift, hc']
      · exact tablePolynomial_coeff_eq_zero_of_ge _
          (Nat.le_of_not_gt hd)
    rw [Polynomial.coeff_add, Polynomial.coeff_add]
    rw [tablePolynomial_coeff_eq_zero_of_ge _ hlow]
    rw [Polynomial.coeff_C_mul_X_pow]
    rw [if_neg hV]
    rw [Polynomial.coeff_X_pow_mul']
    simp only [hN1, if_true]
    rw [hhigh]
    simp [recombineSplit, hA, hV, hH]

/-- Polynomial form of the universal split:
`X P = A + v X^N + X^(N+1) H`. -/
theorem universalSplitPolynomial
    {F : Type*} [CommSemiring F]
    (N : Nat) (p : Polynomial F)
    (hsupp : ∀ r, 2 * N - 1 ≤ r → p.coeff r = 0) :
    Polynomial.X * p =
      recombineSplitPolynomial N p.coeff := by
  ext r
  rw [coeff_X_mul_eq_xShift]
  rw [coeff_recombineSplitPolynomial N p.coeff hsupp r]
  exact universalSplitCoeff N p.coeff hsupp r

/-- Product of two length-`N` table polynomials has no coefficient at or above
degree `2N-1`. -/
theorem tablePolynomial_mul_support
    {F : Type*} [CommSemiring F] {N : Nat}
    (u k : Table F N) (r : Nat)
    (hr : 2 * N - 1 ≤ r) :
    (tablePolynomial u * tablePolynomial k).coeff r = 0 := by
  classical
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hsum : x.1 + x.2 = r := Finset.mem_antidiagonal.mp hx
  by_cases h₁ : x.1 < N
  · have h₂ : N ≤ x.2 := by omega
    rw [tablePolynomial_coeff_eq_zero_of_ge k h₂]
    simp
  · have h₁' : N ≤ x.1 := Nat.le_of_not_gt h₁
    rw [tablePolynomial_coeff_eq_zero_of_ge u h₁']
    simp

/-- Universal split specialized to two committed length-`N` table
polynomials. -/
theorem universalSplit_tablePolynomial_mul
    {F : Type*} [CommSemiring F] {N : Nat}
    (u k : Table F N) :
    Polynomial.X * (tablePolynomial u * tablePolynomial k) =
      recombineSplitPolynomial N
        (tablePolynomial u * tablePolynomial k).coeff := by
  apply universalSplitPolynomial
  intro r hr
  exact tablePolynomial_mul_support u k r hr

/-- For positive `N`, the selected split value in the product specialization
is the middle coefficient `[X^(N-1)] U K`. -/
theorem splitValue_tablePolynomial_mul_eq_middleCoeff
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (u k : Table F N) :
    splitValue N (tablePolynomial u * tablePolynomial k).coeff =
      middleCoeff u k := by
  rw [splitValue_eq N _ hN]
  exact coeff_tablePolynomial_mul_eq_middleCoeff hN u k

end CoeffExtract
