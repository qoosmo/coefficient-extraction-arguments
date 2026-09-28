import CoeffExtract.MLEProductRecursion
import Mathlib.Algebra.Ring.Parity

open scoped BigOperators
open Polynomial

namespace CoeffExtract

/-- Coefficients of a doubled-exponent polynomial at even indices. -/
@[simp] theorem coeff_expand_two_even
    {F : Type*} [CommRing F] (p : Polynomial F) (q : Nat) :
    (Polynomial.expand F 2 p).coeff (2 * q) = p.coeff q := by
  simpa using Polynomial.coeff_expand_mul' (R := F) (p := 2) (by decide) p q

/-- Coefficients of a doubled-exponent polynomial vanish at odd indices. -/
@[simp] theorem coeff_expand_two_odd
    {F : Type*} [CommRing F] (p : Polynomial F) (q : Nat) :
    (Polynomial.expand F 2 p).coeff (2 * q + 1) = 0 := by
  rw [Polynomial.coeff_expand (R := F) (p := 2) (by decide) p]
  simp [Nat.not_two_dvd_bit1]

/-- Even coefficient of a linear factor times a doubled-exponent polynomial. -/
theorem coeff_linear_mul_expand_even
    {F : Type*} [CommRing F] (a b : F) (p : Polynomial F) (q : Nat) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X) *
      Polynomial.expand F 2 p).coeff (2 * q) =
      a * p.coeff q := by
  rw [add_mul]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, mul_assoc]
  rw [coeff_expand_two_even]
  cases q with
  | zero =>
      simp
  | succ q =>
      have hidx : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
      rw [hidx, Polynomial.coeff_X_mul, coeff_expand_two_odd]
      simp

/-- Odd coefficient of a linear factor times a doubled-exponent polynomial. -/
theorem coeff_linear_mul_expand_odd
    {F : Type*} [CommRing F] (a b : F) (p : Polynomial F) (q : Nat) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X) *
      Polynomial.expand F 2 p).coeff (2 * q + 1) =
      b * p.coeff q := by
  rw [add_mul]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, mul_assoc]
  rw [coeff_expand_two_odd, Polynomial.coeff_X_mul, coeff_expand_two_even]
  simp

/-- Product weights split according to the least-significant bit. -/
theorem productWeight_even
    {F : Type*} [CommRing F] (n : Nat)
    (z : Fin (n + 1) → F) (q : Fin (2 ^ n)) :
    productWeight z
        ⟨2 * q.1, by
          rw [pow_succ]
          omega⟩ =
      z 0 * productWeight (fun i : Fin n => z i.succ) q := by
  unfold productWeight
  rw [Fin.prod_univ_succ]
  have hbit : 2 * q.1 = Nat.bit false q.1 := by
    simp [Nat.bit_val]
  have hzero : Nat.testBit (2 * q.1) 0 = false := by
    rw [hbit, Nat.testBit_bit_zero]
  have hsucc : ∀ i : Fin n,
      Nat.testBit (2 * q.1) i.succ = Nat.testBit q.1 i.1 := by
    intro i
    rw [hbit, Nat.testBit_bit_succ]
  simp [hzero, hsucc]

/-- Product weights split according to the least-significant bit. -/
theorem productWeight_odd
    {F : Type*} [CommRing F] (n : Nat)
    (z : Fin (n + 1) → F) (q : Fin (2 ^ n)) :
    productWeight z
        ⟨2 * q.1 + 1, by
          rw [pow_succ]
          omega⟩ =
      (1 - z 0) * productWeight (fun i : Fin n => z i.succ) q := by
  unfold productWeight
  rw [Fin.prod_univ_succ]
  have hbit : 2 * q.1 + 1 = Nat.bit true q.1 := by
    simp [Nat.bit_val]
  have hzero : Nat.testBit (2 * q.1 + 1) 0 = true := by
    rw [hbit, Nat.testBit_bit_zero]
  have hsucc : ∀ i : Fin n,
      Nat.testBit (2 * q.1 + 1) i.succ = Nat.testBit q.1 i.1 := by
    intro i
    rw [hbit, Nat.testBit_bit_succ]
  simp [hzero, hsucc]

/-- Every coefficient inside the `2^n` support of the product-form kernel is
the corresponding product weight. -/
theorem mleKernelProduct_coeff_fin
    {F : Type*} [CommRing F] :
    ∀ (n : Nat) (z : Fin n → F) (j : Fin (2 ^ n)),
      (mleKernelProduct n z).coeff j.1 = productWeight z j := by
  intro n
  induction n with
  | zero =>
      intro z j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      simp [mleKernelProduct, productWeight]
  | succ n ih =>
      intro z j
      obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' j.1
      · have hqN : q < 2 ^ n := by
          rw [pow_succ] at j.2
          omega
        let qf : Fin (2 ^ n) := ⟨q, hqN⟩
        let jf : Fin (2 ^ (n + 1)) :=
          ⟨2 * q, by
            rw [pow_succ]
            omega⟩
        have hj : j = jf := by
          apply Fin.ext
          exact hq
        rw [hj, mleKernelProduct_succ,
          coeff_linear_mul_expand_even]
        rw [ih (fun i => z i.succ) qf]
        simpa [jf, qf] using (productWeight_even n z qf).symm
      · have hqN : q < 2 ^ n := by
          rw [pow_succ] at j.2
          omega
        let qf : Fin (2 ^ n) := ⟨q, hqN⟩
        let jf : Fin (2 ^ (n + 1)) :=
          ⟨2 * q + 1, by
            rw [pow_succ]
            omega⟩
        have hj : j = jf := by
          apply Fin.ext
          exact hq
        rw [hj, mleKernelProduct_succ,
          coeff_linear_mul_expand_odd]
        rw [ih (fun i => z i.succ) qf]
        simpa [jf, qf] using (productWeight_odd n z qf).symm

/-- A table polynomial has no coefficients at or beyond its ambient table
length. -/
theorem tablePolynomial_coeff_eq_zero_of_ge
    {F : Type*} [Semiring F] {N k : Nat}
    (t : Table F N) (hk : N ≤ k) :
    (tablePolynomial t).coeff k = 0 := by
  classical
  unfold tablePolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.coeff_monomial]
  simp only [ite_eq_right_iff]
  intro hik
  have hiN : i.1 < N := i.2
  omega

/-- The product-form kernel is exactly the polynomial whose coefficient table
is `productWeightTable`. -/
theorem mleKernelProduct_eq_productWeightPolynomial
    {F : Type*} [CommRing F] (n : Nat) (z : Fin n → F) :
    mleKernelProduct n z =
      tablePolynomial (productWeightTable n z) := by
  ext k
  by_cases hk : k < 2 ^ n
  · let j : Fin (2 ^ n) := ⟨k, hk⟩
    calc
      (mleKernelProduct n z).coeff k
          = productWeight z j := by
              simpa [j] using (mleKernelProduct_coeff_fin n z j)
      _ = (productWeightTable n z) j := rfl
      _ = (tablePolynomial (productWeightTable n z)).coeff j.1 := by
              symm
              exact tablePolynomial_coeff_fin (productWeightTable n z) j
      _ = (tablePolynomial (productWeightTable n z)).coeff k := by
              rfl
  · have hk' : 2 ^ n ≤ k := Nat.le_of_not_gt hk
    rw [tablePolynomial_coeff_eq_zero_of_ge _ hk']
    obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' k
    · by_cases hn : n = 0
      · subst n
        have hp0 : mleKernelProduct 0 z = 1 := by
          simp [mleKernelProduct]
        rw [hp0]
        simp [hk]
      · cases n with
        | zero => contradiction
        | succ n =>
            rw [mleKernelProduct_succ, hq,
              coeff_linear_mul_expand_even]
            have hq' : 2 ^ n ≤ q := by
              rw [pow_succ] at hk'
              omega
            rw [mleKernelProduct_eq_productWeightPolynomial n
              (fun i => z i.succ)]
            rw [tablePolynomial_coeff_eq_zero_of_ge _ hq']
            simp
    · by_cases hn : n = 0
      · subst n
        have hp0 : mleKernelProduct 0 z = 1 := by
          simp [mleKernelProduct]
        rw [hp0]
        simp [hk]
      · cases n with
        | zero => contradiction
        | succ n =>
            rw [mleKernelProduct_succ, hq,
              coeff_linear_mul_expand_odd]
            have hq' : 2 ^ n ≤ q := by
              rw [pow_succ] at hk'
              omega
            rw [mleKernelProduct_eq_productWeightPolynomial n
              (fun i => z i.succ)]
            rw [tablePolynomial_coeff_eq_zero_of_ge _ hq']
            simp
termination_by n

/-- Final product/table bridge for the public multilinear-evaluation kernel. -/
theorem mleKernelProduct_eq_mleKernelPolynomial
    {F : Type*} [CommRing F] (n : Nat) (z : Fin n → F) :
    mleKernelProduct n z = mleKernelPolynomial n z := by
  rw [mleKernelProduct_eq_productWeightPolynomial]
  unfold mleKernelPolynomial
  rw [mleKernelCoeffs_eq_productWeightTable]

end CoeffExtract
