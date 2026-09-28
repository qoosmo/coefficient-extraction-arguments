import CoeffExtract.MLEProductBridge
import Mathlib.Algebra.BigOperators.NatAntidiagonal

open scoped BigOperators
open Polynomial

namespace CoeffExtract

/-- Polynomial-level realization of the abstract `middleCoeff` functional.

For positive table length `N`, the coefficient of degree `N-1` in the product
of the two table polynomials is exactly the finite middle-coefficient sum. -/
theorem coeff_tablePolynomial_mul_eq_middleCoeff
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (u k : Table F N) :
    (tablePolynomial u * tablePolynomial k).coeff (N - 1) =
      middleCoeff u k := by
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsucc : (N - 1).succ = N := by omega
  rw [hsucc]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold middleCoeff
  apply Finset.sum_congr rfl
  intro i hi
  rw [tablePolynomial_coeff_fin]
  have hrev : N - 1 - i.1 = (revIndex i).1 := by
    rw [revIndex_val]
  rw [hrev, tablePolynomial_coeff_fin]

/-- Polynomial inner-product identity:
`[X^(N-1)] V_a(X) V_b*(X) = <a,b>`. -/
theorem coeff_tablePolynomial_mul_reversed_eq_dot
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (a b : Table F N) :
    (tablePolynomial a * reversedTablePolynomial b).coeff (N - 1) =
      dot a b := by
  unfold reversedTablePolynomial
  rw [coeff_tablePolynomial_mul_eq_middleCoeff hN]
  exact middleCoeff_reverse_eq_dot a b

/-- Polynomial form of a public linear functional. -/
theorem coeff_tablePolynomial_mul_public_eq
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (a p : Table F N) :
    (tablePolynomial a * reversedTablePolynomial p).coeff (N - 1) =
      ∑ i : Fin N, a i * p i := by
  rw [coeff_tablePolynomial_mul_reversed_eq_dot hN]
  rfl

/-- Polynomial form of the hypercube-sum functional. -/
theorem coeff_tablePolynomial_mul_ones_eq_sum
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (a : Table F N) :
    (tablePolynomial a *
      reversedTablePolynomial (fun _ : Fin N => (1 : F))).coeff (N - 1) =
      ∑ i : Fin N, a i := by
  rw [coeff_tablePolynomial_mul_reversed_eq_dot hN]
  simp [dot]

end CoeffExtract
