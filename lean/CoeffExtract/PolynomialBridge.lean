import CoeffExtract.CoefficientIdentity
import Mathlib.Algebra.Polynomial.Basic

open scoped BigOperators
open Polynomial

namespace CoeffExtract

/-- Mathlib `Polynomial` realization of the paper's table polynomial
`V_t(X) = ∑_{i=0}^{N-1} t(i) X^i`. -/
noncomputable def tablePolynomial {F : Type*} [Semiring F] {N : Nat}
    (t : Table F N) : F[X] :=
  ∑ i : Fin N, Polynomial.monomial i.1 (t i)

/-- The coefficient of `X^i` in the table polynomial is exactly the table
entry at `i`.  This is the bridge from the coefficient-vector model used in
Phase 1 to Mathlib's `Polynomial`. -/
@[simp] theorem tablePolynomial_coeff_fin {F : Type*} [Semiring F] {N : Nat}
    (t : Table F N) (i : Fin N) :
    (tablePolynomial t).coeff i.1 = t i := by
  classical
  simp [tablePolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, ← Fin.ext_iff]

/-- The table-polynomial map is injective. -/
theorem tablePolynomial_injective {F : Type*} [Semiring F] {N : Nat} :
    Function.Injective (tablePolynomial : Table F N → F[X]) := by
  intro a b h
  funext i
  have hc := congrArg (fun p : F[X] => p.coeff i.1) h
  simpa using hc

/-- Evaluation of a table directly from its coefficient vector. -/
def evalTable {F : Type*} [Semiring F] {N : Nat}
    (t : Table F N) (x : F) : F :=
  ∑ i : Fin N, t i * x ^ i.1

/-- Mathlib polynomial evaluation agrees with the direct coefficient-vector
formula. -/
@[simp] theorem eval_tablePolynomial {F : Type*} [CommSemiring F] {N : Nat}
    (t : Table F N) (x : F) :
    (tablePolynomial t).eval x = evalTable t x := by
  classical
  unfold tablePolynomial evalTable
  rw [Polynomial.eval_finsetSum]
  simp [Polynomial.eval_monomial]

/-- Polynomial realization of the coefficient reversal from Phase 1. -/
noncomputable def reversedTablePolynomial {F : Type*} [Semiring F] {N : Nat}
    (t : Table F N) : F[X] :=
  tablePolynomial (reverse t)

@[simp] theorem reversedTablePolynomial_coeff_fin
    {F : Type*} [Semiring F] {N : Nat}
    (t : Table F N) (i : Fin N) :
    (reversedTablePolynomial t).coeff i.1 = t (revIndex i) := by
  simp [reversedTablePolynomial]

/-- Reversing twice is the identity also after passing to Mathlib
polynomials. -/
@[simp] theorem reversedTablePolynomial_reverse
    {F : Type*} [Semiring F] {N : Nat} (t : Table F N) :
    reversedTablePolynomial (reverse t) = tablePolynomial t := by
  simp [reversedTablePolynomial]

end CoeffExtract
