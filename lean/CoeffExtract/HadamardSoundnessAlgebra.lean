import CoeffExtract.DeepQuotientInterface
import Mathlib.Algebra.Polynomial.Roots

open scoped BigOperators
open Polynomial

namespace CoeffExtract

def hadamardErrorTable
    {F : Type*} [Ring F] {N : Nat}
    (a b c : Table F N) : Table F N :=
  fun i => a i * b i - c i

@[simp] theorem hadamardErrorTable_apply
    {F : Type*} [Ring F] {N : Nat}
    (a b c : Table F N) (i : Fin N) :
    hadamardErrorTable a b c i = a i * b i - c i := rfl

noncomputable def hadamardFingerprintPolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (a b c : Table F N) : Polynomial F :=
  tablePolynomial (hadamardErrorTable a b c)

theorem eval_hadamardFingerprintPolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (a b c : Table F N) (γ : F) :
    (hadamardFingerprintPolynomial a b c).eval γ =
      weightedHadamardSum γ a b -
        (tablePolynomial c).eval γ := by
  classical
  unfold hadamardFingerprintPolynomial weightedHadamardSum
  rw [eval_tablePolynomial, eval_tablePolynomial]
  unfold evalTable
  simp only [hadamardErrorTable_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem hadamardFingerprintPolynomial_ne_zero
    {F : Type*} [CommRing F] {N : Nat}
    (a b c : Table F N)
    (hfalse : hadamard a b ≠ c) :
    hadamardFingerprintPolynomial a b c ≠ 0 := by
  intro hzero
  apply hfalse
  funext i
  have hc := congrArg
    (fun p : Polynomial F => p.coeff i.1) hzero
  simp [hadamardFingerprintPolynomial, hadamardErrorTable,
    hadamard] at hc
  exact sub_eq_zero.mp hc

theorem tablePolynomial_natDegree_lt
    {F : Type*} [Semiring F] {N : Nat}
    (hN : 0 < N) (t : Table F N) :
    (tablePolynomial t).natDegree < N := by
  rw [Nat.lt_iff_le_pred hN]
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro r hr
  apply tablePolynomial_coeff_eq_zero_of_ge
  omega

theorem hadamardFingerprintPolynomial_natDegree_le
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (a b c : Table F N) :
    (hadamardFingerprintPolynomial a b c).natDegree ≤ N - 1 := by
  unfold hadamardFingerprintPolynomial
  exact (Nat.lt_iff_le_pred hN).mp
    (tablePolynomial_natDegree_lt hN (hadamardErrorTable a b c))

noncomputable def zeroChallengeFinset
    {F : Type*} [Field F] [Fintype F]
    (p : Polynomial F) : Finset F := by
  classical
  exact Finset.univ.filter (fun x => p.eval x = 0)

theorem card_zeroChallengeFinset_le_natDegree
    {F : Type*} [Field F] [Fintype F]
    (p : Polynomial F) (hp : p ≠ 0) :
    (zeroChallengeFinset p).card ≤ p.natDegree := by
  classical
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  have hx0 : p.eval x = 0 := by
    simpa [zeroChallengeFinset] using hx
  rw [Polynomial.mem_roots']
  exact ⟨hp, hx0⟩

theorem card_bad_hadamard_gamma_le
    {F : Type*} [Field F] [Fintype F] {N : Nat}
    (hN : 0 < N) (a b c : Table F N)
    (hfalse : hadamard a b ≠ c) :
    (zeroChallengeFinset
      (hadamardFingerprintPolynomial a b c)).card ≤ N - 1 := by
  exact (card_zeroChallengeFinset_le_natDegree _
      (hadamardFingerprintPolynomial_ne_zero a b c hfalse)).trans
    (hadamardFingerprintPolynomial_natDegree_le hN a b c)

noncomputable def scalingErrorPolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (Q : Polynomial F) (γ : F) (a : Table F N) : Polynomial F :=
  Q - scaledTablePolynomial γ a

theorem scalingErrorPolynomial_ne_zero
    {F : Type*} [CommRing F] {N : Nat}
    (Q : Polynomial F) (γ : F) (a : Table F N)
    (hQ : Q ≠ scaledTablePolynomial γ a) :
    scalingErrorPolynomial Q γ a ≠ 0 := by
  simpa [scalingErrorPolynomial, sub_ne_zero] using hQ

theorem scalingErrorPolynomial_natDegree_lt
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (Q : Polynomial F) (γ : F) (a : Table F N)
    (hQdeg : Q.natDegree < N) :
    (scalingErrorPolynomial Q γ a).natDegree < N := by
  unfold scalingErrorPolynomial
  exact lt_of_le_of_lt
    (Polynomial.natDegree_sub_le Q (scaledTablePolynomial γ a))
    (max_lt hQdeg
      (by
        unfold scaledTablePolynomial
        exact tablePolynomial_natDegree_lt hN (geometricScale γ a)))

theorem eval_scalingErrorPolynomial_eq_zero_iff
    {F : Type*} [Field F] {N : Nat}
    (Q : Polynomial F) (γ θ : F) (a : Table F N) :
    (scalingErrorPolynomial Q γ a).eval θ = 0 ↔
      Q.eval θ = (tablePolynomial a).eval (γ * θ) := by
  unfold scalingErrorPolynomial
  rw [Polynomial.eval_sub, eval_scaledTablePolynomial]
  exact sub_eq_zero

theorem card_bad_scaling_theta_le
    {F : Type*} [Field F] [Fintype F] {N : Nat}
    (hN : 0 < N) (Q : Polynomial F) (γ : F) (a : Table F N)
    (hQdeg : Q.natDegree < N)
    (hwrong : Q ≠ scaledTablePolynomial γ a) :
    (zeroChallengeFinset
      (scalingErrorPolynomial Q γ a)).card ≤ N - 1 := by
  have hdeg :
      (scalingErrorPolynomial Q γ a).natDegree ≤ N - 1 :=
    (Nat.lt_iff_le_pred hN).mp
      (scalingErrorPolynomial_natDegree_lt hN Q γ a hQdeg)
  exact (card_zeroChallengeFinset_le_natDegree _
      (scalingErrorPolynomial_ne_zero Q γ a hwrong)).trans hdeg

end CoeffExtract
