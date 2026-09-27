import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace CoeffExtract

/-- A length-`N` table. In the paper, `N = 2^n` and indices are Boolean
hypercube points written in binary order. -/
abbrev Table (F : Type*) (N : Nat) := Fin N → F

/-- The table-form Kronecker coefficient vector.  At the coefficient-vector
level this is the identity map: the table entries are used verbatim as the
coefficients of `V_t(X) = ∑ t(i) X^i`. -/
def tableCoeffs {F : Type*} {N : Nat} (t : Table F N) : Table F N := t

@[simp] theorem tableCoeffs_apply {F : Type*} {N : Nat}
    (t : Table F N) (i : Fin N) : tableCoeffs t i = t i := rfl

theorem tableCoeffs_injective {F : Type*} {N : Nat} :
    Function.Injective (tableCoeffs : Table F N → Table F N) := by
  intro a b h
  exact h

theorem tableCoeffs_surjective {F : Type*} {N : Nat} :
    Function.Surjective (tableCoeffs : Table F N → Table F N) := by
  intro a
  exact ⟨a, rfl⟩

/-- Inner product of two committed tables. -/
def dot {F : Type*} [Semiring F] {N : Nat} (a b : Table F N) : F :=
  ∑ i : Fin N, a i * b i

@[simp] theorem dot_zero_left {F : Type*} [Semiring F] {N : Nat}
    (b : Table F N) : dot (fun _ => 0) b = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right {F : Type*} [Semiring F] {N : Nat}
    (a : Table F N) : dot a (fun _ => 0) = 0 := by
  simp [dot]

/-- Pointwise (Hadamard) product. -/
def hadamard {F : Type*} [Mul F] {N : Nat} (a b : Table F N) : Table F N :=
  fun i => a i * b i

@[simp] theorem hadamard_apply {F : Type*} [Mul F] {N : Nat}
    (a b : Table F N) (i : Fin N) : hadamard a b i = a i * b i := rfl

end CoeffExtract
