import CoeffExtract.HadamardInterface
import Mathlib.Algebra.Polynomial.Div

open scoped BigOperators
open Polynomial

namespace CoeffExtract

/-- Algebraic DEEP quotient relation:
`P(X) - y = (X-z) Q(X)`. -/
def DeepQuotientRelation
    {F : Type*} [CommRing F]
    (p q : Polynomial F) (z y : F) : Prop :=
  p - Polynomial.C y = (Polynomial.X - Polynomial.C z) * q

/-- Canonical honest DEEP quotient at `z`, using the claimed value `P(z)`. -/
noncomputable def deepQuotient
    {F : Type*} [Field F]
    (p : Polynomial F) (z : F) : Polynomial F :=
  (p - Polynomial.C (p.eval z)) /ₘ
    (Polynomial.X - Polynomial.C z)

/-- The canonical quotient satisfies the DEEP polynomial identity. -/
theorem deepQuotient_spec
    {F : Type*} [Field F]
    (p : Polynomial F) (z : F) :
    DeepQuotientRelation p (deepQuotient p z) z (p.eval z) := by
  unfold DeepQuotientRelation deepQuotient
  symm
  apply (Polynomial.mul_divByMonic_eq_iff_isRoot).2
  simp [Polynomial.IsRoot]

/-- Any exact DEEP quotient identity forces the claimed out-of-domain value. -/
theorem deepQuotientRelation_forces_eval
    {F : Type*} [Field F]
    {p q : Polynomial F} {z y : F}
    (h : DeepQuotientRelation p q z y) :
    p.eval z = y := by
  unfold DeepQuotientRelation at h
  have he := congrArg (fun r : Polynomial F => r.eval z) h
  simp only [Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, sub_self, zero_mul] at he
  exact sub_eq_zero.mp he

/-- Local evaluation formula for a DEEP quotient away from its pole. -/
theorem deepQuotientRelation_eval_of_ne
    {F : Type*} [Field F]
    {p q : Polynomial F} {z y ξ : F}
    (h : DeepQuotientRelation p q z y)
    (hξ : ξ ≠ z) :
    q.eval ξ = (p.eval ξ - y) / (ξ - z) := by
  unfold DeepQuotientRelation at h
  have he := congrArg (fun r : Polynomial F => r.eval ξ) h
  simp only [Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X] at he
  apply (eq_div_iff (sub_ne_zero.mpr hξ)).2
  simpa [mul_comm] using he.symm

/-- The canonical quotient has the verifier-side local formula. -/
theorem eval_deepQuotient_of_ne
    {F : Type*} [Field F]
    (p : Polynomial F) (z ξ : F)
    (hξ : ξ ≠ z) :
    (deepQuotient p z).eval ξ =
      (p.eval ξ - p.eval z) / (ξ - z) := by
  exact deepQuotientRelation_eval_of_ne
    (deepQuotient_spec p z) hξ

/-- Hadamard protocol scalar `y₁ = V_a(γθ)`. -/
noncomputable def hadamardY1
    {F : Type*} [Field F] {N : Nat}
    (γ θ : F) (a : Table F N) : F :=
  (tablePolynomial a).eval (γ * θ)

/-- Hadamard protocol scalar `y₃ = V_c(γ)`. -/
noncomputable def hadamardY3
    {F : Type*} [Field F] {N : Nat}
    (γ : F) (c : Table F N) : F :=
  (tablePolynomial c).eval γ

/-- Honest DEEP quotient binding `V_a` at `γθ`. -/
noncomputable def hadamardDeepQA
    {F : Type*} [Field F] {N : Nat}
    (γ θ : F) (a : Table F N) : Polynomial F :=
  deepQuotient (tablePolynomial a) (γ * θ)

/-- Honest DEEP quotient binding `Q_γ` at `θ`. -/
noncomputable def hadamardDeepQQ
    {F : Type*} [Field F] {N : Nat}
    (γ θ : F) (a : Table F N) : Polynomial F :=
  deepQuotient (scaledTablePolynomial γ a) θ

/-- Honest DEEP quotient binding `V_c` at `γ`. -/
noncomputable def hadamardDeepQC
    {F : Type*} [Field F] {N : Nat}
    (γ : F) (c : Table F N) : Polynomial F :=
  deepQuotient (tablePolynomial c) γ

/-- The first honest Hadamard DEEP relation. -/
theorem hadamardDeepQA_spec
    {F : Type*} [Field F] {N : Nat}
    (γ θ : F) (a : Table F N) :
    DeepQuotientRelation
      (tablePolynomial a)
      (hadamardDeepQA γ θ a)
      (γ * θ)
      (hadamardY1 γ θ a) := by
  unfold hadamardDeepQA hadamardY1
  exact deepQuotient_spec _ _

/-- The same scalar `y₁` is also `Q_γ(θ)`. -/
theorem hadamardY1_eq_scaled_eval
    {F : Type*} [Field F] {N : Nat}
    (γ θ : F) (a : Table F N) :
    hadamardY1 γ θ a =
      (scaledTablePolynomial γ a).eval θ := by
  unfold hadamardY1
  rw [eval_scaledTablePolynomial]

/-- The second honest Hadamard DEEP relation reuses `y₁`. -/
theorem hadamardDeepQQ_spec
    {F : Type*} [Field F] {N : Nat}
    (γ θ : F) (a : Table F N) :
    DeepQuotientRelation
      (scaledTablePolynomial γ a)
      (hadamardDeepQQ γ θ a)
      θ
      (hadamardY1 γ θ a) := by
  unfold hadamardDeepQQ
  rw [hadamardY1_eq_scaled_eval γ θ a]
  exact deepQuotient_spec _ _

/-- The third honest Hadamard DEEP relation binds `V_c(γ)=y₃`. -/
theorem hadamardDeepQC_spec
    {F : Type*} [Field F] {N : Nat}
    (γ : F) (c : Table F N) :
    DeepQuotientRelation
      (tablePolynomial c)
      (hadamardDeepQC γ c)
      γ
      (hadamardY3 γ c) := by
  unfold hadamardDeepQC hadamardY3
  exact deepQuotient_spec _ _

/-- Deterministic DEEP consistency for the two relations sharing `y₁`:
if both polynomial quotient identities hold, they force
`V_a(γθ)=y₁=Q(θ)`. -/
theorem hadamardDeep_link_consistency
    {F : Type*} [Field F] {N : Nat}
    (γ θ y1 : F) (a : Table F N)
    (Q qa qQ : Polynomial F)
    (ha :
      DeepQuotientRelation
        (tablePolynomial a) qa (γ * θ) y1)
    (hQ :
      DeepQuotientRelation Q qQ θ y1) :
    (tablePolynomial a).eval (γ * θ) = y1 ∧
      Q.eval θ = y1 := by
  exact ⟨deepQuotientRelation_forces_eval ha,
    deepQuotientRelation_forces_eval hQ⟩

/-- Deterministic DEEP consistency for the output commitment. -/
theorem hadamardDeep_output_consistency
    {F : Type*} [Field F] {N : Nat}
    (γ y3 : F) (c : Table F N)
    (qc : Polynomial F)
    (hc :
      DeepQuotientRelation
        (tablePolynomial c) qc γ y3) :
    (tablePolynomial c).eval γ = y3 :=
  deepQuotientRelation_forces_eval hc

/-- Honest Hadamard DEEP package: the three quotient identities all hold and
the first two reuse the same scalar `y₁`. -/
theorem hadamardDeep_honest_package
    {F : Type*} [Field F] {N : Nat}
    (γ θ : F) (a c : Table F N) :
    DeepQuotientRelation
        (tablePolynomial a)
        (hadamardDeepQA γ θ a)
        (γ * θ)
        (hadamardY1 γ θ a)
    ∧
    DeepQuotientRelation
        (scaledTablePolynomial γ a)
        (hadamardDeepQQ γ θ a)
        θ
        (hadamardY1 γ θ a)
    ∧
    DeepQuotientRelation
        (tablePolynomial c)
        (hadamardDeepQC γ c)
        γ
        (hadamardY3 γ c) := by
  exact ⟨hadamardDeepQA_spec γ θ a,
    hadamardDeepQQ_spec γ θ a,
    hadamardDeepQC_spec γ c⟩

end CoeffExtract
