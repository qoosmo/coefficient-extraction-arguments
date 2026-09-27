import CoeffExtract.Basic

namespace CoeffExtract

/-- Index reversal `i ↦ N-1-i`, corresponding to polynomial reversal
`P*(X) = X^(N-1) P(X⁻¹)`. -/
def revIndex {N : Nat} (i : Fin N) : Fin N :=
  ⟨N - 1 - i.1, by omega⟩

@[simp] theorem revIndex_val {N : Nat} (i : Fin N) :
    (revIndex i).1 = N - 1 - i.1 := rfl

@[simp] theorem revIndex_involutive {N : Nat} (i : Fin N) :
    revIndex (revIndex i) = i := by
  apply Fin.ext
  simp [revIndex]
  omega

/-- Reversal of a length-`N` coefficient vector. -/
def reverse {F : Type*} {N : Nat} (a : Table F N) : Table F N :=
  fun i => a (revIndex i)

@[simp] theorem reverse_apply {F : Type*} {N : Nat}
    (a : Table F N) (i : Fin N) : reverse a i = a (revIndex i) := rfl

@[simp] theorem reverse_reverse {F : Type*} {N : Nat} (a : Table F N) :
    reverse (reverse a) = a := by
  funext i
  simp [reverse]

theorem reverse_injective {F : Type*} {N : Nat} :
    Function.Injective (reverse : Table F N → Table F N) := by
  intro a b h
  have := congrArg reverse h
  simpa using this

end CoeffExtract
