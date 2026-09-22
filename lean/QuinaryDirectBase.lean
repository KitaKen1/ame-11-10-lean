import QuinaryGraph

/-! Direct small matrix witnesses, without a packed lookup during multiplication. -/
namespace AMEProbe.QuinaryDirect
open GraphState GraphCharacter QuinaryGraph

def Certificate (A : Finset (Fin 12)) : Prop :=
  ∃ L : Matrix (Fin 6) (Fin 6) (ZMod 5),
    L * executableCutMatrix (k := 6) (t := 6) graph A = 1

theorem injective_of_certificate (A : Finset (Fin 12)) (hA : A.card = 6)
    (h : Certificate A) : CutInjective graph A := by
  obtain ⟨L, hL⟩ := h
  have hAc : Aᶜ.card = 6 := by simp [Finset.card_compl, hA]
  apply cutInjective_of_leftInverse graph A hA hAc L
  rw [← executableCutMatrix_eq]
  exact hL

end AMEProbe.QuinaryDirect
