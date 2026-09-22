import BinaryGraph

/-! Rectangular left-inverse certificates for the binary five-party cuts. -/
namespace AMEProbe.BinaryDirect
open GraphState GraphCharacter BinaryGraph

def Certificate (A : Finset (Fin 12)) : Prop :=
  ∃ L : Matrix (Fin 5) (Fin 7) (ZMod 2),
    L * executableCutMatrix (k := 5) (t := 7) graph A = 1

theorem injective_of_certificate (A : Finset (Fin 12)) (hA : A.card = 5)
    (h : Certificate A) : CutInjective graph A := by
  obtain ⟨L, hL⟩ := h
  have hAc : Aᶜ.card = 7 := by simp [Finset.card_compl, hA]
  apply cutInjective_of_leftInverse graph A hA hAc L
  rw [← executableCutMatrix_eq]
  exact hL

end AMEProbe.BinaryDirect
