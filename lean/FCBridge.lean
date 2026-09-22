import AMEProbe
import FormalConjectures.OpenQuantumProblems.«35»

/-!
This module uses the unmodified FC definitions at commit 8927a585c5d5.
Its conclusions are conditional: the actual parent construction is not supplied here.
No FC existence theorem (which could contain `sorry`) is used as a premise.
-/

open scoped BigOperators
open OpenQuantumProblem35

namespace AMEProbe.FCBridge

noncomputable def splitAmplitude (ψ : StateVector 11 10)
    (x : Config 5 10) (z : Config 6 10) : ℂ :=
  ψ (combineFirst 5 (by omega) x z)

theorem reduction_eq_fc (ψ : StateVector 11 10) (x y : Config 5 10) :
    AMEProbe.reduction (splitAmplitude ψ) (splitAmplitude ψ) x y =
      reducedDensityFirst 5 (by omega) ψ x y := rfl

/-- A bridge into the exact FC existence predicate; all remaining hypotheses are visible. -/
theorem existsAME_of_reductions (ψ : StateVector 11 10)
    (hnorm : IsNormalized ψ)
    (hred : ∀ (π : Equiv.Perm (Fin 11)) (x y : Config 5 10),
      AMEProbe.reduction (splitAmplitude (permuteState π ψ))
        (splitAmplitude (permuteState π ψ)) x y =
          if x = y then (1 / (10 ^ 5) : ℂ) else 0) :
    ExistsAME 11 10 := by
  refine ⟨ψ, hnorm, ?_⟩
  intro π
  unfold HasMaximallyMixedFirstReduction
  funext x y
  change reducedDensityFirst 5 (by omega) (permuteState π ψ) x y = _
  rw [← reduction_eq_fc, hred]
  rw [maximallyMixed_apply, card_config]
  simp only [Nat.cast_pow, Nat.cast_ofNat, one_div]

end AMEProbe.FCBridge

#print axioms AMEProbe.FCBridge.reduction_eq_fc
#print axioms AMEProbe.FCBridge.existsAME_of_reductions
