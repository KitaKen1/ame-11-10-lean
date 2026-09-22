import FinalState

/-! Unconditional proof of the original Formal Conjectures `ExistsAME 11 10`. -/
open scoped BigOperators
open OpenQuantumProblem35
namespace AMEProbe.AME11_10
open GraphCharacter CoupledState FinalState
set_option maxHeartbeats 2000000

def localEquiv : Fin 10 ≃ Local :=
  localTenEquiv.symm.trans
    (Equiv.prodCongr (ZMod.finEquiv 2).toEquiv (ZMod.finEquiv 5).toEquiv)

theorem existsAME_11_10 : ExistsAME 11 10 := by
  apply FCValueBridge.existsAME_of_reindexed localEquiv amplitude
  · exact normalized
  · intro A hA x y
    calc
      (∑ z : {i : Fin 11 // i ∉ A} → Local,
        amplitude (pasteOn A x z) * star (amplitude (pasteOn A y z))) =
          if x = y then (1 / 100000 : ℂ) else 0 := by
            simpa only [reduction] using reduction_formula A hA x y
      _ = if x = y then ((10 : ℂ) ^ (11 / 2))⁻¹ else 0 := by norm_num

end AMEProbe.AME11_10

#print axioms AMEProbe.AME11_10.existsAME_11_10
