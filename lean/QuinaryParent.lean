import QuinaryLookup
import GraphNormalization
import FCValueBridge

/-! A complete AME(12,5) parent, from explicit graph and inverse certificates. -/
open scoped BigOperators
open OpenQuantumProblem35
namespace AMEProbe.QuinaryParent
open GraphState GraphCharacter QuinaryGraph QuinaryDirect

theorem every_cut_injective (A : Finset (Fin 12)) (hA : A.card = 6) :
    CutInjective graph A := injective_of_certificate A hA (all_certified A hA)

theorem every_reduction (A : Finset (Fin 12)) (hA : A.card = 6)
    (x y : A → ZMod 5) :
    reduction (fun x z => amplitude12 graph (pasteOn A x z))
      (fun x z => amplitude12 graph (pasteOn A x z)) x y =
        if x = y then (1 / 5 ^ 6 : ℂ) else 0 :=
  quinary_reduction graph symmetric diagonal A hA (every_cut_injective A hA) x y

/-- This conclusion uses FC's original definition, without assuming a parent theorem. -/
theorem existsAME_12_5 : ExistsAME 12 5 := by
  apply FCValueBridge.existsAME_of_reindexed (ZMod.finEquiv 5).toEquiv (amplitude12 graph)
  · exact GraphNormalization.normalized12 graph
  · intro A hA x y
    change (∑ z : {i : Fin 12 // i ∉ A} → ZMod 5,
      amplitude12 graph (pasteOn A x z) * star (amplitude12 graph (pasteOn A y z))) =
        if x = y then ((5 : ℂ) ^ 6)⁻¹ else 0
    simpa only [reduction, one_div] using every_reduction A hA x y

end AMEProbe.QuinaryParent
#print axioms AMEProbe.QuinaryParent.existsAME_12_5
