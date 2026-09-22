import BinaryLookup
import GraphNormalization

/-! The normalized twelve-qubit five-uniform parent. This is not AME(12,2). -/
open scoped BigOperators
namespace AMEProbe.BinaryParent
open GraphState GraphCharacter BinaryGraph BinaryDirect

theorem every_cut_injective (A : Finset (Fin 12)) (hA : A.card = 5) :
    CutInjective graph A := injective_of_certificate A hA (all_certified A hA)

theorem every_reduction (A : Finset (Fin 12)) (hA : A.card = 5)
    (x y : A → ZMod 2) :
    reduction (fun x z => amplitude12 graph (pasteOn A x z))
      (fun x z => amplitude12 graph (pasteOn A x z)) x y =
        if x = y then (1 / 2 ^ 5 : ℂ) else 0 :=
  binary_reduction graph symmetric diagonal A hA (every_cut_injective A hA) x y

theorem normalized :
    (∑ x : Fin 12 → ZMod 2, amplitude12 graph x * star (amplitude12 graph x)) = 1 :=
  GraphNormalization.normalized12 graph

end AMEProbe.BinaryParent
#print axioms AMEProbe.BinaryParent.every_reduction
#print axioms AMEProbe.BinaryParent.normalized
