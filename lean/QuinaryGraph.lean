import GraphState
import QuinaryCutProbe

/-! Public AME(12,5) graph, with the diagonal set to zero.
Source: sjbevins/AME-paper-materials, commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4.
Graph data license: ../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
open scoped BigOperators
namespace AMEProbe.QuinaryGraph
open GraphCharacter GraphState

def graph : Fin 12 → Fin 12 → ZMod 5 :=
  !![0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 3;
    0, 0, 0, 3, 2, 4, 2, 1, 4, 4, 4, 0;
    0, 0, 0, 2, 1, 0, 0, 4, 1, 1, 0, 2;
    0, 3, 2, 0, 2, 2, 3, 2, 4, 4, 3, 2;
    0, 2, 1, 2, 0, 0, 3, 4, 1, 3, 3, 3;
    0, 4, 0, 2, 0, 0, 3, 4, 4, 4, 3, 1;
    4, 2, 0, 3, 3, 3, 0, 3, 0, 2, 3, 1;
    4, 1, 4, 2, 4, 4, 3, 0, 1, 4, 0, 4;
    4, 4, 1, 4, 1, 4, 0, 1, 0, 4, 4, 4;
    4, 4, 1, 4, 3, 4, 2, 4, 4, 0, 3, 1;
    4, 4, 0, 3, 3, 3, 3, 0, 4, 3, 0, 2;
    3, 0, 2, 2, 3, 1, 1, 4, 4, 1, 2, 0]

theorem symmetric (i j : Fin 12) : graph i j = graph j i := by decide +revert
theorem diagonal (i : Fin 12) : graph i i = 0 := by decide +revert

def sampleSet : Finset (Fin 12) := {6, 7, 8, 9, 10, 11}
theorem sampleCard : sampleSet.card = 6 := by decide
theorem sampleComplCard : sampleSetᶜ.card = 6 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem sampleMatrix : cutMatrix graph sampleSet sampleCard sampleComplCard =
    QuinaryCutProbe.cut := by
  rw [← executableCutMatrix_eq]
  decide

theorem sampleInjective : CutInjective graph sampleSet := by
  apply cutInjective_of_leftInverse graph sampleSet sampleCard sampleComplCard
    QuinaryCutProbe.inverseCertificate
  rw [sampleMatrix]
  exact QuinaryCutProbe.inverse_mul_cut

/-- An actual parent amplitude has the maximally mixed reduction on this cut. -/
theorem sampleReduction (x y : sampleSet → ZMod 5) :
    reduction (fun x z => amplitude12 graph (pasteOn sampleSet x z))
      (fun x z => amplitude12 graph (pasteOn sampleSet x z)) x y =
        if x = y then (1 / 5 ^ 6 : ℂ) else 0 :=
  quinary_reduction graph symmetric diagonal sampleSet sampleCard sampleInjective x y

end AMEProbe.QuinaryGraph
#print axioms AMEProbe.QuinaryGraph.sampleReduction
