import GraphState

/-! The explicit twelve-vertex binary graph with differences {3,5,6,7,9}. -/
namespace AMEProbe.BinaryGraph

def graph : Fin 12 → Fin 12 → ZMod 2 :=
  !![0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1;
    1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1;
    1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1;
    1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1;
    1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0;
    0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1;
    1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0]

theorem symmetric (i j : Fin 12) : graph i j = graph j i := by decide +revert +kernel
theorem diagonal (i : Fin 12) : graph i i = 0 := by decide +revert +kernel

end AMEProbe.BinaryGraph
