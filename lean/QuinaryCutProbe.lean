import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! One explicit GF(5) balanced-cut certificate, from the published AME(12,5) graph.
Source: sjbevins/AME-paper-materials, commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4.
This covers only the cut {0,...,5}|{6,...,11}, not all cuts. -/
namespace AMEProbe.QuinaryCutProbe

def cut : Matrix (Fin 6) (Fin 6) (ZMod 5) :=
  !![4, 4, 4, 4, 4, 3;
      2, 1, 4, 4, 4, 0;
      0, 4, 1, 1, 0, 2;
      3, 2, 4, 4, 3, 2;
      3, 4, 1, 3, 3, 3;
      3, 4, 4, 4, 3, 1]

def inverseCertificate : Matrix (Fin 6) (Fin 6) (ZMod 5) :=
  !![1, 2, 4, 3, 0, 3;
      1, 0, 3, 4, 0, 3;
      1, 0, 0, 1, 2, 4;
      1, 0, 2, 0, 3, 4;
      1, 3, 4, 4, 0, 1;
      2, 0, 1, 4, 0, 0]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem inverse_mul_cut : inverseCertificate * cut = 1 := by
  decide

end AMEProbe.QuinaryCutProbe

#print axioms AMEProbe.QuinaryCutProbe.inverse_mul_cut
