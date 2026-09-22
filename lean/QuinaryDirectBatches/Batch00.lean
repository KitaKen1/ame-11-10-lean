import QuinaryCoverage

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch00
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def knownCuts : List (Finset (Fin 12)) := [{0, 1, 2, 3, 4, 5}, {0, 1, 2, 3, 4, 6}, {0, 1, 2, 3, 4, 7}, {0, 1, 2, 3, 5, 6}, {0, 1, 2, 3, 5, 7}, {0, 1, 2, 3, 6, 7}, {0, 1, 2, 4, 5, 6}, {0, 1, 2, 4, 5, 7}, {0, 1, 2, 4, 6, 7}, {0, 1, 2, 5, 6, 7}, {0, 1, 3, 4, 5, 6}, {0, 1, 3, 4, 5, 7}, {0, 1, 3, 4, 6, 7}, {0, 1, 3, 5, 6, 7}, {0, 1, 4, 5, 6, 7}, {0, 2, 3, 4, 5, 6}, {0, 2, 3, 4, 5, 7}, {0, 2, 3, 4, 6, 7}, {0, 2, 3, 5, 6, 7}, {0, 2, 4, 5, 6, 7}, {0, 3, 4, 5, 6, 7}, {1, 2, 3, 4, 5, 6}, {1, 2, 3, 4, 5, 7}, {1, 2, 3, 4, 6, 7}, {1, 2, 3, 5, 6, 7}, {1, 2, 4, 5, 6, 7}, {1, 3, 4, 5, 6, 7}, {2, 3, 4, 5, 6, 7}]

theorem covered : ∀ A ∈ batch 0, A ∈ knownCuts := by decide +kernel

theorem certificate_63 : Certificate {0, 1, 2, 3, 4, 5} := by
  refine ⟨!![1, 1, 1, 1, 1, 2;
      2, 0, 0, 0, 3, 0;
      4, 3, 0, 2, 4, 1;
      3, 4, 1, 0, 4, 4;
      0, 0, 2, 3, 0, 0;
      3, 3, 4, 4, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 4, 5} =
      !![4, 2, 0, 3, 3, 3;
      4, 1, 4, 2, 4, 4;
      4, 4, 1, 4, 1, 4;
      4, 4, 1, 4, 3, 4;
      4, 4, 0, 3, 3, 3;
      3, 0, 2, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_95 : Certificate {0, 1, 2, 3, 4, 6} := by
  refine ⟨!![0, 0, 3, 3, 4, 2;
      1, 4, 4, 1, 2, 2;
      4, 3, 3, 3, 3, 4;
      2, 3, 2, 0, 4, 3;
      4, 4, 2, 1, 2, 3;
      1, 1, 0, 2, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 4, 6} =
      !![0, 4, 0, 2, 0, 3;
      4, 1, 4, 2, 4, 3;
      4, 4, 1, 4, 1, 0;
      4, 4, 1, 4, 3, 2;
      4, 4, 0, 3, 3, 3;
      3, 0, 2, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_159 : Certificate {0, 1, 2, 3, 4, 7} := by
  refine ⟨!![1, 4, 0, 2, 0, 4;
      2, 0, 4, 3, 0, 4;
      0, 1, 1, 3, 3, 1;
      3, 1, 0, 0, 4, 0;
      3, 2, 3, 0, 3, 1;
      3, 2, 1, 2, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 4, 7} =
      !![0, 4, 0, 2, 0, 4;
      4, 2, 0, 3, 3, 3;
      4, 4, 1, 4, 1, 1;
      4, 4, 1, 4, 3, 4;
      4, 4, 0, 3, 3, 0;
      3, 0, 2, 2, 3, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_111 : Certificate {0, 1, 2, 3, 5, 6} := by
  refine ⟨!![4, 2, 4, 2, 4, 1;
      3, 2, 3, 0, 4, 3;
      1, 2, 0, 3, 1, 2;
      2, 2, 4, 4, 3, 1;
      2, 1, 3, 2, 0, 2;
      0, 0, 2, 3, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 5, 6} =
      !![0, 2, 1, 2, 0, 3;
      4, 1, 4, 2, 4, 3;
      4, 4, 1, 4, 4, 0;
      4, 4, 1, 4, 4, 2;
      4, 4, 0, 3, 3, 3;
      3, 0, 2, 2, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_175 : Certificate {0, 1, 2, 3, 5, 7} := by
  refine ⟨!![1, 2, 3, 0, 3, 3;
      0, 2, 2, 3, 3, 0;
      3, 2, 3, 2, 0, 4;
      4, 2, 3, 2, 2, 3;
      3, 1, 2, 4, 2, 3;
      0, 0, 3, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 5, 7} =
      !![0, 2, 1, 2, 0, 4;
      4, 2, 0, 3, 3, 3;
      4, 4, 1, 4, 4, 1;
      4, 4, 1, 4, 4, 4;
      4, 4, 0, 3, 3, 0;
      3, 0, 2, 2, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_207 : Certificate {0, 1, 2, 3, 6, 7} := by
  refine ⟨!![4, 3, 3, 4, 3, 2;
      3, 3, 2, 2, 3, 4;
      2, 0, 4, 4, 1, 3;
      2, 3, 3, 1, 2, 2;
      2, 4, 2, 1, 2, 0;
      2, 4, 0, 3, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 6, 7} =
      !![0, 2, 1, 2, 3, 4;
      0, 4, 0, 2, 3, 4;
      4, 4, 1, 4, 0, 1;
      4, 4, 1, 4, 2, 4;
      4, 4, 0, 3, 3, 0;
      3, 0, 2, 2, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_119 : Certificate {0, 1, 2, 4, 5, 6} := by
  refine ⟨!![3, 2, 3, 2, 1, 3;
      4, 1, 3, 3, 1, 1;
      4, 3, 4, 0, 1, 1;
      2, 1, 3, 2, 2, 1;
      4, 1, 0, 2, 1, 3;
      3, 4, 4, 1, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 5, 6} =
      !![0, 3, 2, 2, 2, 3;
      4, 1, 4, 4, 4, 3;
      4, 4, 1, 1, 4, 0;
      4, 4, 1, 3, 4, 2;
      4, 4, 0, 3, 3, 3;
      3, 0, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_183 : Certificate {0, 1, 2, 4, 5, 7} := by
  refine ⟨!![1, 3, 3, 3, 3, 1;
      3, 4, 3, 1, 2, 0;
      1, 2, 4, 4, 4, 3;
      2, 3, 4, 2, 1, 0;
      1, 1, 3, 1, 1, 2;
      2, 3, 2, 4, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 5, 7} =
      !![0, 3, 2, 2, 2, 2;
      4, 2, 0, 3, 3, 3;
      4, 4, 1, 1, 4, 1;
      4, 4, 1, 3, 4, 4;
      4, 4, 0, 3, 3, 0;
      3, 0, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_215 : Certificate {0, 1, 2, 4, 6, 7} := by
  refine ⟨!![2, 3, 1, 4, 3, 3;
      1, 4, 2, 4, 2, 1;
      0, 2, 1, 3, 4, 1;
      2, 1, 4, 2, 4, 0;
      4, 3, 2, 4, 3, 3;
      1, 4, 4, 3, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 6, 7} =
      !![0, 3, 2, 2, 3, 2;
      0, 4, 0, 0, 3, 4;
      4, 4, 1, 1, 0, 1;
      4, 4, 1, 3, 2, 4;
      4, 4, 0, 3, 3, 0;
      3, 0, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_231 : Certificate {0, 1, 2, 5, 6, 7} := by
  refine ⟨!![0, 2, 0, 3, 1, 0;
      0, 1, 4, 1, 1, 2;
      2, 3, 2, 4, 1, 4;
      1, 3, 4, 0, 0, 3;
      4, 3, 4, 3, 1, 1;
      4, 3, 2, 0, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 6, 7} =
      !![0, 3, 2, 2, 3, 2;
      0, 2, 1, 0, 3, 4;
      4, 4, 1, 4, 0, 1;
      4, 4, 1, 4, 2, 4;
      4, 4, 0, 3, 3, 0;
      3, 0, 2, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_123 : Certificate {0, 1, 3, 4, 5, 6} := by
  refine ⟨!![2, 2, 3, 3, 1, 0;
      2, 4, 2, 4, 2, 4;
      2, 1, 3, 1, 2, 4;
      2, 3, 4, 3, 1, 2;
      1, 1, 0, 0, 1, 4;
      3, 2, 3, 0, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 5, 6} =
      !![0, 0, 2, 1, 0, 0;
      4, 1, 2, 4, 4, 3;
      4, 4, 4, 1, 4, 0;
      4, 4, 4, 3, 4, 2;
      4, 4, 3, 3, 3, 3;
      3, 0, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_187 : Certificate {0, 1, 3, 4, 5, 7} := by
  refine ⟨!![1, 1, 2, 1, 4, 3;
      2, 3, 2, 3, 0, 1;
      3, 0, 4, 1, 0, 0;
      3, 4, 0, 0, 3, 4;
      0, 4, 4, 2, 2, 4;
      3, 4, 3, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 5, 7} =
      !![0, 0, 2, 1, 0, 4;
      4, 2, 3, 3, 3, 3;
      4, 4, 4, 1, 4, 1;
      4, 4, 4, 3, 4, 4;
      4, 4, 3, 3, 3, 0;
      3, 0, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_219 : Certificate {0, 1, 3, 4, 6, 7} := by
  refine ⟨!![2, 4, 1, 1, 4, 4;
      1, 1, 4, 1, 3, 1;
      0, 3, 4, 2, 1, 4;
      2, 1, 1, 0, 3, 3;
      4, 1, 0, 2, 2, 3;
      1, 2, 4, 4, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 6, 7} =
      !![0, 0, 2, 1, 0, 4;
      0, 4, 2, 0, 3, 4;
      4, 4, 4, 1, 0, 1;
      4, 4, 4, 3, 2, 4;
      4, 4, 3, 3, 3, 0;
      3, 0, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_235 : Certificate {0, 1, 3, 5, 6, 7} := by
  refine ⟨!![4, 0, 2, 1, 2, 2;
      4, 4, 1, 4, 2, 4;
      4, 3, 2, 3, 1, 2;
      0, 4, 3, 3, 2, 1;
      2, 1, 1, 4, 2, 4;
      2, 1, 4, 1, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 6, 7} =
      !![0, 0, 2, 0, 0, 4;
      0, 2, 2, 0, 3, 4;
      4, 4, 4, 4, 0, 1;
      4, 4, 4, 4, 2, 4;
      4, 4, 3, 3, 3, 0;
      3, 0, 2, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_243 : Certificate {0, 1, 4, 5, 6, 7} := by
  refine ⟨!![0, 2, 2, 2, 2, 4;
      0, 1, 0, 3, 4, 4;
      4, 3, 0, 4, 0, 3;
      2, 3, 2, 3, 4, 3;
      4, 0, 2, 3, 0, 0;
      3, 3, 0, 4, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 6, 7} =
      !![0, 0, 1, 0, 0, 4;
      0, 3, 2, 2, 3, 2;
      4, 4, 1, 4, 0, 1;
      4, 4, 3, 4, 2, 4;
      4, 4, 3, 3, 3, 0;
      3, 0, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_125 : Certificate {0, 2, 3, 4, 5, 6} := by
  refine ⟨!![4, 0, 4, 3, 4, 4;
      4, 2, 3, 4, 0, 3;
      1, 0, 3, 3, 0, 2;
      3, 3, 3, 2, 4, 4;
      2, 0, 3, 0, 0, 1;
      2, 2, 4, 1, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 5, 6} =
      !![0, 0, 3, 2, 4, 2;
      4, 4, 2, 4, 4, 3;
      4, 1, 4, 1, 4, 0;
      4, 1, 4, 3, 4, 2;
      4, 0, 3, 3, 3, 3;
      3, 2, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_189 : Certificate {0, 2, 3, 4, 5, 7} := by
  refine ⟨!![4, 3, 4, 3, 1, 4;
      2, 3, 4, 3, 1, 2;
      1, 2, 3, 3, 3, 2;
      0, 2, 2, 3, 3, 0;
      2, 2, 3, 0, 3, 1;
      0, 2, 0, 0, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 5, 7} =
      !![0, 0, 3, 2, 4, 1;
      4, 0, 3, 3, 3, 3;
      4, 1, 4, 1, 4, 1;
      4, 1, 4, 3, 4, 4;
      4, 0, 3, 3, 3, 0;
      3, 2, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_221 : Certificate {0, 2, 3, 4, 6, 7} := by
  refine ⟨!![1, 0, 2, 3, 4, 0;
      4, 2, 1, 1, 4, 2;
      4, 0, 0, 3, 0, 1;
      3, 3, 0, 0, 0, 0;
      0, 2, 4, 3, 0, 4;
      3, 0, 2, 0, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 6, 7} =
      !![0, 0, 3, 2, 2, 1;
      0, 0, 2, 0, 3, 4;
      4, 1, 4, 1, 0, 1;
      4, 1, 4, 3, 2, 4;
      4, 0, 3, 3, 3, 0;
      3, 2, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_237 : Certificate {0, 2, 3, 5, 6, 7} := by
  refine ⟨!![0, 1, 1, 2, 0, 3;
      2, 0, 1, 1, 4, 2;
      0, 4, 1, 4, 4, 3;
      1, 4, 1, 1, 4, 2;
      4, 4, 0, 4, 4, 1;
      4, 4, 3, 1, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 6, 7} =
      !![0, 0, 3, 4, 2, 1;
      0, 1, 2, 0, 3, 4;
      4, 1, 4, 4, 0, 1;
      4, 1, 4, 4, 2, 4;
      4, 0, 3, 3, 3, 0;
      3, 2, 2, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_245 : Certificate {0, 2, 4, 5, 6, 7} := by
  refine ⟨!![0, 0, 2, 1, 4, 1;
      0, 2, 0, 1, 3, 3;
      2, 3, 1, 0, 1, 4;
      1, 0, 0, 2, 0, 4;
      2, 2, 3, 0, 4, 4;
      4, 0, 2, 2, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 6, 7} =
      !![0, 0, 2, 4, 2, 1;
      0, 2, 2, 2, 3, 2;
      4, 1, 1, 4, 0, 1;
      4, 1, 3, 4, 2, 4;
      4, 0, 3, 3, 3, 0;
      3, 2, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_249 : Certificate {0, 3, 4, 5, 6, 7} := by
  refine ⟨!![3, 4, 1, 0, 3, 0;
      2, 1, 1, 1, 1, 1;
      2, 0, 1, 1, 4, 2;
      3, 1, 1, 3, 1, 0;
      4, 1, 4, 0, 2, 2;
      1, 1, 3, 3, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 6, 7} =
      !![0, 3, 2, 4, 2, 1;
      0, 2, 1, 0, 0, 4;
      4, 4, 1, 4, 0, 1;
      4, 4, 3, 4, 2, 4;
      4, 3, 3, 3, 3, 0;
      3, 2, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_126 : Certificate {1, 2, 3, 4, 5, 6} := by
  refine ⟨!![4, 3, 3, 3, 1, 1;
      1, 4, 1, 3, 0, 3;
      3, 1, 3, 2, 1, 3;
      1, 0, 2, 3, 0, 0;
      0, 0, 1, 1, 3, 4;
      4, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 5, 6} =
      !![0, 0, 0, 0, 0, 4;
      1, 4, 2, 4, 4, 3;
      4, 1, 4, 1, 4, 0;
      4, 1, 4, 3, 4, 2;
      4, 0, 3, 3, 3, 3;
      0, 2, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_190 : Certificate {1, 2, 3, 4, 5, 7} := by
  refine ⟨!![1, 2, 0, 0, 3, 0;
      1, 1, 2, 4, 1, 0;
      2, 4, 2, 1, 0, 1;
      4, 0, 2, 3, 0, 0;
      1, 0, 1, 1, 3, 4;
      4, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 5, 7} =
      !![0, 0, 0, 0, 0, 4;
      2, 0, 3, 3, 3, 3;
      4, 1, 4, 1, 4, 1;
      4, 1, 4, 3, 4, 4;
      4, 0, 3, 3, 3, 0;
      0, 2, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_222 : Certificate {1, 2, 3, 4, 6, 7} := by
  refine ⟨!![1, 2, 0, 4, 3, 3;
      2, 1, 3, 2, 4, 3;
      2, 4, 2, 4, 0, 2;
      1, 0, 4, 0, 1, 3;
      4, 0, 4, 4, 2, 1;
      0, 0, 1, 1, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 6, 7} =
      !![0, 0, 0, 0, 4, 4;
      4, 0, 2, 0, 3, 4;
      4, 1, 4, 1, 0, 1;
      4, 1, 4, 3, 2, 4;
      4, 0, 3, 3, 3, 0;
      0, 2, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_238 : Certificate {1, 2, 3, 5, 6, 7} := by
  refine ⟨!![0, 4, 4, 3, 0, 2;
      1, 2, 3, 4, 2, 1;
      0, 3, 0, 2, 4, 0;
      3, 0, 2, 0, 3, 4;
      2, 0, 1, 4, 0, 0;
      2, 0, 4, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 6, 7} =
      !![0, 0, 0, 0, 4, 4;
      2, 1, 2, 0, 3, 4;
      4, 1, 4, 4, 0, 1;
      4, 1, 4, 4, 2, 4;
      4, 0, 3, 3, 3, 0;
      0, 2, 2, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_246 : Certificate {1, 2, 4, 5, 6, 7} := by
  refine ⟨!![0, 0, 4, 2, 3, 2;
      0, 2, 2, 2, 2, 4;
      3, 4, 3, 2, 2, 1;
      4, 3, 3, 4, 2, 1;
      3, 3, 2, 3, 4, 2;
      1, 2, 3, 2, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 6, 7} =
      !![0, 0, 0, 0, 4, 4;
      3, 2, 2, 2, 3, 2;
      4, 1, 1, 4, 0, 1;
      4, 1, 3, 4, 2, 4;
      4, 0, 3, 3, 3, 0;
      0, 2, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_250 : Certificate {1, 3, 4, 5, 6, 7} := by
  refine ⟨!![3, 1, 1, 4, 4, 3;
      1, 2, 4, 4, 2, 2;
      0, 4, 2, 1, 2, 2;
      3, 3, 1, 2, 2, 3;
      2, 3, 0, 1, 4, 4;
      2, 2, 0, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 6, 7} =
      !![0, 0, 0, 0, 4, 4;
      0, 2, 1, 0, 0, 4;
      4, 4, 1, 4, 0, 1;
      4, 4, 3, 4, 2, 4;
      4, 3, 3, 3, 3, 0;
      0, 2, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_252 : Certificate {2, 3, 4, 5, 6, 7} := by
  refine ⟨!![4, 4, 1, 2, 1, 4;
      0, 0, 2, 1, 4, 1;
      1, 3, 0, 4, 3, 3;
      0, 1, 2, 3, 4, 0;
      4, 1, 1, 2, 1, 1;
      0, 4, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 6, 7} =
      !![0, 0, 0, 0, 4, 4;
      0, 3, 2, 4, 2, 1;
      1, 4, 1, 4, 0, 1;
      1, 4, 3, 4, 2, 4;
      0, 3, 3, 3, 3, 0;
      2, 2, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem known_certified : ∀ A ∈ knownCuts, Certificate A := by
  intro A h
  simp only [knownCuts, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact certificate_63
  · exact certificate_95
  · exact certificate_159
  · exact certificate_111
  · exact certificate_175
  · exact certificate_207
  · exact certificate_119
  · exact certificate_183
  · exact certificate_215
  · exact certificate_231
  · exact certificate_123
  · exact certificate_187
  · exact certificate_219
  · exact certificate_235
  · exact certificate_243
  · exact certificate_125
  · exact certificate_189
  · exact certificate_221
  · exact certificate_237
  · exact certificate_245
  · exact certificate_249
  · exact certificate_126
  · exact certificate_190
  · exact certificate_222
  · exact certificate_238
  · exact certificate_246
  · exact certificate_250
  · exact certificate_252

theorem checked : ∀ A ∈ batch 0, Certificate A := by
  intro A h
  exact known_certified A (covered A h)

end AMEProbe.QuinaryDirect.Batch00
#print axioms AMEProbe.QuinaryDirect.Batch00.checked
