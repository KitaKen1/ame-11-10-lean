import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch04
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_1055 : Certificate {0, 1, 2, 3, 4, 10} := by
  refine ⟨!![4, 2, 1, 4, 2, 0;
      0, 3, 1, 3, 3, 0;
      4, 1, 4, 1, 1, 4;
      1, 2, 4, 3, 4, 1;
      4, 4, 3, 4, 3, 3;
      3, 3, 1, 4, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 4, 10} =
      !![0, 4, 0, 2, 0, 3;
      4, 2, 0, 3, 3, 3;
      4, 1, 4, 2, 4, 0;
      4, 4, 1, 4, 1, 4;
      4, 4, 1, 4, 3, 3;
      3, 0, 2, 2, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1071 : Certificate {0, 1, 2, 3, 5, 10} := by
  refine ⟨!![2, 3, 4, 0, 4, 4;
      1, 3, 4, 3, 3, 1;
      3, 2, 0, 2, 3, 4;
      3, 1, 1, 2, 2, 2;
      2, 0, 1, 0, 0, 2;
      0, 0, 0, 1, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 5, 10} =
      !![0, 2, 1, 2, 0, 3;
      4, 2, 0, 3, 3, 3;
      4, 1, 4, 2, 4, 0;
      4, 4, 1, 4, 4, 4;
      4, 4, 1, 4, 4, 3;
      3, 0, 2, 2, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1079 : Certificate {0, 1, 2, 4, 5, 10} := by
  refine ⟨!![0, 4, 0, 2, 1, 1;
      2, 2, 1, 1, 4, 1;
      2, 2, 3, 2, 1, 1;
      1, 3, 2, 1, 0, 2;
      4, 3, 0, 1, 2, 2;
      2, 1, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 5, 10} =
      !![0, 3, 2, 2, 2, 3;
      4, 2, 0, 3, 3, 3;
      4, 1, 4, 4, 4, 0;
      4, 4, 1, 1, 4, 4;
      4, 4, 1, 3, 4, 3;
      3, 0, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1083 : Certificate {0, 1, 3, 4, 5, 10} := by
  refine ⟨!![1, 2, 2, 2, 4, 2;
      4, 2, 1, 4, 0, 4;
      4, 2, 3, 0, 2, 4;
      3, 1, 4, 0, 1, 2;
      3, 3, 0, 2, 4, 3;
      1, 2, 3, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 5, 10} =
      !![0, 0, 2, 1, 0, 0;
      4, 2, 3, 3, 3, 3;
      4, 1, 2, 4, 4, 0;
      4, 4, 4, 1, 4, 4;
      4, 4, 4, 3, 4, 3;
      3, 0, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1085 : Certificate {0, 2, 3, 4, 5, 10} := by
  refine ⟨!![3, 1, 4, 2, 0, 1;
      3, 2, 1, 1, 1, 0;
      2, 3, 1, 0, 1, 0;
      3, 4, 3, 3, 2, 4;
      0, 4, 3, 4, 4, 0;
      1, 3, 1, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 5, 10} =
      !![0, 0, 3, 2, 4, 4;
      4, 0, 3, 3, 3, 3;
      4, 4, 2, 4, 4, 0;
      4, 1, 4, 1, 4, 4;
      4, 1, 4, 3, 4, 3;
      3, 2, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1086 : Certificate {1, 2, 3, 4, 5, 10} := by
  refine ⟨!![4, 4, 2, 2, 2, 4;
      4, 0, 4, 1, 3, 3;
      0, 4, 0, 2, 1, 1;
      2, 0, 0, 2, 3, 0;
      3, 2, 2, 3, 3, 3;
      4, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 5, 10} =
      !![0, 0, 0, 0, 0, 4;
      2, 0, 3, 3, 3, 3;
      1, 4, 2, 4, 4, 0;
      4, 1, 4, 1, 4, 4;
      4, 1, 4, 3, 4, 3;
      0, 2, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1103 : Certificate {0, 1, 2, 3, 6, 10} := by
  refine ⟨!![2, 2, 3, 2, 3, 3;
      2, 2, 1, 0, 2, 1;
      0, 3, 2, 0, 4, 2;
      2, 4, 1, 1, 0, 4;
      2, 0, 1, 0, 0, 2;
      4, 0, 2, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 6, 10} =
      !![0, 2, 1, 2, 3, 3;
      0, 4, 0, 2, 3, 3;
      4, 1, 4, 2, 3, 0;
      4, 4, 1, 4, 0, 4;
      4, 4, 1, 4, 2, 3;
      3, 0, 2, 2, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1111 : Certificate {0, 1, 2, 4, 6, 10} := by
  refine ⟨!![0, 3, 2, 1, 3, 4;
      4, 2, 4, 0, 3, 4;
      4, 2, 1, 1, 0, 4;
      1, 1, 1, 4, 4, 3;
      2, 3, 2, 2, 3, 4;
      1, 3, 1, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 6, 10} =
      !![0, 3, 2, 2, 3, 3;
      0, 4, 0, 0, 3, 3;
      4, 1, 4, 4, 3, 0;
      4, 4, 1, 1, 0, 4;
      4, 4, 1, 3, 2, 3;
      3, 0, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1115 : Certificate {0, 1, 3, 4, 6, 10} := by
  refine ⟨!![3, 4, 1, 1, 1, 3;
      3, 1, 2, 4, 1, 4;
      3, 1, 4, 0, 3, 4;
      0, 3, 2, 0, 4, 2;
      3, 3, 3, 4, 1, 1;
      1, 2, 0, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 6, 10} =
      !![0, 0, 2, 1, 0, 0;
      0, 4, 2, 0, 3, 3;
      4, 1, 2, 4, 3, 0;
      4, 4, 4, 1, 0, 4;
      4, 4, 4, 3, 2, 3;
      3, 0, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1117 : Certificate {0, 2, 3, 4, 6, 10} := by
  refine ⟨!![2, 3, 2, 3, 1, 4;
      3, 0, 2, 4, 4, 0;
      2, 0, 0, 2, 3, 0;
      2, 3, 0, 1, 0, 2;
      1, 2, 0, 3, 3, 2;
      1, 0, 0, 4, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 6, 10} =
      !![0, 0, 3, 2, 2, 4;
      0, 0, 2, 0, 3, 3;
      4, 4, 2, 4, 3, 0;
      4, 1, 4, 1, 0, 4;
      4, 1, 4, 3, 2, 3;
      3, 2, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1118 : Certificate {1, 2, 3, 4, 6, 10} := by
  refine ⟨!![2, 3, 1, 3, 4, 2;
      2, 1, 0, 0, 4, 1;
      0, 2, 3, 4, 2, 1;
      3, 2, 2, 0, 0, 1;
      1, 2, 2, 3, 2, 1;
      3, 3, 3, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 6, 10} =
      !![0, 0, 0, 0, 4, 4;
      4, 0, 2, 0, 3, 3;
      1, 4, 2, 4, 3, 0;
      4, 1, 4, 1, 0, 4;
      4, 1, 4, 3, 2, 3;
      0, 2, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1127 : Certificate {0, 1, 2, 5, 6, 10} := by
  refine ⟨!![2, 0, 4, 4, 1, 0;
      1, 3, 0, 2, 1, 1;
      1, 3, 2, 3, 3, 1;
      2, 4, 4, 0, 3, 4;
      3, 3, 2, 0, 2, 3;
      1, 1, 4, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 6, 10} =
      !![0, 3, 2, 2, 3, 3;
      0, 2, 1, 0, 3, 3;
      4, 1, 4, 4, 3, 0;
      4, 4, 1, 4, 0, 4;
      4, 4, 1, 4, 2, 3;
      3, 0, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1131 : Certificate {0, 1, 3, 5, 6, 10} := by
  refine ⟨!![2, 4, 0, 3, 0, 3;
      3, 0, 3, 4, 3, 0;
      3, 0, 0, 0, 0, 0;
      3, 3, 0, 4, 2, 2;
      2, 4, 1, 1, 3, 0;
      4, 3, 2, 3, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 6, 10} =
      !![0, 0, 2, 0, 0, 0;
      0, 2, 2, 0, 3, 3;
      4, 1, 2, 4, 3, 0;
      4, 4, 4, 4, 0, 4;
      4, 4, 4, 4, 2, 3;
      3, 0, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1133 : Certificate {0, 2, 3, 5, 6, 10} := by
  refine ⟨!![3, 3, 1, 1, 4, 4;
      1, 3, 1, 3, 2, 2;
      4, 2, 1, 3, 0, 3;
      1, 1, 3, 3, 1, 4;
      4, 1, 3, 2, 4, 3;
      3, 2, 1, 0, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 6, 10} =
      !![0, 0, 3, 4, 2, 4;
      0, 1, 2, 0, 3, 3;
      4, 4, 2, 4, 3, 0;
      4, 1, 4, 4, 0, 4;
      4, 1, 4, 4, 2, 3;
      3, 2, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1134 : Certificate {1, 2, 3, 5, 6, 10} := by
  refine ⟨!![4, 4, 0, 2, 0, 2;
      3, 0, 4, 0, 4, 3;
      1, 4, 3, 3, 3, 4;
      2, 2, 1, 2, 3, 2;
      3, 0, 0, 3, 2, 0;
      1, 0, 0, 2, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 6, 10} =
      !![0, 0, 0, 0, 4, 4;
      2, 1, 2, 0, 3, 3;
      1, 4, 2, 4, 3, 0;
      4, 1, 4, 4, 0, 4;
      4, 1, 4, 4, 2, 3;
      0, 2, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1139 : Certificate {0, 1, 4, 5, 6, 10} := by
  refine ⟨!![3, 2, 4, 4, 1, 0;
      0, 0, 3, 4, 3, 0;
      1, 0, 0, 0, 0, 0;
      4, 4, 3, 1, 4, 1;
      1, 2, 0, 2, 4, 2;
      4, 4, 0, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 6, 10} =
      !![0, 0, 1, 0, 0, 0;
      0, 3, 2, 2, 3, 3;
      4, 1, 4, 4, 3, 0;
      4, 4, 1, 4, 0, 4;
      4, 4, 3, 4, 2, 3;
      3, 0, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1141 : Certificate {0, 2, 4, 5, 6, 10} := by
  refine ⟨!![3, 4, 1, 4, 3, 3;
      0, 0, 2, 1, 2, 0;
      1, 4, 4, 0, 4, 1;
      4, 0, 0, 4, 1, 0;
      1, 1, 1, 3, 0, 3;
      4, 0, 0, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 6, 10} =
      !![0, 0, 2, 4, 2, 4;
      0, 2, 2, 2, 3, 3;
      4, 4, 4, 4, 3, 0;
      4, 1, 1, 4, 0, 4;
      4, 1, 3, 4, 2, 3;
      3, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1142 : Certificate {1, 2, 4, 5, 6, 10} := by
  refine ⟨!![3, 3, 3, 0, 1, 3;
      3, 3, 0, 1, 3, 3;
      0, 1, 2, 2, 3, 0;
      4, 2, 1, 2, 0, 0;
      3, 1, 2, 0, 0, 0;
      1, 4, 3, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 6, 10} =
      !![0, 0, 0, 0, 4, 4;
      3, 2, 2, 2, 3, 3;
      1, 4, 4, 4, 3, 0;
      4, 1, 1, 4, 0, 4;
      4, 1, 3, 4, 2, 3;
      0, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1145 : Certificate {0, 3, 4, 5, 6, 10} := by
  refine ⟨!![2, 1, 1, 1, 3, 2;
      0, 0, 2, 1, 2, 0;
      0, 1, 1, 3, 1, 0;
      4, 0, 1, 2, 2, 0;
      2, 4, 0, 3, 4, 4;
      4, 0, 2, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 6, 10} =
      !![0, 3, 2, 4, 2, 4;
      0, 2, 1, 0, 0, 0;
      4, 2, 4, 4, 3, 0;
      4, 4, 1, 4, 0, 4;
      4, 4, 3, 4, 2, 3;
      3, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1146 : Certificate {1, 3, 4, 5, 6, 10} := by
  refine ⟨!![3, 3, 2, 4, 2, 3;
      3, 3, 4, 0, 4, 3;
      4, 0, 2, 0, 2, 4;
      1, 4, 3, 3, 0, 2;
      2, 0, 2, 3, 4, 4;
      2, 0, 3, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 6, 10} =
      !![0, 0, 0, 0, 4, 4;
      0, 2, 1, 0, 0, 0;
      1, 2, 4, 4, 3, 0;
      4, 4, 1, 4, 0, 4;
      4, 4, 3, 4, 2, 3;
      0, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1148 : Certificate {2, 3, 4, 5, 6, 10} := by
  refine ⟨!![2, 1, 1, 4, 2, 3;
      3, 4, 1, 2, 0, 2;
      3, 2, 4, 3, 1, 0;
      4, 1, 3, 0, 1, 1;
      1, 2, 4, 1, 3, 0;
      3, 3, 1, 4, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 6, 10} =
      !![0, 0, 0, 0, 4, 4;
      0, 3, 2, 4, 2, 4;
      4, 2, 4, 4, 3, 0;
      1, 4, 1, 4, 0, 4;
      1, 4, 3, 4, 2, 3;
      2, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1167 : Certificate {0, 1, 2, 3, 7, 10} := by
  refine ⟨!![4, 0, 3, 0, 4, 1;
      4, 1, 4, 4, 0, 1;
      4, 1, 3, 3, 0, 2;
      0, 4, 0, 1, 0, 2;
      3, 3, 3, 3, 1, 4;
      4, 4, 4, 0, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 7, 10} =
      !![0, 2, 1, 2, 4, 3;
      0, 4, 0, 2, 4, 3;
      4, 2, 0, 3, 3, 3;
      4, 4, 1, 4, 1, 4;
      4, 4, 1, 4, 4, 3;
      3, 0, 2, 2, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1175 : Certificate {0, 1, 2, 4, 7, 10} := by
  refine ⟨!![3, 0, 0, 4, 0, 0;
      3, 1, 1, 3, 1, 0;
      3, 3, 0, 0, 1, 2;
      0, 2, 0, 3, 0, 1;
      1, 0, 2, 4, 3, 3;
      3, 4, 1, 4, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 7, 10} =
      !![0, 3, 2, 2, 2, 3;
      0, 4, 0, 0, 4, 3;
      4, 2, 0, 3, 3, 3;
      4, 4, 1, 1, 1, 4;
      4, 4, 1, 3, 4, 3;
      3, 0, 2, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1179 : Certificate {0, 1, 3, 4, 7, 10} := by
  refine ⟨!![3, 3, 1, 2, 2, 2;
      3, 4, 2, 1, 3, 2;
      1, 2, 2, 1, 1, 3;
      2, 1, 4, 0, 2, 2;
      3, 0, 3, 2, 4, 3;
      3, 2, 2, 2, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 7, 10} =
      !![0, 0, 2, 1, 4, 0;
      0, 4, 2, 0, 4, 3;
      4, 2, 3, 3, 3, 3;
      4, 4, 4, 1, 1, 4;
      4, 4, 4, 3, 4, 3;
      3, 0, 2, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1181 : Certificate {0, 2, 3, 4, 7, 10} := by
  refine ⟨!![0, 4, 4, 1, 4, 0;
      3, 0, 4, 3, 3, 0;
      4, 4, 0, 3, 4, 4;
      3, 0, 0, 4, 3, 4;
      3, 1, 0, 4, 4, 1;
      0, 3, 0, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 7, 10} =
      !![0, 0, 3, 2, 1, 4;
      0, 0, 2, 0, 4, 3;
      4, 0, 3, 3, 3, 3;
      4, 1, 4, 1, 1, 4;
      4, 1, 4, 3, 4, 3;
      3, 2, 2, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1182 : Certificate {1, 2, 3, 4, 7, 10} := by
  refine ⟨!![0, 1, 1, 4, 1, 0;
      4, 4, 2, 0, 0, 3;
      2, 3, 1, 2, 2, 3;
      4, 3, 2, 2, 4, 2;
      4, 1, 4, 0, 2, 4;
      0, 4, 1, 0, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 7, 10} =
      !![0, 0, 0, 0, 4, 4;
      4, 0, 2, 0, 4, 3;
      2, 0, 3, 3, 3, 3;
      4, 1, 4, 1, 1, 4;
      4, 1, 4, 3, 4, 3;
      0, 2, 2, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1191 : Certificate {0, 1, 2, 5, 7, 10} := by
  refine ⟨!![2, 3, 1, 1, 3, 2;
      0, 4, 4, 0, 0, 3;
      3, 0, 0, 3, 1, 3;
      3, 1, 2, 4, 1, 4;
      4, 1, 4, 3, 4, 2;
      2, 3, 2, 0, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 7, 10} =
      !![0, 3, 2, 2, 2, 3;
      0, 2, 1, 0, 4, 3;
      4, 2, 0, 3, 3, 3;
      4, 4, 1, 4, 1, 4;
      4, 4, 1, 4, 4, 3;
      3, 0, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1195 : Certificate {0, 1, 3, 5, 7, 10} := by
  refine ⟨!![2, 0, 4, 2, 1, 1;
      2, 1, 2, 3, 2, 4;
      3, 3, 2, 2, 3, 4;
      3, 4, 4, 3, 3, 0;
      0, 1, 4, 4, 1, 3;
      0, 3, 2, 3, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 7, 10} =
      !![0, 0, 2, 0, 4, 0;
      0, 2, 2, 0, 4, 3;
      4, 2, 3, 3, 3, 3;
      4, 4, 4, 4, 1, 4;
      4, 4, 4, 4, 4, 3;
      3, 0, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1197 : Certificate {0, 2, 3, 5, 7, 10} := by
  refine ⟨!![3, 4, 3, 4, 2, 0;
      2, 0, 4, 0, 2, 2;
      0, 4, 4, 0, 0, 3;
      2, 0, 0, 1, 2, 1;
      1, 1, 1, 4, 2, 4;
      3, 3, 3, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 7, 10} =
      !![0, 0, 3, 4, 1, 4;
      0, 1, 2, 0, 4, 3;
      4, 0, 3, 3, 3, 3;
      4, 1, 4, 4, 1, 4;
      4, 1, 4, 4, 4, 3;
      3, 2, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1198 : Certificate {1, 2, 3, 5, 7, 10} := by
  refine ⟨!![2, 4, 0, 0, 2, 2;
      2, 3, 2, 4, 1, 4;
      3, 0, 4, 0, 3, 1;
      0, 4, 3, 0, 4, 1;
      1, 0, 0, 1, 4, 0;
      3, 0, 0, 4, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 7, 10} =
      !![0, 0, 0, 0, 4, 4;
      2, 1, 2, 0, 4, 3;
      2, 0, 3, 3, 3, 3;
      4, 1, 4, 4, 1, 4;
      4, 1, 4, 4, 4, 3;
      0, 2, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1203 : Certificate {0, 1, 4, 5, 7, 10} := by
  refine ⟨!![2, 4, 4, 1, 4, 0;
      1, 0, 3, 4, 1, 1;
      0, 3, 0, 3, 1, 3;
      4, 2, 3, 4, 3, 0;
      4, 3, 0, 3, 1, 3;
      2, 0, 0, 1, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 7, 10} =
      !![0, 0, 1, 0, 4, 0;
      0, 3, 2, 2, 2, 3;
      4, 2, 3, 3, 3, 3;
      4, 4, 1, 4, 1, 4;
      4, 4, 3, 4, 4, 3;
      3, 0, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1205 : Certificate {0, 2, 4, 5, 7, 10} := by
  refine ⟨!![4, 1, 1, 0, 0, 4;
      4, 2, 3, 2, 3, 1;
      1, 1, 2, 1, 3, 2;
      3, 1, 2, 2, 0, 3;
      3, 2, 4, 1, 3, 1;
      1, 3, 1, 1, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 7, 10} =
      !![0, 0, 2, 4, 1, 4;
      0, 2, 2, 2, 2, 3;
      4, 0, 3, 3, 3, 3;
      4, 1, 1, 4, 1, 4;
      4, 1, 3, 4, 4, 3;
      3, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1206 : Certificate {1, 2, 4, 5, 7, 10} := by
  refine ⟨!![1, 4, 4, 2, 2, 4;
      3, 3, 4, 3, 4, 4;
      2, 0, 1, 0, 2, 4;
      0, 4, 0, 2, 0, 0;
      0, 0, 2, 1, 3, 3;
      4, 0, 3, 4, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 7, 10} =
      !![0, 0, 0, 0, 4, 4;
      3, 2, 2, 2, 2, 3;
      2, 0, 3, 3, 3, 3;
      4, 1, 1, 4, 1, 4;
      4, 1, 3, 4, 4, 3;
      0, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1209 : Certificate {0, 3, 4, 5, 7, 10} := by
  refine ⟨!![2, 2, 3, 2, 3, 3;
      0, 2, 1, 3, 2, 2;
      4, 0, 3, 0, 4, 4;
      1, 0, 3, 1, 1, 0;
      4, 3, 0, 1, 3, 3;
      0, 4, 1, 4, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 7, 10} =
      !![0, 3, 2, 4, 1, 4;
      0, 2, 1, 0, 4, 0;
      4, 3, 3, 3, 3, 3;
      4, 4, 1, 4, 1, 4;
      4, 4, 3, 4, 4, 3;
      3, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1210 : Certificate {1, 3, 4, 5, 7, 10} := by
  refine ⟨!![1, 3, 0, 1, 3, 4;
      3, 1, 1, 1, 1, 4;
      0, 1, 2, 1, 3, 3;
      4, 1, 4, 4, 4, 2;
      1, 2, 4, 3, 0, 1;
      3, 3, 1, 2, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 7, 10} =
      !![0, 0, 0, 0, 4, 4;
      0, 2, 1, 0, 4, 0;
      2, 3, 3, 3, 3, 3;
      4, 4, 1, 4, 1, 4;
      4, 4, 3, 4, 4, 3;
      0, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1212 : Certificate {2, 3, 4, 5, 7, 10} := by
  refine ⟨!![2, 4, 1, 1, 2, 4;
      4, 1, 0, 3, 3, 2;
      1, 1, 1, 3, 0, 1;
      1, 3, 1, 4, 2, 2;
      3, 2, 2, 2, 4, 2;
      1, 3, 3, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 7, 10} =
      !![0, 0, 0, 0, 4, 4;
      0, 3, 2, 4, 1, 4;
      0, 3, 3, 3, 3, 3;
      1, 4, 1, 4, 1, 4;
      1, 4, 3, 4, 4, 3;
      2, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1223 : Certificate {0, 1, 2, 6, 7, 10} := by
  refine ⟨!![3, 0, 1, 3, 0, 3;
      4, 2, 1, 1, 3, 3;
      3, 0, 1, 2, 1, 1;
      0, 0, 1, 4, 0, 3;
      3, 4, 1, 4, 2, 2;
      4, 2, 0, 1, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 6, 7, 10} =
      !![0, 3, 2, 3, 2, 3;
      0, 2, 1, 3, 4, 3;
      0, 4, 0, 3, 4, 3;
      4, 4, 1, 0, 1, 4;
      4, 4, 1, 2, 4, 3;
      3, 0, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1227 : Certificate {0, 1, 3, 6, 7, 10} := by
  refine ⟨!![4, 1, 0, 4, 3, 1;
      0, 2, 3, 0, 0, 0;
      4, 1, 0, 3, 4, 4;
      4, 1, 1, 2, 4, 2;
      2, 2, 0, 1, 3, 3;
      4, 3, 2, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 6, 7, 10} =
      !![0, 0, 2, 0, 4, 0;
      0, 2, 2, 3, 4, 3;
      0, 4, 2, 3, 4, 3;
      4, 4, 4, 0, 1, 4;
      4, 4, 4, 2, 4, 3;
      3, 0, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1229 : Certificate {0, 2, 3, 6, 7, 10} := by
  refine ⟨!![3, 1, 3, 1, 2, 3;
      0, 1, 4, 0, 0, 0;
      3, 0, 4, 0, 3, 1;
      3, 0, 0, 4, 3, 4;
      4, 0, 1, 2, 0, 4;
      3, 0, 3, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 6, 7, 10} =
      !![0, 0, 3, 2, 1, 4;
      0, 1, 2, 3, 4, 3;
      0, 0, 2, 3, 4, 3;
      4, 1, 4, 0, 1, 4;
      4, 1, 4, 2, 4, 3;
      3, 2, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1230 : Certificate {1, 2, 3, 6, 7, 10} := by
  refine ⟨!![3, 0, 2, 3, 4, 4;
      1, 1, 3, 1, 3, 3;
      4, 4, 2, 3, 3, 0;
      4, 4, 3, 2, 3, 3;
      3, 2, 4, 2, 3, 4;
      2, 4, 3, 1, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 6, 7, 10} =
      !![0, 0, 0, 4, 4, 4;
      2, 1, 2, 3, 4, 3;
      4, 0, 2, 3, 4, 3;
      4, 1, 4, 0, 1, 4;
      4, 1, 4, 2, 4, 3;
      0, 2, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1235 : Certificate {0, 1, 4, 6, 7, 10} := by
  refine ⟨!![0, 2, 4, 4, 3, 1;
      2, 4, 1, 0, 0, 0;
      0, 2, 4, 3, 4, 4;
      0, 4, 4, 0, 3, 1;
      4, 2, 4, 3, 4, 4;
      2, 3, 3, 1, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 6, 7, 10} =
      !![0, 0, 1, 0, 4, 0;
      0, 3, 2, 3, 2, 3;
      0, 4, 0, 3, 4, 3;
      4, 4, 1, 0, 1, 4;
      4, 4, 3, 2, 4, 3;
      3, 0, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1237 : Certificate {0, 2, 4, 6, 7, 10} := by
  refine ⟨!![2, 3, 2, 3, 2, 2;
      1, 3, 4, 2, 2, 3;
      1, 0, 3, 0, 1, 2;
      2, 0, 2, 4, 2, 2;
      2, 0, 0, 2, 3, 0;
      2, 0, 0, 0, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 6, 7, 10} =
      !![0, 0, 2, 2, 1, 4;
      0, 2, 2, 3, 2, 3;
      0, 0, 0, 3, 4, 3;
      4, 1, 1, 0, 1, 4;
      4, 1, 3, 2, 4, 3;
      3, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1238 : Certificate {1, 2, 4, 6, 7, 10} := by
  refine ⟨!![3, 3, 3, 1, 4, 2;
      0, 4, 3, 3, 1, 2;
      0, 1, 2, 1, 0, 1;
      0, 2, 0, 1, 0, 0;
      1, 3, 4, 1, 4, 2;
      3, 0, 1, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 6, 7, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 2, 3;
      4, 0, 0, 3, 4, 3;
      4, 1, 1, 0, 1, 4;
      4, 1, 3, 2, 4, 3;
      0, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1241 : Certificate {0, 3, 4, 6, 7, 10} := by
  refine ⟨!![0, 4, 1, 4, 3, 1;
      1, 1, 2, 2, 2, 3;
      4, 3, 4, 1, 2, 1;
      4, 2, 1, 3, 1, 3;
      1, 4, 3, 0, 1, 2;
      4, 2, 4, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 6, 7, 10} =
      !![0, 3, 2, 2, 1, 4;
      0, 2, 1, 0, 4, 0;
      0, 2, 0, 3, 4, 3;
      4, 4, 1, 0, 1, 4;
      4, 4, 3, 2, 4, 3;
      3, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1242 : Certificate {1, 3, 4, 6, 7, 10} := by
  refine ⟨!![0, 2, 3, 2, 4, 3;
      1, 1, 3, 1, 1, 0;
      4, 4, 2, 3, 0, 3;
      4, 4, 3, 1, 1, 4;
      1, 0, 3, 0, 2, 3;
      4, 1, 4, 4, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 6, 7, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 1, 0, 4, 0;
      4, 2, 0, 3, 4, 3;
      4, 4, 1, 0, 1, 4;
      4, 4, 3, 2, 4, 3;
      0, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1244 : Certificate {2, 3, 4, 6, 7, 10} := by
  refine ⟨!![3, 2, 3, 2, 2, 1;
      3, 3, 1, 3, 2, 0;
      4, 0, 1, 4, 2, 2;
      1, 3, 4, 0, 1, 2;
      2, 4, 4, 4, 1, 0;
      1, 3, 2, 1, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 6, 7, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 2, 2, 1, 4;
      0, 2, 0, 3, 4, 3;
      1, 4, 1, 0, 1, 4;
      1, 4, 3, 2, 4, 3;
      2, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1251 : Certificate {0, 1, 5, 6, 7, 10} := by
  refine ⟨!![1, 0, 4, 3, 0, 3;
      4, 1, 3, 2, 1, 1;
      2, 0, 3, 4, 2, 2;
      0, 2, 0, 2, 4, 2;
      4, 0, 0, 0, 0, 0;
      2, 4, 0, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 6, 7, 10} =
      !![0, 0, 0, 0, 4, 0;
      0, 3, 2, 3, 2, 3;
      0, 2, 0, 3, 4, 3;
      4, 4, 4, 0, 1, 4;
      4, 4, 4, 2, 4, 3;
      3, 0, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1253 : Certificate {0, 2, 5, 6, 7, 10} := by
  refine ⟨!![4, 1, 4, 0, 0, 2;
      2, 0, 1, 0, 2, 4;
      4, 2, 1, 3, 3, 2;
      2, 2, 1, 2, 1, 1;
      0, 4, 2, 3, 4, 4;
      4, 1, 3, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 6, 7, 10} =
      !![0, 0, 4, 2, 1, 4;
      0, 2, 2, 3, 2, 3;
      0, 1, 0, 3, 4, 3;
      4, 1, 4, 0, 1, 4;
      4, 1, 4, 2, 4, 3;
      3, 2, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1254 : Certificate {1, 2, 5, 6, 7, 10} := by
  refine ⟨!![3, 4, 0, 2, 4, 3;
      4, 4, 4, 1, 4, 2;
      2, 2, 2, 1, 4, 2;
      4, 1, 4, 3, 3, 4;
      3, 3, 2, 0, 3, 2;
      2, 1, 4, 2, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 6, 7, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 2, 3;
      2, 1, 0, 3, 4, 3;
      4, 1, 4, 0, 1, 4;
      4, 1, 4, 2, 4, 3;
      0, 2, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1257 : Certificate {0, 3, 5, 6, 7, 10} := by
  refine ⟨!![1, 1, 2, 3, 1, 0;
      3, 0, 4, 0, 3, 1;
      1, 2, 1, 4, 3, 4;
      4, 2, 1, 3, 1, 3;
      1, 4, 3, 0, 1, 2;
      1, 1, 1, 2, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 6, 7, 10} =
      !![0, 3, 4, 2, 1, 4;
      0, 2, 0, 0, 4, 0;
      0, 2, 0, 3, 4, 3;
      4, 4, 4, 0, 1, 4;
      4, 4, 4, 2, 4, 3;
      3, 2, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1258 : Certificate {1, 3, 5, 6, 7, 10} := by
  refine ⟨!![4, 4, 2, 3, 0, 3;
      0, 2, 3, 1, 0, 1;
      0, 1, 4, 1, 2, 4;
      3, 1, 2, 2, 2, 4;
      0, 3, 1, 2, 0, 2;
      1, 1, 2, 1, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 6, 7, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 0, 0, 4, 0;
      2, 2, 0, 3, 4, 3;
      4, 4, 4, 0, 1, 4;
      4, 4, 4, 2, 4, 3;
      0, 2, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1260 : Certificate {2, 3, 5, 6, 7, 10} := by
  refine ⟨!![2, 3, 2, 3, 3, 4;
      2, 1, 1, 3, 1, 0;
      2, 2, 4, 1, 4, 3;
      2, 0, 4, 0, 2, 2;
      2, 0, 2, 1, 0, 1;
      0, 0, 4, 4, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 6, 7, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 4, 2, 1, 4;
      1, 2, 0, 3, 4, 3;
      1, 4, 4, 0, 1, 4;
      1, 4, 4, 2, 4, 3;
      2, 2, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1265 : Certificate {0, 4, 5, 6, 7, 10} := by
  refine ⟨!![2, 1, 0, 3, 2, 2;
      3, 3, 2, 4, 0, 3;
      3, 1, 1, 1, 1, 4;
      3, 3, 4, 1, 4, 0;
      3, 2, 2, 4, 0, 3;
      1, 3, 3, 3, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 6, 7, 10} =
      !![0, 2, 4, 2, 1, 4;
      0, 1, 0, 0, 4, 0;
      0, 2, 2, 3, 2, 3;
      4, 1, 4, 0, 1, 4;
      4, 3, 4, 2, 4, 3;
      3, 3, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1266 : Certificate {1, 4, 5, 6, 7, 10} := by
  refine ⟨!![2, 4, 3, 0, 3, 2;
      1, 1, 1, 2, 1, 1;
      3, 3, 3, 4, 0, 4;
      1, 1, 3, 4, 0, 3;
      1, 0, 1, 2, 1, 1;
      2, 4, 1, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 6, 7, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 1, 0, 0, 4, 0;
      3, 2, 2, 3, 2, 3;
      4, 1, 4, 0, 1, 4;
      4, 3, 4, 2, 4, 3;
      0, 3, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1268 : Certificate {2, 4, 5, 6, 7, 10} := by
  refine ⟨!![1, 1, 4, 4, 0, 2;
      3, 0, 4, 2, 4, 3;
      2, 3, 4, 1, 4, 1;
      4, 1, 0, 3, 3, 2;
      4, 3, 3, 4, 1, 2;
      1, 1, 2, 3, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 6, 7, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 4, 2, 1, 4;
      2, 2, 2, 3, 2, 3;
      1, 1, 4, 0, 1, 4;
      1, 3, 4, 2, 4, 3;
      2, 3, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1272 : Certificate {3, 4, 5, 6, 7, 10} := by
  refine ⟨!![0, 1, 3, 4, 1, 1;
      2, 2, 4, 0, 2, 4;
      1, 4, 1, 0, 1, 1;
      4, 0, 2, 4, 2, 1;
      2, 4, 4, 3, 4, 1;
      3, 1, 4, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 6, 7, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 4, 2, 1, 4;
      2, 1, 0, 0, 4, 0;
      4, 1, 4, 0, 1, 4;
      4, 3, 4, 2, 4, 3;
      2, 3, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 1197 then
    if mask < 1134 then
      if mask < 1111 then
        if mask < 1083 then
          if mask < 1071 then
            ⟨{0, 1, 2, 3, 4, 10}, certificate_1055⟩
          else
            if mask < 1079 then
              ⟨{0, 1, 2, 3, 5, 10}, certificate_1071⟩
            else
              ⟨{0, 1, 2, 4, 5, 10}, certificate_1079⟩
        else
          if mask < 1086 then
            if mask < 1085 then
              ⟨{0, 1, 3, 4, 5, 10}, certificate_1083⟩
            else
              ⟨{0, 2, 3, 4, 5, 10}, certificate_1085⟩
          else
            if mask < 1103 then
              ⟨{1, 2, 3, 4, 5, 10}, certificate_1086⟩
            else
              ⟨{0, 1, 2, 3, 6, 10}, certificate_1103⟩
      else
        if mask < 1118 then
          if mask < 1115 then
            ⟨{0, 1, 2, 4, 6, 10}, certificate_1111⟩
          else
            if mask < 1117 then
              ⟨{0, 1, 3, 4, 6, 10}, certificate_1115⟩
            else
              ⟨{0, 2, 3, 4, 6, 10}, certificate_1117⟩
        else
          if mask < 1131 then
            if mask < 1127 then
              ⟨{1, 2, 3, 4, 6, 10}, certificate_1118⟩
            else
              ⟨{0, 1, 2, 5, 6, 10}, certificate_1127⟩
          else
            if mask < 1133 then
              ⟨{0, 1, 3, 5, 6, 10}, certificate_1131⟩
            else
              ⟨{0, 2, 3, 5, 6, 10}, certificate_1133⟩
    else
      if mask < 1167 then
        if mask < 1142 then
          if mask < 1139 then
            ⟨{1, 2, 3, 5, 6, 10}, certificate_1134⟩
          else
            if mask < 1141 then
              ⟨{0, 1, 4, 5, 6, 10}, certificate_1139⟩
            else
              ⟨{0, 2, 4, 5, 6, 10}, certificate_1141⟩
        else
          if mask < 1146 then
            if mask < 1145 then
              ⟨{1, 2, 4, 5, 6, 10}, certificate_1142⟩
            else
              ⟨{0, 3, 4, 5, 6, 10}, certificate_1145⟩
          else
            if mask < 1148 then
              ⟨{1, 3, 4, 5, 6, 10}, certificate_1146⟩
            else
              ⟨{2, 3, 4, 5, 6, 10}, certificate_1148⟩
      else
        if mask < 1181 then
          if mask < 1175 then
            ⟨{0, 1, 2, 3, 7, 10}, certificate_1167⟩
          else
            if mask < 1179 then
              ⟨{0, 1, 2, 4, 7, 10}, certificate_1175⟩
            else
              ⟨{0, 1, 3, 4, 7, 10}, certificate_1179⟩
        else
          if mask < 1191 then
            if mask < 1182 then
              ⟨{0, 2, 3, 4, 7, 10}, certificate_1181⟩
            else
              ⟨{1, 2, 3, 4, 7, 10}, certificate_1182⟩
          else
            if mask < 1195 then
              ⟨{0, 1, 2, 5, 7, 10}, certificate_1191⟩
            else
              ⟨{0, 1, 3, 5, 7, 10}, certificate_1195⟩
  else
    if mask < 1238 then
      if mask < 1212 then
        if mask < 1205 then
          if mask < 1198 then
            ⟨{0, 2, 3, 5, 7, 10}, certificate_1197⟩
          else
            if mask < 1203 then
              ⟨{1, 2, 3, 5, 7, 10}, certificate_1198⟩
            else
              ⟨{0, 1, 4, 5, 7, 10}, certificate_1203⟩
        else
          if mask < 1209 then
            if mask < 1206 then
              ⟨{0, 2, 4, 5, 7, 10}, certificate_1205⟩
            else
              ⟨{1, 2, 4, 5, 7, 10}, certificate_1206⟩
          else
            if mask < 1210 then
              ⟨{0, 3, 4, 5, 7, 10}, certificate_1209⟩
            else
              ⟨{1, 3, 4, 5, 7, 10}, certificate_1210⟩
      else
        if mask < 1229 then
          if mask < 1223 then
            ⟨{2, 3, 4, 5, 7, 10}, certificate_1212⟩
          else
            if mask < 1227 then
              ⟨{0, 1, 2, 6, 7, 10}, certificate_1223⟩
            else
              ⟨{0, 1, 3, 6, 7, 10}, certificate_1227⟩
        else
          if mask < 1235 then
            if mask < 1230 then
              ⟨{0, 2, 3, 6, 7, 10}, certificate_1229⟩
            else
              ⟨{1, 2, 3, 6, 7, 10}, certificate_1230⟩
          else
            if mask < 1237 then
              ⟨{0, 1, 4, 6, 7, 10}, certificate_1235⟩
            else
              ⟨{0, 2, 4, 6, 7, 10}, certificate_1237⟩
    else
      if mask < 1257 then
        if mask < 1244 then
          if mask < 1241 then
            ⟨{1, 2, 4, 6, 7, 10}, certificate_1238⟩
          else
            if mask < 1242 then
              ⟨{0, 3, 4, 6, 7, 10}, certificate_1241⟩
            else
              ⟨{1, 3, 4, 6, 7, 10}, certificate_1242⟩
        else
          if mask < 1253 then
            if mask < 1251 then
              ⟨{2, 3, 4, 6, 7, 10}, certificate_1244⟩
            else
              ⟨{0, 1, 5, 6, 7, 10}, certificate_1251⟩
          else
            if mask < 1254 then
              ⟨{0, 2, 5, 6, 7, 10}, certificate_1253⟩
            else
              ⟨{1, 2, 5, 6, 7, 10}, certificate_1254⟩
      else
        if mask < 1265 then
          if mask < 1258 then
            ⟨{0, 3, 5, 6, 7, 10}, certificate_1257⟩
          else
            if mask < 1260 then
              ⟨{1, 3, 5, 6, 7, 10}, certificate_1258⟩
            else
              ⟨{2, 3, 5, 6, 7, 10}, certificate_1260⟩
        else
          if mask < 1268 then
            if mask < 1266 then
              ⟨{0, 4, 5, 6, 7, 10}, certificate_1265⟩
            else
              ⟨{1, 4, 5, 6, 7, 10}, certificate_1266⟩
          else
            if mask < 1272 then
              ⟨{2, 4, 5, 6, 7, 10}, certificate_1268⟩
            else
              ⟨{3, 4, 5, 6, 7, 10}, certificate_1272⟩
end AMEProbe.QuinaryDirect.Batch04
#print axioms AMEProbe.QuinaryDirect.Batch04.lookup
