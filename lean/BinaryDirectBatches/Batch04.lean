import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch04
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_1039 : Certificate {0, 1, 2, 3, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 3, 10} =
      !![0, 1, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1047 : Certificate {0, 1, 2, 4, 10} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 4, 10} =
      !![1, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 1;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1051 : Certificate {0, 1, 3, 4, 10} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 1;
      0, 1, 0, 1, 1, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 4, 10} =
      !![0, 0, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 1;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1053 : Certificate {0, 2, 3, 4, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 4, 10} =
      !![0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 1;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1054 : Certificate {1, 2, 3, 4, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 4, 10} =
      !![0, 0, 1, 0, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1063 : Certificate {0, 1, 2, 5, 10} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 1;
      0, 0, 0, 0, 1, 0, 1;
      1, 0, 0, 1, 1, 0, 1;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 5, 10} =
      !![1, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1067 : Certificate {0, 1, 3, 5, 10} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 5, 10} =
      !![0, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1069 : Certificate {0, 2, 3, 5, 10} := by
  refine ⟨!![1, 0, 1, 1, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 5, 10} =
      !![0, 0, 0, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 1, 0;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1070 : Certificate {1, 2, 3, 5, 10} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 5, 10} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1075 : Certificate {0, 1, 4, 5, 10} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 5, 10} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1077 : Certificate {0, 2, 4, 5, 10} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 5, 10} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1078 : Certificate {1, 2, 4, 5, 10} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 5, 10} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1081 : Certificate {0, 3, 4, 5, 10} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 5, 10} =
      !![0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1082 : Certificate {1, 3, 4, 5, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 5, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1084 : Certificate {2, 3, 4, 5, 10} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 5, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1095 : Certificate {0, 1, 2, 6, 10} := by
  refine ⟨!![0, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 6, 10} =
      !![1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 1, 0, 1;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1099 : Certificate {0, 1, 3, 6, 10} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 1, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 6, 10} =
      !![0, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1101 : Certificate {0, 2, 3, 6, 10} := by
  refine ⟨!![1, 1, 0, 0, 1, 1, 0;
      1, 0, 1, 0, 1, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 6, 10} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1102 : Certificate {1, 2, 3, 6, 10} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 6, 10} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1107 : Certificate {0, 1, 4, 6, 10} := by
  refine ⟨!![0, 1, 0, 1, 1, 1, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 6, 10} =
      !![0, 0, 0, 0, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1109 : Certificate {0, 2, 4, 6, 10} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 6, 10} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1110 : Certificate {1, 2, 4, 6, 10} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 6, 10} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1113 : Certificate {0, 3, 4, 6, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 1;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 6, 10} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1114 : Certificate {1, 3, 4, 6, 10} := by
  refine ⟨!![1, 0, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 1, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 0, 1, 1, 1, 1, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 6, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 0, 0;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1116 : Certificate {2, 3, 4, 6, 10} := by
  refine ⟨!![1, 0, 1, 1, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 6, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1123 : Certificate {0, 1, 5, 6, 10} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 6, 10} =
      !![0, 0, 1, 0, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 0, 0, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1125 : Certificate {0, 2, 5, 6, 10} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 6, 10} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1126 : Certificate {1, 2, 5, 6, 10} := by
  refine ⟨!![0, 1, 0, 1, 0, 1, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 0, 1, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 6, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1129 : Certificate {0, 3, 5, 6, 10} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 6, 10} =
      !![0, 0, 0, 1, 1;
      0, 0, 1, 0, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1130 : Certificate {1, 3, 5, 6, 10} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 1;
      1, 1, 1, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 6, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 0;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1132 : Certificate {2, 3, 5, 6, 10} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 6, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1137 : Certificate {0, 4, 5, 6, 10} := by
  refine ⟨!![0, 0, 1, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 6, 10} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 0, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1138 : Certificate {1, 4, 5, 6, 10} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 6, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1140 : Certificate {2, 4, 5, 6, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 1;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 1;
      1, 0, 1, 1, 0, 0, 1;
      1, 0, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 6, 10} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1144 : Certificate {3, 4, 5, 6, 10} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 6, 10} =
      !![1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1159 : Certificate {0, 1, 2, 7, 10} := by
  refine ⟨!![1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 7, 10} =
      !![1, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1163 : Certificate {0, 1, 3, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 7, 10} =
      !![0, 0, 0, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 0, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1165 : Certificate {0, 2, 3, 7, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 7, 10} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1166 : Certificate {1, 2, 3, 7, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 7, 10} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1171 : Certificate {0, 1, 4, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 7, 10} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1173 : Certificate {0, 2, 4, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 7, 10} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1174 : Certificate {1, 2, 4, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 7, 10} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1177 : Certificate {0, 3, 4, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 7, 10} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1178 : Certificate {1, 3, 4, 7, 10} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 7, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1180 : Certificate {2, 3, 4, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 7, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1187 : Certificate {0, 1, 5, 7, 10} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 7, 10} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1189 : Certificate {0, 2, 5, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 7, 10} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1190 : Certificate {1, 2, 5, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 7, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1193 : Certificate {0, 3, 5, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 1;
      0, 0, 0, 0, 1, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 7, 10} =
      !![0, 0, 0, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1194 : Certificate {1, 3, 5, 7, 10} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 7, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1196 : Certificate {2, 3, 5, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 1, 0;
      1, 0, 0, 1, 1, 1, 0;
      1, 1, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 7, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1201 : Certificate {0, 4, 5, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 7, 10} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 0, 1, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1202 : Certificate {1, 4, 5, 7, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 7, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1204 : Certificate {2, 4, 5, 7, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 1;
      0, 0, 0, 0, 1, 0, 1;
      1, 1, 1, 0, 1, 0, 1;
      0, 1, 1, 0, 1, 0, 1;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 7, 10} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1208 : Certificate {3, 4, 5, 7, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 7, 10} =
      !![1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1219 : Certificate {0, 1, 6, 7, 10} := by
  refine ⟨!![1, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 6, 7, 10} =
      !![0, 0, 0, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1221 : Certificate {0, 2, 6, 7, 10} := by
  refine ⟨!![0, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 6, 7, 10} =
      !![0, 0, 1, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1222 : Certificate {1, 2, 6, 7, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 6, 7, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1225 : Certificate {0, 3, 6, 7, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 6, 7, 10} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1226 : Certificate {1, 3, 6, 7, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 6, 7, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1228 : Certificate {2, 3, 6, 7, 10} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 1;
      1, 0, 1, 1, 0, 0, 1;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 6, 7, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1233 : Certificate {0, 4, 6, 7, 10} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 1;
      0, 0, 1, 1, 0, 0, 1;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 6, 7, 10} =
      !![0, 1, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1234 : Certificate {1, 4, 6, 7, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 6, 7, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1236 : Certificate {2, 4, 6, 7, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 6, 7, 10} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1240 : Certificate {3, 4, 6, 7, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 6, 7, 10} =
      !![1, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1249 : Certificate {0, 5, 6, 7, 10} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 6, 7, 10} =
      !![0, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1250 : Certificate {1, 5, 6, 7, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 1;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 6, 7, 10} =
      !![0, 1, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1252 : Certificate {2, 5, 6, 7, 10} := by
  refine ⟨!![1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 6, 7, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1256 : Certificate {3, 5, 6, 7, 10} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 6, 7, 10} =
      !![1, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1264 : Certificate {4, 5, 6, 7, 10} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 6, 7, 10} =
      !![0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 1159 then
    if mask < 1101 then
      if mask < 1070 then
        if mask < 1054 then
          if mask < 1051 then
            if mask < 1047 then
              ⟨{0, 1, 2, 3, 10}, certificate_1039⟩
            else
              ⟨{0, 1, 2, 4, 10}, certificate_1047⟩
          else
            if mask < 1053 then
              ⟨{0, 1, 3, 4, 10}, certificate_1051⟩
            else
              ⟨{0, 2, 3, 4, 10}, certificate_1053⟩
        else
          if mask < 1067 then
            if mask < 1063 then
              ⟨{1, 2, 3, 4, 10}, certificate_1054⟩
            else
              ⟨{0, 1, 2, 5, 10}, certificate_1063⟩
          else
            if mask < 1069 then
              ⟨{0, 1, 3, 5, 10}, certificate_1067⟩
            else
              ⟨{0, 2, 3, 5, 10}, certificate_1069⟩
      else
        if mask < 1081 then
          if mask < 1077 then
            if mask < 1075 then
              ⟨{1, 2, 3, 5, 10}, certificate_1070⟩
            else
              ⟨{0, 1, 4, 5, 10}, certificate_1075⟩
          else
            if mask < 1078 then
              ⟨{0, 2, 4, 5, 10}, certificate_1077⟩
            else
              ⟨{1, 2, 4, 5, 10}, certificate_1078⟩
        else
          if mask < 1084 then
            if mask < 1082 then
              ⟨{0, 3, 4, 5, 10}, certificate_1081⟩
            else
              ⟨{1, 3, 4, 5, 10}, certificate_1082⟩
          else
            if mask < 1095 then
              ⟨{2, 3, 4, 5, 10}, certificate_1084⟩
            else
              if mask < 1099 then
                ⟨{0, 1, 2, 6, 10}, certificate_1095⟩
              else
                ⟨{0, 1, 3, 6, 10}, certificate_1099⟩
    else
      if mask < 1125 then
        if mask < 1110 then
          if mask < 1107 then
            if mask < 1102 then
              ⟨{0, 2, 3, 6, 10}, certificate_1101⟩
            else
              ⟨{1, 2, 3, 6, 10}, certificate_1102⟩
          else
            if mask < 1109 then
              ⟨{0, 1, 4, 6, 10}, certificate_1107⟩
            else
              ⟨{0, 2, 4, 6, 10}, certificate_1109⟩
        else
          if mask < 1114 then
            if mask < 1113 then
              ⟨{1, 2, 4, 6, 10}, certificate_1110⟩
            else
              ⟨{0, 3, 4, 6, 10}, certificate_1113⟩
          else
            if mask < 1116 then
              ⟨{1, 3, 4, 6, 10}, certificate_1114⟩
            else
              if mask < 1123 then
                ⟨{2, 3, 4, 6, 10}, certificate_1116⟩
              else
                ⟨{0, 1, 5, 6, 10}, certificate_1123⟩
      else
        if mask < 1132 then
          if mask < 1129 then
            if mask < 1126 then
              ⟨{0, 2, 5, 6, 10}, certificate_1125⟩
            else
              ⟨{1, 2, 5, 6, 10}, certificate_1126⟩
          else
            if mask < 1130 then
              ⟨{0, 3, 5, 6, 10}, certificate_1129⟩
            else
              ⟨{1, 3, 5, 6, 10}, certificate_1130⟩
        else
          if mask < 1138 then
            if mask < 1137 then
              ⟨{2, 3, 5, 6, 10}, certificate_1132⟩
            else
              ⟨{0, 4, 5, 6, 10}, certificate_1137⟩
          else
            if mask < 1140 then
              ⟨{1, 4, 5, 6, 10}, certificate_1138⟩
            else
              if mask < 1144 then
                ⟨{2, 4, 5, 6, 10}, certificate_1140⟩
              else
                ⟨{3, 4, 5, 6, 10}, certificate_1144⟩
  else
    if mask < 1202 then
      if mask < 1178 then
        if mask < 1171 then
          if mask < 1165 then
            if mask < 1163 then
              ⟨{0, 1, 2, 7, 10}, certificate_1159⟩
            else
              ⟨{0, 1, 3, 7, 10}, certificate_1163⟩
          else
            if mask < 1166 then
              ⟨{0, 2, 3, 7, 10}, certificate_1165⟩
            else
              ⟨{1, 2, 3, 7, 10}, certificate_1166⟩
        else
          if mask < 1174 then
            if mask < 1173 then
              ⟨{0, 1, 4, 7, 10}, certificate_1171⟩
            else
              ⟨{0, 2, 4, 7, 10}, certificate_1173⟩
          else
            if mask < 1177 then
              ⟨{1, 2, 4, 7, 10}, certificate_1174⟩
            else
              ⟨{0, 3, 4, 7, 10}, certificate_1177⟩
      else
        if mask < 1190 then
          if mask < 1187 then
            if mask < 1180 then
              ⟨{1, 3, 4, 7, 10}, certificate_1178⟩
            else
              ⟨{2, 3, 4, 7, 10}, certificate_1180⟩
          else
            if mask < 1189 then
              ⟨{0, 1, 5, 7, 10}, certificate_1187⟩
            else
              ⟨{0, 2, 5, 7, 10}, certificate_1189⟩
        else
          if mask < 1194 then
            if mask < 1193 then
              ⟨{1, 2, 5, 7, 10}, certificate_1190⟩
            else
              ⟨{0, 3, 5, 7, 10}, certificate_1193⟩
          else
            if mask < 1196 then
              ⟨{1, 3, 5, 7, 10}, certificate_1194⟩
            else
              if mask < 1201 then
                ⟨{2, 3, 5, 7, 10}, certificate_1196⟩
              else
                ⟨{0, 4, 5, 7, 10}, certificate_1201⟩
    else
      if mask < 1233 then
        if mask < 1221 then
          if mask < 1208 then
            if mask < 1204 then
              ⟨{1, 4, 5, 7, 10}, certificate_1202⟩
            else
              ⟨{2, 4, 5, 7, 10}, certificate_1204⟩
          else
            if mask < 1219 then
              ⟨{3, 4, 5, 7, 10}, certificate_1208⟩
            else
              ⟨{0, 1, 6, 7, 10}, certificate_1219⟩
        else
          if mask < 1225 then
            if mask < 1222 then
              ⟨{0, 2, 6, 7, 10}, certificate_1221⟩
            else
              ⟨{1, 2, 6, 7, 10}, certificate_1222⟩
          else
            if mask < 1226 then
              ⟨{0, 3, 6, 7, 10}, certificate_1225⟩
            else
              if mask < 1228 then
                ⟨{1, 3, 6, 7, 10}, certificate_1226⟩
              else
                ⟨{2, 3, 6, 7, 10}, certificate_1228⟩
      else
        if mask < 1249 then
          if mask < 1236 then
            if mask < 1234 then
              ⟨{0, 4, 6, 7, 10}, certificate_1233⟩
            else
              ⟨{1, 4, 6, 7, 10}, certificate_1234⟩
          else
            if mask < 1240 then
              ⟨{2, 4, 6, 7, 10}, certificate_1236⟩
            else
              ⟨{3, 4, 6, 7, 10}, certificate_1240⟩
        else
          if mask < 1252 then
            if mask < 1250 then
              ⟨{0, 5, 6, 7, 10}, certificate_1249⟩
            else
              ⟨{1, 5, 6, 7, 10}, certificate_1250⟩
          else
            if mask < 1256 then
              ⟨{2, 5, 6, 7, 10}, certificate_1252⟩
            else
              if mask < 1264 then
                ⟨{3, 5, 6, 7, 10}, certificate_1256⟩
              else
                ⟨{4, 5, 6, 7, 10}, certificate_1264⟩
end AMEProbe.BinaryDirect.Batch04
#print axioms AMEProbe.BinaryDirect.Batch04.lookup
