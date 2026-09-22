import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch00
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_31 : Certificate {0, 1, 2, 3, 4} := by
  refine ⟨!![0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 1, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 3, 4} =
      !![1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_47 : Certificate {0, 1, 2, 3, 5} := by
  refine ⟨!![0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 3, 5} =
      !![0, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_55 : Certificate {0, 1, 2, 4, 5} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      0, 1, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 4, 5} =
      !![1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_59 : Certificate {0, 1, 3, 4, 5} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 4, 5} =
      !![0, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_61 : Certificate {0, 2, 3, 4, 5} := by
  refine ⟨!![0, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 4, 5} =
      !![0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_62 : Certificate {1, 2, 3, 4, 5} := by
  refine ⟨!![0, 0, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 4, 5} =
      !![0, 0, 1, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_79 : Certificate {0, 1, 2, 3, 6} := by
  refine ⟨!![0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 3, 6} =
      !![0, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_87 : Certificate {0, 1, 2, 4, 6} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 1;
      1, 0, 1, 0, 0, 0, 1;
      1, 0, 1, 1, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 4, 6} =
      !![1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_91 : Certificate {0, 1, 3, 4, 6} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 4, 6} =
      !![0, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_93 : Certificate {0, 2, 3, 4, 6} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 4, 6} =
      !![0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_94 : Certificate {1, 2, 3, 4, 6} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 4, 6} =
      !![0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_103 : Certificate {0, 1, 2, 5, 6} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 5, 6} =
      !![1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_107 : Certificate {0, 1, 3, 5, 6} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 5, 6} =
      !![0, 0, 0, 1, 0;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_109 : Certificate {0, 2, 3, 5, 6} := by
  refine ⟨!![0, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 5, 6} =
      !![0, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_110 : Certificate {1, 2, 3, 5, 6} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 5, 6} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_115 : Certificate {0, 1, 4, 5, 6} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 5, 6} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_117 : Certificate {0, 2, 4, 5, 6} := by
  refine ⟨!![0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 5, 6} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_118 : Certificate {1, 2, 4, 5, 6} := by
  refine ⟨!![0, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 5, 6} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_121 : Certificate {0, 3, 4, 5, 6} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 5, 6} =
      !![0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_122 : Certificate {1, 3, 4, 5, 6} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 5, 6} =
      !![0, 1, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_124 : Certificate {2, 3, 4, 5, 6} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 1;
      1, 0, 1, 0, 0, 0, 1;
      1, 1, 0, 0, 1, 0, 1;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 5, 6} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_143 : Certificate {0, 1, 2, 3, 7} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 1;
      0, 0, 1, 0, 1, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 3, 7} =
      !![0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_151 : Certificate {0, 1, 2, 4, 7} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 4, 7} =
      !![1, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_155 : Certificate {0, 1, 3, 4, 7} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 1, 0;
      1, 0, 1, 0, 1, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 4, 7} =
      !![0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_157 : Certificate {0, 2, 3, 4, 7} := by
  refine ⟨!![1, 0, 1, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1, 0;
      0, 1, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 4, 7} =
      !![0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_158 : Certificate {1, 2, 3, 4, 7} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 1;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 4, 7} =
      !![0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_167 : Certificate {0, 1, 2, 5, 7} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 5, 7} =
      !![1, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_171 : Certificate {0, 1, 3, 5, 7} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 5, 7} =
      !![0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_173 : Certificate {0, 2, 3, 5, 7} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 1;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 1;
      0, 0, 1, 0, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 5, 7} =
      !![0, 0, 0, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_174 : Certificate {1, 2, 3, 5, 7} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 5, 7} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_179 : Certificate {0, 1, 4, 5, 7} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 5, 7} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_181 : Certificate {0, 2, 4, 5, 7} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 1, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 5, 7} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_182 : Certificate {1, 2, 4, 5, 7} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 1, 1, 0;
      0, 0, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 5, 7} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 1;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_185 : Certificate {0, 3, 4, 5, 7} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 5, 7} =
      !![0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_186 : Certificate {1, 3, 4, 5, 7} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 5, 7} =
      !![0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_188 : Certificate {2, 3, 4, 5, 7} := by
  refine ⟨!![0, 1, 0, 1, 0, 1, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 5, 7} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_199 : Certificate {0, 1, 2, 6, 7} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 6, 7} =
      !![1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 0, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_203 : Certificate {0, 1, 3, 6, 7} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 6, 7} =
      !![0, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_205 : Certificate {0, 2, 3, 6, 7} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 6, 7} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_206 : Certificate {1, 2, 3, 6, 7} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 6, 7} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_211 : Certificate {0, 1, 4, 6, 7} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 6, 7} =
      !![0, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_213 : Certificate {0, 2, 4, 6, 7} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 6, 7} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_214 : Certificate {1, 2, 4, 6, 7} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 6, 7} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_217 : Certificate {0, 3, 4, 6, 7} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 6, 7} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_218 : Certificate {1, 3, 4, 6, 7} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 1;
      0, 0, 0, 0, 1, 0, 1;
      1, 1, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 1;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 6, 7} =
      !![0, 1, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 1, 1, 0, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_220 : Certificate {2, 3, 4, 6, 7} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 6, 7} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_227 : Certificate {0, 1, 5, 6, 7} := by
  refine ⟨!![0, 1, 1, 0, 0, 1, 1;
      1, 0, 0, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 1;
      1, 0, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 6, 7} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 0, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_229 : Certificate {0, 2, 5, 6, 7} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 6, 7} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_230 : Certificate {1, 2, 5, 6, 7} := by
  refine ⟨!![1, 1, 0, 0, 0, 1, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 6, 7} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_233 : Certificate {0, 3, 5, 6, 7} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 6, 7} =
      !![0, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_234 : Certificate {1, 3, 5, 6, 7} := by
  refine ⟨!![0, 0, 1, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 6, 7} =
      !![0, 1, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_236 : Certificate {2, 3, 5, 6, 7} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 6, 7} =
      !![0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_241 : Certificate {0, 4, 5, 6, 7} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 6, 7} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_242 : Certificate {1, 4, 5, 6, 7} := by
  refine ⟨!![1, 0, 0, 0, 1, 1, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 6, 7} =
      !![0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_244 : Certificate {2, 4, 5, 6, 7} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 6, 7} =
      !![0, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_248 : Certificate {3, 4, 5, 6, 7} := by
  refine ⟨!![1, 1, 1, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 6, 7} =
      !![1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 173 then
    if mask < 110 then
      if mask < 87 then
        if mask < 59 then
          if mask < 47 then
            ⟨{0, 1, 2, 3, 4}, certificate_31⟩
          else
            if mask < 55 then
              ⟨{0, 1, 2, 3, 5}, certificate_47⟩
            else
              ⟨{0, 1, 2, 4, 5}, certificate_55⟩
        else
          if mask < 62 then
            if mask < 61 then
              ⟨{0, 1, 3, 4, 5}, certificate_59⟩
            else
              ⟨{0, 2, 3, 4, 5}, certificate_61⟩
          else
            if mask < 79 then
              ⟨{1, 2, 3, 4, 5}, certificate_62⟩
            else
              ⟨{0, 1, 2, 3, 6}, certificate_79⟩
      else
        if mask < 94 then
          if mask < 91 then
            ⟨{0, 1, 2, 4, 6}, certificate_87⟩
          else
            if mask < 93 then
              ⟨{0, 1, 3, 4, 6}, certificate_91⟩
            else
              ⟨{0, 2, 3, 4, 6}, certificate_93⟩
        else
          if mask < 107 then
            if mask < 103 then
              ⟨{1, 2, 3, 4, 6}, certificate_94⟩
            else
              ⟨{0, 1, 2, 5, 6}, certificate_103⟩
          else
            if mask < 109 then
              ⟨{0, 1, 3, 5, 6}, certificate_107⟩
            else
              ⟨{0, 2, 3, 5, 6}, certificate_109⟩
    else
      if mask < 143 then
        if mask < 118 then
          if mask < 115 then
            ⟨{1, 2, 3, 5, 6}, certificate_110⟩
          else
            if mask < 117 then
              ⟨{0, 1, 4, 5, 6}, certificate_115⟩
            else
              ⟨{0, 2, 4, 5, 6}, certificate_117⟩
        else
          if mask < 122 then
            if mask < 121 then
              ⟨{1, 2, 4, 5, 6}, certificate_118⟩
            else
              ⟨{0, 3, 4, 5, 6}, certificate_121⟩
          else
            if mask < 124 then
              ⟨{1, 3, 4, 5, 6}, certificate_122⟩
            else
              ⟨{2, 3, 4, 5, 6}, certificate_124⟩
      else
        if mask < 157 then
          if mask < 151 then
            ⟨{0, 1, 2, 3, 7}, certificate_143⟩
          else
            if mask < 155 then
              ⟨{0, 1, 2, 4, 7}, certificate_151⟩
            else
              ⟨{0, 1, 3, 4, 7}, certificate_155⟩
        else
          if mask < 167 then
            if mask < 158 then
              ⟨{0, 2, 3, 4, 7}, certificate_157⟩
            else
              ⟨{1, 2, 3, 4, 7}, certificate_158⟩
          else
            if mask < 171 then
              ⟨{0, 1, 2, 5, 7}, certificate_167⟩
            else
              ⟨{0, 1, 3, 5, 7}, certificate_171⟩
  else
    if mask < 214 then
      if mask < 188 then
        if mask < 181 then
          if mask < 174 then
            ⟨{0, 2, 3, 5, 7}, certificate_173⟩
          else
            if mask < 179 then
              ⟨{1, 2, 3, 5, 7}, certificate_174⟩
            else
              ⟨{0, 1, 4, 5, 7}, certificate_179⟩
        else
          if mask < 185 then
            if mask < 182 then
              ⟨{0, 2, 4, 5, 7}, certificate_181⟩
            else
              ⟨{1, 2, 4, 5, 7}, certificate_182⟩
          else
            if mask < 186 then
              ⟨{0, 3, 4, 5, 7}, certificate_185⟩
            else
              ⟨{1, 3, 4, 5, 7}, certificate_186⟩
      else
        if mask < 205 then
          if mask < 199 then
            ⟨{2, 3, 4, 5, 7}, certificate_188⟩
          else
            if mask < 203 then
              ⟨{0, 1, 2, 6, 7}, certificate_199⟩
            else
              ⟨{0, 1, 3, 6, 7}, certificate_203⟩
        else
          if mask < 211 then
            if mask < 206 then
              ⟨{0, 2, 3, 6, 7}, certificate_205⟩
            else
              ⟨{1, 2, 3, 6, 7}, certificate_206⟩
          else
            if mask < 213 then
              ⟨{0, 1, 4, 6, 7}, certificate_211⟩
            else
              ⟨{0, 2, 4, 6, 7}, certificate_213⟩
    else
      if mask < 233 then
        if mask < 220 then
          if mask < 217 then
            ⟨{1, 2, 4, 6, 7}, certificate_214⟩
          else
            if mask < 218 then
              ⟨{0, 3, 4, 6, 7}, certificate_217⟩
            else
              ⟨{1, 3, 4, 6, 7}, certificate_218⟩
        else
          if mask < 229 then
            if mask < 227 then
              ⟨{2, 3, 4, 6, 7}, certificate_220⟩
            else
              ⟨{0, 1, 5, 6, 7}, certificate_227⟩
          else
            if mask < 230 then
              ⟨{0, 2, 5, 6, 7}, certificate_229⟩
            else
              ⟨{1, 2, 5, 6, 7}, certificate_230⟩
      else
        if mask < 241 then
          if mask < 234 then
            ⟨{0, 3, 5, 6, 7}, certificate_233⟩
          else
            if mask < 236 then
              ⟨{1, 3, 5, 6, 7}, certificate_234⟩
            else
              ⟨{2, 3, 5, 6, 7}, certificate_236⟩
        else
          if mask < 244 then
            if mask < 242 then
              ⟨{0, 4, 5, 6, 7}, certificate_241⟩
            else
              ⟨{1, 4, 5, 6, 7}, certificate_242⟩
          else
            if mask < 248 then
              ⟨{2, 4, 5, 6, 7}, certificate_244⟩
            else
              ⟨{3, 4, 5, 6, 7}, certificate_248⟩
end AMEProbe.BinaryDirect.Batch00
#print axioms AMEProbe.BinaryDirect.Batch00.lookup
