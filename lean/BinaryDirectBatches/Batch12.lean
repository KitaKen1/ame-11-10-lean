import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch12
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_3079 : Certificate {0, 1, 2, 10, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 1, 1, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 10, 11} =
      !![1, 0, 0, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3083 : Certificate {0, 1, 3, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 10, 11} =
      !![0, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3085 : Certificate {0, 2, 3, 10, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      0, 1, 1, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 10, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3086 : Certificate {1, 2, 3, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 10, 11} =
      !![0, 0, 1, 0, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3091 : Certificate {0, 1, 4, 10, 11} := by
  refine ⟨!![0, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 10, 11} =
      !![0, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3093 : Certificate {0, 2, 4, 10, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1;
      1, 0, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 10, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 0;
      1, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 1, 0;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3094 : Certificate {1, 2, 4, 10, 11} := by
  refine ⟨!![0, 1, 1, 0, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 10, 11} =
      !![0, 0, 0, 0, 0;
      0, 0, 0, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3097 : Certificate {0, 3, 4, 10, 11} := by
  refine ⟨!![1, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 10, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3098 : Certificate {1, 3, 4, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 10, 11} =
      !![0, 1, 0, 0, 0;
      0, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3100 : Certificate {2, 3, 4, 10, 11} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 10, 11} =
      !![0, 1, 0, 0, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 1, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3107 : Certificate {0, 1, 5, 10, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      0, 0, 1, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 10, 11} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3109 : Certificate {0, 2, 5, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 10, 11} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3110 : Certificate {1, 2, 5, 10, 11} := by
  refine ⟨!![1, 0, 1, 0, 1, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3113 : Certificate {0, 3, 5, 10, 11} := by
  refine ⟨!![1, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 10, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3114 : Certificate {1, 3, 5, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3116 : Certificate {2, 3, 5, 10, 11} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 1, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3121 : Certificate {0, 4, 5, 10, 11} := by
  refine ⟨!![1, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 10, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3122 : Certificate {1, 4, 5, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3124 : Certificate {2, 4, 5, 10, 11} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3128 : Certificate {3, 4, 5, 10, 11} := by
  refine ⟨!![0, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 1;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 1;
      1, 0, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 10, 11} =
      !![1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3139 : Certificate {0, 1, 6, 10, 11} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 6, 10, 11} =
      !![0, 0, 0, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3141 : Certificate {0, 2, 6, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 6, 10, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 1, 1;
      1, 1, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3142 : Certificate {1, 2, 6, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 6, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 1, 1;
      1, 1, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3145 : Certificate {0, 3, 6, 10, 11} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 6, 10, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3146 : Certificate {1, 3, 6, 10, 11} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 6, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3148 : Certificate {2, 3, 6, 10, 11} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 6, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3153 : Certificate {0, 4, 6, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 6, 10, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3154 : Certificate {1, 4, 6, 10, 11} := by
  refine ⟨!![0, 1, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 6, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3156 : Certificate {2, 4, 6, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 6, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3160 : Certificate {3, 4, 6, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 6, 10, 11} =
      !![1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3169 : Certificate {0, 5, 6, 10, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 6, 10, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3170 : Certificate {1, 5, 6, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 6, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 0, 0, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3172 : Certificate {2, 5, 6, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 0, 0, 1, 1, 1, 0;
      1, 1, 0, 1, 1, 1, 0;
      1, 1, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 6, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3176 : Certificate {3, 5, 6, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 6, 10, 11} =
      !![1, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 0, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3184 : Certificate {4, 5, 6, 10, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 6, 10, 11} =
      !![0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 0, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3203 : Certificate {0, 1, 7, 10, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 7, 10, 11} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3205 : Certificate {0, 2, 7, 10, 11} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 7, 10, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3206 : Certificate {1, 2, 7, 10, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 7, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3209 : Certificate {0, 3, 7, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 7, 10, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3210 : Certificate {1, 3, 7, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 7, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 0, 1;
      1, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3212 : Certificate {2, 3, 7, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 7, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3217 : Certificate {0, 4, 7, 10, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 7, 10, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3218 : Certificate {1, 4, 7, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 7, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3220 : Certificate {2, 4, 7, 10, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 7, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3224 : Certificate {3, 4, 7, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 7, 10, 11} =
      !![1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3233 : Certificate {0, 5, 7, 10, 11} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 7, 10, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3234 : Certificate {1, 5, 7, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 7, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3236 : Certificate {2, 5, 7, 10, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 7, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3240 : Certificate {3, 5, 7, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 7, 10, 11} =
      !![1, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3248 : Certificate {4, 5, 7, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 7, 10, 11} =
      !![0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3265 : Certificate {0, 6, 7, 10, 11} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 6, 7, 10, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3266 : Certificate {1, 6, 7, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      0, 0, 1, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 6, 7, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3268 : Certificate {2, 6, 7, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 6, 7, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3272 : Certificate {3, 6, 7, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 6, 7, 10, 11} =
      !![1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3280 : Certificate {4, 6, 7, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 6, 7, 10, 11} =
      !![0, 1, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3296 : Certificate {5, 6, 7, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 1;
      1, 0, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 6, 7, 10, 11} =
      !![1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 3156 then
    if mask < 3114 then
      if mask < 3097 then
        if mask < 3086 then
          if mask < 3083 then
            ⟨{0, 1, 2, 10, 11}, certificate_3079⟩
          else
            if mask < 3085 then
              ⟨{0, 1, 3, 10, 11}, certificate_3083⟩
            else
              ⟨{0, 2, 3, 10, 11}, certificate_3085⟩
        else
          if mask < 3093 then
            if mask < 3091 then
              ⟨{1, 2, 3, 10, 11}, certificate_3086⟩
            else
              ⟨{0, 1, 4, 10, 11}, certificate_3091⟩
          else
            if mask < 3094 then
              ⟨{0, 2, 4, 10, 11}, certificate_3093⟩
            else
              ⟨{1, 2, 4, 10, 11}, certificate_3094⟩
      else
        if mask < 3107 then
          if mask < 3098 then
            ⟨{0, 3, 4, 10, 11}, certificate_3097⟩
          else
            if mask < 3100 then
              ⟨{1, 3, 4, 10, 11}, certificate_3098⟩
            else
              ⟨{2, 3, 4, 10, 11}, certificate_3100⟩
        else
          if mask < 3110 then
            if mask < 3109 then
              ⟨{0, 1, 5, 10, 11}, certificate_3107⟩
            else
              ⟨{0, 2, 5, 10, 11}, certificate_3109⟩
          else
            if mask < 3113 then
              ⟨{1, 2, 5, 10, 11}, certificate_3110⟩
            else
              ⟨{0, 3, 5, 10, 11}, certificate_3113⟩
    else
      if mask < 3141 then
        if mask < 3122 then
          if mask < 3116 then
            ⟨{1, 3, 5, 10, 11}, certificate_3114⟩
          else
            if mask < 3121 then
              ⟨{2, 3, 5, 10, 11}, certificate_3116⟩
            else
              ⟨{0, 4, 5, 10, 11}, certificate_3121⟩
        else
          if mask < 3128 then
            if mask < 3124 then
              ⟨{1, 4, 5, 10, 11}, certificate_3122⟩
            else
              ⟨{2, 4, 5, 10, 11}, certificate_3124⟩
          else
            if mask < 3139 then
              ⟨{3, 4, 5, 10, 11}, certificate_3128⟩
            else
              ⟨{0, 1, 6, 10, 11}, certificate_3139⟩
      else
        if mask < 3146 then
          if mask < 3142 then
            ⟨{0, 2, 6, 10, 11}, certificate_3141⟩
          else
            if mask < 3145 then
              ⟨{1, 2, 6, 10, 11}, certificate_3142⟩
            else
              ⟨{0, 3, 6, 10, 11}, certificate_3145⟩
        else
          if mask < 3153 then
            if mask < 3148 then
              ⟨{1, 3, 6, 10, 11}, certificate_3146⟩
            else
              ⟨{2, 3, 6, 10, 11}, certificate_3148⟩
          else
            if mask < 3154 then
              ⟨{0, 4, 6, 10, 11}, certificate_3153⟩
            else
              ⟨{1, 4, 6, 10, 11}, certificate_3154⟩
  else
    if mask < 3218 then
      if mask < 3203 then
        if mask < 3170 then
          if mask < 3160 then
            ⟨{2, 4, 6, 10, 11}, certificate_3156⟩
          else
            if mask < 3169 then
              ⟨{3, 4, 6, 10, 11}, certificate_3160⟩
            else
              ⟨{0, 5, 6, 10, 11}, certificate_3169⟩
        else
          if mask < 3176 then
            if mask < 3172 then
              ⟨{1, 5, 6, 10, 11}, certificate_3170⟩
            else
              ⟨{2, 5, 6, 10, 11}, certificate_3172⟩
          else
            if mask < 3184 then
              ⟨{3, 5, 6, 10, 11}, certificate_3176⟩
            else
              ⟨{4, 5, 6, 10, 11}, certificate_3184⟩
      else
        if mask < 3209 then
          if mask < 3205 then
            ⟨{0, 1, 7, 10, 11}, certificate_3203⟩
          else
            if mask < 3206 then
              ⟨{0, 2, 7, 10, 11}, certificate_3205⟩
            else
              ⟨{1, 2, 7, 10, 11}, certificate_3206⟩
        else
          if mask < 3212 then
            if mask < 3210 then
              ⟨{0, 3, 7, 10, 11}, certificate_3209⟩
            else
              ⟨{1, 3, 7, 10, 11}, certificate_3210⟩
          else
            if mask < 3217 then
              ⟨{2, 3, 7, 10, 11}, certificate_3212⟩
            else
              ⟨{0, 4, 7, 10, 11}, certificate_3217⟩
    else
      if mask < 3248 then
        if mask < 3233 then
          if mask < 3220 then
            ⟨{1, 4, 7, 10, 11}, certificate_3218⟩
          else
            if mask < 3224 then
              ⟨{2, 4, 7, 10, 11}, certificate_3220⟩
            else
              ⟨{3, 4, 7, 10, 11}, certificate_3224⟩
        else
          if mask < 3236 then
            if mask < 3234 then
              ⟨{0, 5, 7, 10, 11}, certificate_3233⟩
            else
              ⟨{1, 5, 7, 10, 11}, certificate_3234⟩
          else
            if mask < 3240 then
              ⟨{2, 5, 7, 10, 11}, certificate_3236⟩
            else
              ⟨{3, 5, 7, 10, 11}, certificate_3240⟩
      else
        if mask < 3268 then
          if mask < 3265 then
            ⟨{4, 5, 7, 10, 11}, certificate_3248⟩
          else
            if mask < 3266 then
              ⟨{0, 6, 7, 10, 11}, certificate_3265⟩
            else
              ⟨{1, 6, 7, 10, 11}, certificate_3266⟩
        else
          if mask < 3280 then
            if mask < 3272 then
              ⟨{2, 6, 7, 10, 11}, certificate_3268⟩
            else
              ⟨{3, 6, 7, 10, 11}, certificate_3272⟩
          else
            if mask < 3296 then
              ⟨{4, 6, 7, 10, 11}, certificate_3280⟩
            else
              ⟨{5, 6, 7, 10, 11}, certificate_3296⟩
end AMEProbe.BinaryDirect.Batch12
#print axioms AMEProbe.BinaryDirect.Batch12.lookup
