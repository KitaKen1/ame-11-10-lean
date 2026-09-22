import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch11
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_2819 : Certificate {0, 1, 8, 9, 11} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 8, 9, 11} =
      !![0, 0, 1, 1, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2821 : Certificate {0, 2, 8, 9, 11} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 8, 9, 11} =
      !![0, 0, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2822 : Certificate {1, 2, 8, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 8, 9, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2825 : Certificate {0, 3, 8, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 8, 9, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2826 : Certificate {1, 3, 8, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2828 : Certificate {2, 3, 8, 9, 11} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2833 : Certificate {0, 4, 8, 9, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 8, 9, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      1, 0, 1, 1, 0;
      1, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2834 : Certificate {1, 4, 8, 9, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 1, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 8, 9, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2836 : Certificate {2, 4, 8, 9, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 8, 9, 11} =
      !![0, 0, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2840 : Certificate {3, 4, 8, 9, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 8, 9, 11} =
      !![1, 0, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2849 : Certificate {0, 5, 8, 9, 11} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 8, 9, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2850 : Certificate {1, 5, 8, 9, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      1, 0, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2852 : Certificate {2, 5, 8, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2856 : Certificate {3, 5, 8, 9, 11} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 8, 9, 11} =
      !![1, 1, 0, 1, 0;
      0, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2864 : Certificate {4, 5, 8, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2881 : Certificate {0, 6, 8, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 6, 8, 9, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      1, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2882 : Certificate {1, 6, 8, 9, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 6, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      0, 1, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2884 : Certificate {2, 6, 8, 9, 11} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 6, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2888 : Certificate {3, 6, 8, 9, 11} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 6, 8, 9, 11} =
      !![1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2896 : Certificate {4, 6, 8, 9, 11} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 6, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2912 : Certificate {5, 6, 8, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      1, 0, 0, 1, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 6, 8, 9, 11} =
      !![1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2945 : Certificate {0, 7, 8, 9, 11} := by
  refine ⟨!![1, 1, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 7, 8, 9, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2946 : Certificate {1, 7, 8, 9, 11} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 7, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      1, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2948 : Certificate {2, 7, 8, 9, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 7, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2952 : Certificate {3, 7, 8, 9, 11} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 7, 8, 9, 11} =
      !![1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2960 : Certificate {4, 7, 8, 9, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 1;
      1, 1, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 7, 8, 9, 11} =
      !![0, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2976 : Certificate {5, 7, 8, 9, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 7, 8, 9, 11} =
      !![1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3008 : Certificate {6, 7, 8, 9, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {6, 7, 8, 9, 11} =
      !![1, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 2864 then
    if mask < 2834 then
      if mask < 2825 then
        if mask < 2821 then
          ⟨{0, 1, 8, 9, 11}, certificate_2819⟩
        else
          if mask < 2822 then
            ⟨{0, 2, 8, 9, 11}, certificate_2821⟩
          else
            ⟨{1, 2, 8, 9, 11}, certificate_2822⟩
      else
        if mask < 2828 then
          if mask < 2826 then
            ⟨{0, 3, 8, 9, 11}, certificate_2825⟩
          else
            ⟨{1, 3, 8, 9, 11}, certificate_2826⟩
        else
          if mask < 2833 then
            ⟨{2, 3, 8, 9, 11}, certificate_2828⟩
          else
            ⟨{0, 4, 8, 9, 11}, certificate_2833⟩
    else
      if mask < 2849 then
        if mask < 2836 then
          ⟨{1, 4, 8, 9, 11}, certificate_2834⟩
        else
          if mask < 2840 then
            ⟨{2, 4, 8, 9, 11}, certificate_2836⟩
          else
            ⟨{3, 4, 8, 9, 11}, certificate_2840⟩
      else
        if mask < 2852 then
          if mask < 2850 then
            ⟨{0, 5, 8, 9, 11}, certificate_2849⟩
          else
            ⟨{1, 5, 8, 9, 11}, certificate_2850⟩
        else
          if mask < 2856 then
            ⟨{2, 5, 8, 9, 11}, certificate_2852⟩
          else
            ⟨{3, 5, 8, 9, 11}, certificate_2856⟩
  else
    if mask < 2945 then
      if mask < 2884 then
        if mask < 2881 then
          ⟨{4, 5, 8, 9, 11}, certificate_2864⟩
        else
          if mask < 2882 then
            ⟨{0, 6, 8, 9, 11}, certificate_2881⟩
          else
            ⟨{1, 6, 8, 9, 11}, certificate_2882⟩
      else
        if mask < 2896 then
          if mask < 2888 then
            ⟨{2, 6, 8, 9, 11}, certificate_2884⟩
          else
            ⟨{3, 6, 8, 9, 11}, certificate_2888⟩
        else
          if mask < 2912 then
            ⟨{4, 6, 8, 9, 11}, certificate_2896⟩
          else
            ⟨{5, 6, 8, 9, 11}, certificate_2912⟩
    else
      if mask < 2952 then
        if mask < 2946 then
          ⟨{0, 7, 8, 9, 11}, certificate_2945⟩
        else
          if mask < 2948 then
            ⟨{1, 7, 8, 9, 11}, certificate_2946⟩
          else
            ⟨{2, 7, 8, 9, 11}, certificate_2948⟩
      else
        if mask < 2976 then
          if mask < 2960 then
            ⟨{3, 7, 8, 9, 11}, certificate_2952⟩
          else
            ⟨{4, 7, 8, 9, 11}, certificate_2960⟩
        else
          if mask < 3008 then
            ⟨{5, 7, 8, 9, 11}, certificate_2976⟩
          else
            ⟨{6, 7, 8, 9, 11}, certificate_3008⟩
end AMEProbe.BinaryDirect.Batch11
#print axioms AMEProbe.BinaryDirect.Batch11.lookup
