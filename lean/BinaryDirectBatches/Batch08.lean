import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch08
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_2063 : Certificate {0, 1, 2, 3, 11} := by
  refine ⟨!![1, 0, 0, 0, 1, 1, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 1, 1, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 3, 11} =
      !![0, 1, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2071 : Certificate {0, 1, 2, 4, 11} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 4, 11} =
      !![1, 0, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2075 : Certificate {0, 1, 3, 4, 11} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      0, 1, 1, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 4, 11} =
      !![0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2077 : Certificate {0, 2, 3, 4, 11} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 4, 11} =
      !![0, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2078 : Certificate {1, 2, 3, 4, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 4, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2087 : Certificate {0, 1, 2, 5, 11} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 5, 11} =
      !![1, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2091 : Certificate {0, 1, 3, 5, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 1;
      1, 0, 1, 1, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 5, 11} =
      !![0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2093 : Certificate {0, 2, 3, 5, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 5, 11} =
      !![0, 0, 0, 0, 0;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 1;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2094 : Certificate {1, 2, 3, 5, 11} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 5, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 1;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2099 : Certificate {0, 1, 4, 5, 11} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 5, 11} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2101 : Certificate {0, 2, 4, 5, 11} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 5, 11} =
      !![0, 0, 1, 0, 0;
      1, 0, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 1;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2102 : Certificate {1, 2, 4, 5, 11} := by
  refine ⟨!![0, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 5, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 1;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2105 : Certificate {0, 3, 4, 5, 11} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 5, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2106 : Certificate {1, 3, 4, 5, 11} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 5, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 1;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2108 : Certificate {2, 3, 4, 5, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 5, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2119 : Certificate {0, 1, 2, 6, 11} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 1;
      0, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 6, 11} =
      !![1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2123 : Certificate {0, 1, 3, 6, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 6, 11} =
      !![0, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2125 : Certificate {0, 2, 3, 6, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 1, 0;
      1, 0, 1, 0, 1, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 6, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2126 : Certificate {1, 2, 3, 6, 11} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1, 0;
      0, 1, 0, 0, 1, 1, 0;
      1, 0, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 6, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2131 : Certificate {0, 1, 4, 6, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 6, 11} =
      !![0, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2133 : Certificate {0, 2, 4, 6, 11} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 6, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2134 : Certificate {1, 2, 4, 6, 11} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 1;
      0, 0, 1, 0, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 6, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2137 : Certificate {0, 3, 4, 6, 11} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 6, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 0, 1;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2138 : Certificate {1, 3, 4, 6, 11} := by
  refine ⟨!![1, 0, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 1, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 1, 1, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 6, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 1, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2140 : Certificate {2, 3, 4, 6, 11} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 6, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2147 : Certificate {0, 1, 5, 6, 11} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 6, 11} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2149 : Certificate {0, 2, 5, 6, 11} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 6, 11} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2150 : Certificate {1, 2, 5, 6, 11} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 6, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2153 : Certificate {0, 3, 5, 6, 11} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 6, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2154 : Certificate {1, 3, 5, 6, 11} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 6, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2156 : Certificate {2, 3, 5, 6, 11} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 6, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2161 : Certificate {0, 4, 5, 6, 11} := by
  refine ⟨!![1, 0, 0, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 1;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 6, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2162 : Certificate {1, 4, 5, 6, 11} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 6, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2164 : Certificate {2, 4, 5, 6, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 6, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2168 : Certificate {3, 4, 5, 6, 11} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 6, 11} =
      !![1, 0, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2183 : Certificate {0, 1, 2, 7, 11} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 7, 11} =
      !![1, 0, 0, 0, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2187 : Certificate {0, 1, 3, 7, 11} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 7, 11} =
      !![0, 0, 0, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 1;
      0, 1, 1, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2189 : Certificate {0, 2, 3, 7, 11} := by
  refine ⟨!![0, 0, 1, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 7, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 1;
      0, 1, 1, 0, 1;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2190 : Certificate {1, 2, 3, 7, 11} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 1, 0;
      0, 1, 0, 0, 1, 1, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 7, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 1, 0, 1;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2195 : Certificate {0, 1, 4, 7, 11} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 7, 11} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2197 : Certificate {0, 2, 4, 7, 11} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 7, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2198 : Certificate {1, 2, 4, 7, 11} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 7, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2201 : Certificate {0, 3, 4, 7, 11} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 7, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2202 : Certificate {1, 3, 4, 7, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 7, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2204 : Certificate {2, 3, 4, 7, 11} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 7, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2211 : Certificate {0, 1, 5, 7, 11} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 7, 11} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2213 : Certificate {0, 2, 5, 7, 11} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 7, 11} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 0, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2214 : Certificate {1, 2, 5, 7, 11} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 1;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 7, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 0, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2217 : Certificate {0, 3, 5, 7, 11} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 7, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2218 : Certificate {1, 3, 5, 7, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 7, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2220 : Certificate {2, 3, 5, 7, 11} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 7, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2225 : Certificate {0, 4, 5, 7, 11} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 7, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 0;
      1, 0, 0, 0, 1;
      0, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2226 : Certificate {1, 4, 5, 7, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 7, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2228 : Certificate {2, 4, 5, 7, 11} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 7, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 0, 0, 0;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2232 : Certificate {3, 4, 5, 7, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 7, 11} =
      !![1, 0, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2243 : Certificate {0, 1, 6, 7, 11} := by
  refine ⟨!![1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 6, 7, 11} =
      !![0, 0, 0, 1, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2245 : Certificate {0, 2, 6, 7, 11} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 6, 7, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2246 : Certificate {1, 2, 6, 7, 11} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 6, 7, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 0, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2249 : Certificate {0, 3, 6, 7, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 0, 0, 1, 1, 1, 0;
      1, 1, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 6, 7, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2250 : Certificate {1, 3, 6, 7, 11} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 6, 7, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2252 : Certificate {2, 3, 6, 7, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      1, 1, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 6, 7, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2257 : Certificate {0, 4, 6, 7, 11} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 6, 7, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 0;
      1, 0, 0, 0, 1;
      0, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2258 : Certificate {1, 4, 6, 7, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 6, 7, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 1, 0, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2260 : Certificate {2, 4, 6, 7, 11} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 6, 7, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 0;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2264 : Certificate {3, 4, 6, 7, 11} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 6, 7, 11} =
      !![1, 0, 1, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2273 : Certificate {0, 5, 6, 7, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 6, 7, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2274 : Certificate {1, 5, 6, 7, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 1;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 6, 7, 11} =
      !![0, 1, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 0, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2276 : Certificate {2, 5, 6, 7, 11} := by
  refine ⟨!![1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 6, 7, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2280 : Certificate {3, 5, 6, 7, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 6, 7, 11} =
      !![1, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2288 : Certificate {4, 5, 6, 7, 11} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 6, 7, 11} =
      !![0, 1, 1, 1, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 2183 then
    if mask < 2125 then
      if mask < 2094 then
        if mask < 2078 then
          if mask < 2075 then
            if mask < 2071 then
              ⟨{0, 1, 2, 3, 11}, certificate_2063⟩
            else
              ⟨{0, 1, 2, 4, 11}, certificate_2071⟩
          else
            if mask < 2077 then
              ⟨{0, 1, 3, 4, 11}, certificate_2075⟩
            else
              ⟨{0, 2, 3, 4, 11}, certificate_2077⟩
        else
          if mask < 2091 then
            if mask < 2087 then
              ⟨{1, 2, 3, 4, 11}, certificate_2078⟩
            else
              ⟨{0, 1, 2, 5, 11}, certificate_2087⟩
          else
            if mask < 2093 then
              ⟨{0, 1, 3, 5, 11}, certificate_2091⟩
            else
              ⟨{0, 2, 3, 5, 11}, certificate_2093⟩
      else
        if mask < 2105 then
          if mask < 2101 then
            if mask < 2099 then
              ⟨{1, 2, 3, 5, 11}, certificate_2094⟩
            else
              ⟨{0, 1, 4, 5, 11}, certificate_2099⟩
          else
            if mask < 2102 then
              ⟨{0, 2, 4, 5, 11}, certificate_2101⟩
            else
              ⟨{1, 2, 4, 5, 11}, certificate_2102⟩
        else
          if mask < 2108 then
            if mask < 2106 then
              ⟨{0, 3, 4, 5, 11}, certificate_2105⟩
            else
              ⟨{1, 3, 4, 5, 11}, certificate_2106⟩
          else
            if mask < 2119 then
              ⟨{2, 3, 4, 5, 11}, certificate_2108⟩
            else
              if mask < 2123 then
                ⟨{0, 1, 2, 6, 11}, certificate_2119⟩
              else
                ⟨{0, 1, 3, 6, 11}, certificate_2123⟩
    else
      if mask < 2149 then
        if mask < 2134 then
          if mask < 2131 then
            if mask < 2126 then
              ⟨{0, 2, 3, 6, 11}, certificate_2125⟩
            else
              ⟨{1, 2, 3, 6, 11}, certificate_2126⟩
          else
            if mask < 2133 then
              ⟨{0, 1, 4, 6, 11}, certificate_2131⟩
            else
              ⟨{0, 2, 4, 6, 11}, certificate_2133⟩
        else
          if mask < 2138 then
            if mask < 2137 then
              ⟨{1, 2, 4, 6, 11}, certificate_2134⟩
            else
              ⟨{0, 3, 4, 6, 11}, certificate_2137⟩
          else
            if mask < 2140 then
              ⟨{1, 3, 4, 6, 11}, certificate_2138⟩
            else
              if mask < 2147 then
                ⟨{2, 3, 4, 6, 11}, certificate_2140⟩
              else
                ⟨{0, 1, 5, 6, 11}, certificate_2147⟩
      else
        if mask < 2156 then
          if mask < 2153 then
            if mask < 2150 then
              ⟨{0, 2, 5, 6, 11}, certificate_2149⟩
            else
              ⟨{1, 2, 5, 6, 11}, certificate_2150⟩
          else
            if mask < 2154 then
              ⟨{0, 3, 5, 6, 11}, certificate_2153⟩
            else
              ⟨{1, 3, 5, 6, 11}, certificate_2154⟩
        else
          if mask < 2162 then
            if mask < 2161 then
              ⟨{2, 3, 5, 6, 11}, certificate_2156⟩
            else
              ⟨{0, 4, 5, 6, 11}, certificate_2161⟩
          else
            if mask < 2164 then
              ⟨{1, 4, 5, 6, 11}, certificate_2162⟩
            else
              if mask < 2168 then
                ⟨{2, 4, 5, 6, 11}, certificate_2164⟩
              else
                ⟨{3, 4, 5, 6, 11}, certificate_2168⟩
  else
    if mask < 2226 then
      if mask < 2202 then
        if mask < 2195 then
          if mask < 2189 then
            if mask < 2187 then
              ⟨{0, 1, 2, 7, 11}, certificate_2183⟩
            else
              ⟨{0, 1, 3, 7, 11}, certificate_2187⟩
          else
            if mask < 2190 then
              ⟨{0, 2, 3, 7, 11}, certificate_2189⟩
            else
              ⟨{1, 2, 3, 7, 11}, certificate_2190⟩
        else
          if mask < 2198 then
            if mask < 2197 then
              ⟨{0, 1, 4, 7, 11}, certificate_2195⟩
            else
              ⟨{0, 2, 4, 7, 11}, certificate_2197⟩
          else
            if mask < 2201 then
              ⟨{1, 2, 4, 7, 11}, certificate_2198⟩
            else
              ⟨{0, 3, 4, 7, 11}, certificate_2201⟩
      else
        if mask < 2214 then
          if mask < 2211 then
            if mask < 2204 then
              ⟨{1, 3, 4, 7, 11}, certificate_2202⟩
            else
              ⟨{2, 3, 4, 7, 11}, certificate_2204⟩
          else
            if mask < 2213 then
              ⟨{0, 1, 5, 7, 11}, certificate_2211⟩
            else
              ⟨{0, 2, 5, 7, 11}, certificate_2213⟩
        else
          if mask < 2218 then
            if mask < 2217 then
              ⟨{1, 2, 5, 7, 11}, certificate_2214⟩
            else
              ⟨{0, 3, 5, 7, 11}, certificate_2217⟩
          else
            if mask < 2220 then
              ⟨{1, 3, 5, 7, 11}, certificate_2218⟩
            else
              if mask < 2225 then
                ⟨{2, 3, 5, 7, 11}, certificate_2220⟩
              else
                ⟨{0, 4, 5, 7, 11}, certificate_2225⟩
    else
      if mask < 2257 then
        if mask < 2245 then
          if mask < 2232 then
            if mask < 2228 then
              ⟨{1, 4, 5, 7, 11}, certificate_2226⟩
            else
              ⟨{2, 4, 5, 7, 11}, certificate_2228⟩
          else
            if mask < 2243 then
              ⟨{3, 4, 5, 7, 11}, certificate_2232⟩
            else
              ⟨{0, 1, 6, 7, 11}, certificate_2243⟩
        else
          if mask < 2249 then
            if mask < 2246 then
              ⟨{0, 2, 6, 7, 11}, certificate_2245⟩
            else
              ⟨{1, 2, 6, 7, 11}, certificate_2246⟩
          else
            if mask < 2250 then
              ⟨{0, 3, 6, 7, 11}, certificate_2249⟩
            else
              if mask < 2252 then
                ⟨{1, 3, 6, 7, 11}, certificate_2250⟩
              else
                ⟨{2, 3, 6, 7, 11}, certificate_2252⟩
      else
        if mask < 2273 then
          if mask < 2260 then
            if mask < 2258 then
              ⟨{0, 4, 6, 7, 11}, certificate_2257⟩
            else
              ⟨{1, 4, 6, 7, 11}, certificate_2258⟩
          else
            if mask < 2264 then
              ⟨{2, 4, 6, 7, 11}, certificate_2260⟩
            else
              ⟨{3, 4, 6, 7, 11}, certificate_2264⟩
        else
          if mask < 2276 then
            if mask < 2274 then
              ⟨{0, 5, 6, 7, 11}, certificate_2273⟩
            else
              ⟨{1, 5, 6, 7, 11}, certificate_2274⟩
          else
            if mask < 2280 then
              ⟨{2, 5, 6, 7, 11}, certificate_2276⟩
            else
              if mask < 2288 then
                ⟨{3, 5, 6, 7, 11}, certificate_2280⟩
              else
                ⟨{4, 5, 6, 7, 11}, certificate_2288⟩
end AMEProbe.BinaryDirect.Batch08
#print axioms AMEProbe.BinaryDirect.Batch08.lookup
