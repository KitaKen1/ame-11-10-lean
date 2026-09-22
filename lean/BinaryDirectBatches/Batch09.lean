import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch09
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_2311 : Certificate {0, 1, 2, 8, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 8, 11} =
      !![1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2315 : Certificate {0, 1, 3, 8, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 8, 11} =
      !![0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2317 : Certificate {0, 2, 3, 8, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 8, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2318 : Certificate {1, 2, 3, 8, 11} := by
  refine ⟨!![1, 0, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 8, 11} =
      !![0, 0, 1, 0, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2323 : Certificate {0, 1, 4, 8, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 8, 11} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2325 : Certificate {0, 2, 4, 8, 11} := by
  refine ⟨!![1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 8, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 0;
      1, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2326 : Certificate {1, 2, 4, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 1, 0;
      0, 1, 1, 1, 1, 1, 0;
      0, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 8, 11} =
      !![0, 0, 0, 0, 0;
      0, 0, 0, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2329 : Certificate {0, 3, 4, 8, 11} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 8, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2330 : Certificate {1, 3, 4, 8, 11} := by
  refine ⟨!![1, 0, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 1, 1, 0;
      0, 0, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 8, 11} =
      !![0, 1, 0, 0, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2332 : Certificate {2, 3, 4, 8, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      1, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 8, 11} =
      !![0, 1, 0, 0, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2339 : Certificate {0, 1, 5, 8, 11} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 8, 11} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2341 : Certificate {0, 2, 5, 8, 11} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 8, 11} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2342 : Certificate {1, 2, 5, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 8, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2345 : Certificate {0, 3, 5, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 8, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2346 : Certificate {1, 3, 5, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2348 : Certificate {2, 3, 5, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2353 : Certificate {0, 4, 5, 8, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 8, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2354 : Certificate {1, 4, 5, 8, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 8, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2356 : Certificate {2, 4, 5, 8, 11} := by
  refine ⟨!![0, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 8, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2360 : Certificate {3, 4, 5, 8, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 8, 11} =
      !![1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2371 : Certificate {0, 1, 6, 8, 11} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 6, 8, 11} =
      !![0, 0, 0, 1, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2373 : Certificate {0, 2, 6, 8, 11} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 6, 8, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2374 : Certificate {1, 2, 6, 8, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 6, 8, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2377 : Certificate {0, 3, 6, 8, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 6, 8, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2378 : Certificate {1, 3, 6, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 1;
      1, 0, 0, 0, 1, 0, 1;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 6, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2380 : Certificate {2, 3, 6, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 6, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2385 : Certificate {0, 4, 6, 8, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 6, 8, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2386 : Certificate {1, 4, 6, 8, 11} := by
  refine ⟨!![1, 0, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 6, 8, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2388 : Certificate {2, 4, 6, 8, 11} := by
  refine ⟨!![0, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 6, 8, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2392 : Certificate {3, 4, 6, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 1;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      1, 1, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 6, 8, 11} =
      !![1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2401 : Certificate {0, 5, 6, 8, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 6, 8, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2402 : Certificate {1, 5, 6, 8, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 6, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 0, 1, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2404 : Certificate {2, 5, 6, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 1, 0;
      0, 0, 0, 0, 1, 1, 0;
      0, 1, 0, 0, 1, 1, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 6, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2408 : Certificate {3, 5, 6, 8, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 6, 8, 11} =
      !![1, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2416 : Certificate {4, 5, 6, 8, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 6, 8, 11} =
      !![0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2435 : Certificate {0, 1, 7, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 7, 8, 11} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2437 : Certificate {0, 2, 7, 8, 11} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      0, 0, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 7, 8, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2438 : Certificate {1, 2, 7, 8, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 7, 8, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2441 : Certificate {0, 3, 7, 8, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 7, 8, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2442 : Certificate {1, 3, 7, 8, 11} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 7, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2444 : Certificate {2, 3, 7, 8, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 7, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2449 : Certificate {0, 4, 7, 8, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 7, 8, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2450 : Certificate {1, 4, 7, 8, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 7, 8, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2452 : Certificate {2, 4, 7, 8, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 7, 8, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2456 : Certificate {3, 4, 7, 8, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 7, 8, 11} =
      !![1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2465 : Certificate {0, 5, 7, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 7, 8, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      1, 0, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2466 : Certificate {1, 5, 7, 8, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 7, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2468 : Certificate {2, 5, 7, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 7, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2472 : Certificate {3, 5, 7, 8, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 7, 8, 11} =
      !![1, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2480 : Certificate {4, 5, 7, 8, 11} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 7, 8, 11} =
      !![0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2497 : Certificate {0, 6, 7, 8, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 6, 7, 8, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2498 : Certificate {1, 6, 7, 8, 11} := by
  refine ⟨!![1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 6, 7, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2500 : Certificate {2, 6, 7, 8, 11} := by
  refine ⟨!![1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 6, 7, 8, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2504 : Certificate {3, 6, 7, 8, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 6, 7, 8, 11} =
      !![1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2512 : Certificate {4, 6, 7, 8, 11} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 6, 7, 8, 11} =
      !![0, 1, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2528 : Certificate {5, 6, 7, 8, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 6, 7, 8, 11} =
      !![1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 2388 then
    if mask < 2346 then
      if mask < 2329 then
        if mask < 2318 then
          if mask < 2315 then
            ⟨{0, 1, 2, 8, 11}, certificate_2311⟩
          else
            if mask < 2317 then
              ⟨{0, 1, 3, 8, 11}, certificate_2315⟩
            else
              ⟨{0, 2, 3, 8, 11}, certificate_2317⟩
        else
          if mask < 2325 then
            if mask < 2323 then
              ⟨{1, 2, 3, 8, 11}, certificate_2318⟩
            else
              ⟨{0, 1, 4, 8, 11}, certificate_2323⟩
          else
            if mask < 2326 then
              ⟨{0, 2, 4, 8, 11}, certificate_2325⟩
            else
              ⟨{1, 2, 4, 8, 11}, certificate_2326⟩
      else
        if mask < 2339 then
          if mask < 2330 then
            ⟨{0, 3, 4, 8, 11}, certificate_2329⟩
          else
            if mask < 2332 then
              ⟨{1, 3, 4, 8, 11}, certificate_2330⟩
            else
              ⟨{2, 3, 4, 8, 11}, certificate_2332⟩
        else
          if mask < 2342 then
            if mask < 2341 then
              ⟨{0, 1, 5, 8, 11}, certificate_2339⟩
            else
              ⟨{0, 2, 5, 8, 11}, certificate_2341⟩
          else
            if mask < 2345 then
              ⟨{1, 2, 5, 8, 11}, certificate_2342⟩
            else
              ⟨{0, 3, 5, 8, 11}, certificate_2345⟩
    else
      if mask < 2373 then
        if mask < 2354 then
          if mask < 2348 then
            ⟨{1, 3, 5, 8, 11}, certificate_2346⟩
          else
            if mask < 2353 then
              ⟨{2, 3, 5, 8, 11}, certificate_2348⟩
            else
              ⟨{0, 4, 5, 8, 11}, certificate_2353⟩
        else
          if mask < 2360 then
            if mask < 2356 then
              ⟨{1, 4, 5, 8, 11}, certificate_2354⟩
            else
              ⟨{2, 4, 5, 8, 11}, certificate_2356⟩
          else
            if mask < 2371 then
              ⟨{3, 4, 5, 8, 11}, certificate_2360⟩
            else
              ⟨{0, 1, 6, 8, 11}, certificate_2371⟩
      else
        if mask < 2378 then
          if mask < 2374 then
            ⟨{0, 2, 6, 8, 11}, certificate_2373⟩
          else
            if mask < 2377 then
              ⟨{1, 2, 6, 8, 11}, certificate_2374⟩
            else
              ⟨{0, 3, 6, 8, 11}, certificate_2377⟩
        else
          if mask < 2385 then
            if mask < 2380 then
              ⟨{1, 3, 6, 8, 11}, certificate_2378⟩
            else
              ⟨{2, 3, 6, 8, 11}, certificate_2380⟩
          else
            if mask < 2386 then
              ⟨{0, 4, 6, 8, 11}, certificate_2385⟩
            else
              ⟨{1, 4, 6, 8, 11}, certificate_2386⟩
  else
    if mask < 2450 then
      if mask < 2435 then
        if mask < 2402 then
          if mask < 2392 then
            ⟨{2, 4, 6, 8, 11}, certificate_2388⟩
          else
            if mask < 2401 then
              ⟨{3, 4, 6, 8, 11}, certificate_2392⟩
            else
              ⟨{0, 5, 6, 8, 11}, certificate_2401⟩
        else
          if mask < 2408 then
            if mask < 2404 then
              ⟨{1, 5, 6, 8, 11}, certificate_2402⟩
            else
              ⟨{2, 5, 6, 8, 11}, certificate_2404⟩
          else
            if mask < 2416 then
              ⟨{3, 5, 6, 8, 11}, certificate_2408⟩
            else
              ⟨{4, 5, 6, 8, 11}, certificate_2416⟩
      else
        if mask < 2441 then
          if mask < 2437 then
            ⟨{0, 1, 7, 8, 11}, certificate_2435⟩
          else
            if mask < 2438 then
              ⟨{0, 2, 7, 8, 11}, certificate_2437⟩
            else
              ⟨{1, 2, 7, 8, 11}, certificate_2438⟩
        else
          if mask < 2444 then
            if mask < 2442 then
              ⟨{0, 3, 7, 8, 11}, certificate_2441⟩
            else
              ⟨{1, 3, 7, 8, 11}, certificate_2442⟩
          else
            if mask < 2449 then
              ⟨{2, 3, 7, 8, 11}, certificate_2444⟩
            else
              ⟨{0, 4, 7, 8, 11}, certificate_2449⟩
    else
      if mask < 2480 then
        if mask < 2465 then
          if mask < 2452 then
            ⟨{1, 4, 7, 8, 11}, certificate_2450⟩
          else
            if mask < 2456 then
              ⟨{2, 4, 7, 8, 11}, certificate_2452⟩
            else
              ⟨{3, 4, 7, 8, 11}, certificate_2456⟩
        else
          if mask < 2468 then
            if mask < 2466 then
              ⟨{0, 5, 7, 8, 11}, certificate_2465⟩
            else
              ⟨{1, 5, 7, 8, 11}, certificate_2466⟩
          else
            if mask < 2472 then
              ⟨{2, 5, 7, 8, 11}, certificate_2468⟩
            else
              ⟨{3, 5, 7, 8, 11}, certificate_2472⟩
      else
        if mask < 2500 then
          if mask < 2497 then
            ⟨{4, 5, 7, 8, 11}, certificate_2480⟩
          else
            if mask < 2498 then
              ⟨{0, 6, 7, 8, 11}, certificate_2497⟩
            else
              ⟨{1, 6, 7, 8, 11}, certificate_2498⟩
        else
          if mask < 2512 then
            if mask < 2504 then
              ⟨{2, 6, 7, 8, 11}, certificate_2500⟩
            else
              ⟨{3, 6, 7, 8, 11}, certificate_2504⟩
          else
            if mask < 2528 then
              ⟨{4, 6, 7, 8, 11}, certificate_2512⟩
            else
              ⟨{5, 6, 7, 8, 11}, certificate_2528⟩
end AMEProbe.BinaryDirect.Batch09
#print axioms AMEProbe.BinaryDirect.Batch09.lookup
