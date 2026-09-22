import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch13
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_3331 : Certificate {0, 1, 8, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 8, 10, 11} =
      !![0, 0, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3333 : Certificate {0, 2, 8, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 8, 10, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3334 : Certificate {1, 2, 8, 10, 11} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 8, 10, 11} =
      !![0, 0, 0, 0, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3337 : Certificate {0, 3, 8, 10, 11} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 1;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 1;
      1, 1, 0, 0, 1, 0, 1;
      0, 0, 0, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 8, 10, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3338 : Certificate {1, 3, 8, 10, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3340 : Certificate {2, 3, 8, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3345 : Certificate {0, 4, 8, 10, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 8, 10, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 1, 1, 0;
      1, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3346 : Certificate {1, 4, 8, 10, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 1, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 8, 10, 11} =
      !![0, 0, 0, 0, 0;
      0, 0, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3348 : Certificate {2, 4, 8, 10, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 1, 0;
      0, 1, 0, 1, 1, 1, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 8, 10, 11} =
      !![0, 0, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3352 : Certificate {3, 4, 8, 10, 11} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 8, 10, 11} =
      !![1, 0, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3361 : Certificate {0, 5, 8, 10, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 8, 10, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3362 : Certificate {1, 5, 8, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3364 : Certificate {2, 5, 8, 10, 11} := by
  refine ⟨!![0, 0, 0, 1, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3368 : Certificate {3, 5, 8, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 8, 10, 11} =
      !![1, 1, 0, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3376 : Certificate {4, 5, 8, 10, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3393 : Certificate {0, 6, 8, 10, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 6, 8, 10, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3394 : Certificate {1, 6, 8, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 6, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      0, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3396 : Certificate {2, 6, 8, 10, 11} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 1;
      0, 1, 0, 1, 1, 0, 1;
      0, 1, 0, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 6, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3400 : Certificate {3, 6, 8, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 6, 8, 10, 11} =
      !![1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3408 : Certificate {4, 6, 8, 10, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 6, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3424 : Certificate {5, 6, 8, 10, 11} := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 1, 1;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 6, 8, 10, 11} =
      !![1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3457 : Certificate {0, 7, 8, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 7, 8, 10, 11} =
      !![0, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3458 : Certificate {1, 7, 8, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 7, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      1, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3460 : Certificate {2, 7, 8, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 7, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3464 : Certificate {3, 7, 8, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 7, 8, 10, 11} =
      !![1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3472 : Certificate {4, 7, 8, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 7, 8, 10, 11} =
      !![0, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3488 : Certificate {5, 7, 8, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 7, 8, 10, 11} =
      !![1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3520 : Certificate {6, 7, 8, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {6, 7, 8, 10, 11} =
      !![1, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 3376 then
    if mask < 3346 then
      if mask < 3337 then
        if mask < 3333 then
          ⟨{0, 1, 8, 10, 11}, certificate_3331⟩
        else
          if mask < 3334 then
            ⟨{0, 2, 8, 10, 11}, certificate_3333⟩
          else
            ⟨{1, 2, 8, 10, 11}, certificate_3334⟩
      else
        if mask < 3340 then
          if mask < 3338 then
            ⟨{0, 3, 8, 10, 11}, certificate_3337⟩
          else
            ⟨{1, 3, 8, 10, 11}, certificate_3338⟩
        else
          if mask < 3345 then
            ⟨{2, 3, 8, 10, 11}, certificate_3340⟩
          else
            ⟨{0, 4, 8, 10, 11}, certificate_3345⟩
    else
      if mask < 3361 then
        if mask < 3348 then
          ⟨{1, 4, 8, 10, 11}, certificate_3346⟩
        else
          if mask < 3352 then
            ⟨{2, 4, 8, 10, 11}, certificate_3348⟩
          else
            ⟨{3, 4, 8, 10, 11}, certificate_3352⟩
      else
        if mask < 3364 then
          if mask < 3362 then
            ⟨{0, 5, 8, 10, 11}, certificate_3361⟩
          else
            ⟨{1, 5, 8, 10, 11}, certificate_3362⟩
        else
          if mask < 3368 then
            ⟨{2, 5, 8, 10, 11}, certificate_3364⟩
          else
            ⟨{3, 5, 8, 10, 11}, certificate_3368⟩
  else
    if mask < 3457 then
      if mask < 3396 then
        if mask < 3393 then
          ⟨{4, 5, 8, 10, 11}, certificate_3376⟩
        else
          if mask < 3394 then
            ⟨{0, 6, 8, 10, 11}, certificate_3393⟩
          else
            ⟨{1, 6, 8, 10, 11}, certificate_3394⟩
      else
        if mask < 3408 then
          if mask < 3400 then
            ⟨{2, 6, 8, 10, 11}, certificate_3396⟩
          else
            ⟨{3, 6, 8, 10, 11}, certificate_3400⟩
        else
          if mask < 3424 then
            ⟨{4, 6, 8, 10, 11}, certificate_3408⟩
          else
            ⟨{5, 6, 8, 10, 11}, certificate_3424⟩
    else
      if mask < 3464 then
        if mask < 3458 then
          ⟨{0, 7, 8, 10, 11}, certificate_3457⟩
        else
          if mask < 3460 then
            ⟨{1, 7, 8, 10, 11}, certificate_3458⟩
          else
            ⟨{2, 7, 8, 10, 11}, certificate_3460⟩
      else
        if mask < 3488 then
          if mask < 3472 then
            ⟨{3, 7, 8, 10, 11}, certificate_3464⟩
          else
            ⟨{4, 7, 8, 10, 11}, certificate_3472⟩
        else
          if mask < 3520 then
            ⟨{5, 7, 8, 10, 11}, certificate_3488⟩
          else
            ⟨{6, 7, 8, 10, 11}, certificate_3520⟩
end AMEProbe.BinaryDirect.Batch13
#print axioms AMEProbe.BinaryDirect.Batch13.lookup
