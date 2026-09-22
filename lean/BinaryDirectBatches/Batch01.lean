import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch01
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_271 : Certificate {0, 1, 2, 3, 8} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 3, 8} =
      !![0, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_279 : Certificate {0, 1, 2, 4, 8} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 4, 8} =
      !![1, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_283 : Certificate {0, 1, 3, 4, 8} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 4, 8} =
      !![0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_285 : Certificate {0, 2, 3, 4, 8} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 1, 0;
      0, 1, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 4, 8} =
      !![0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_286 : Certificate {1, 2, 3, 4, 8} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 4, 8} =
      !![0, 0, 1, 0, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_295 : Certificate {0, 1, 2, 5, 8} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 5, 8} =
      !![1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_299 : Certificate {0, 1, 3, 5, 8} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 5, 8} =
      !![0, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_301 : Certificate {0, 2, 3, 5, 8} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 5, 8} =
      !![0, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_302 : Certificate {1, 2, 3, 5, 8} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 5, 8} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_307 : Certificate {0, 1, 4, 5, 8} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 5, 8} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_309 : Certificate {0, 2, 4, 5, 8} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 5, 8} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_310 : Certificate {1, 2, 4, 5, 8} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 5, 8} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_313 : Certificate {0, 3, 4, 5, 8} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 5, 8} =
      !![0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_314 : Certificate {1, 3, 4, 5, 8} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1;
      1, 0, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 5, 8} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_316 : Certificate {2, 3, 4, 5, 8} := by
  refine ⟨!![1, 0, 0, 1, 0, 1, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 5, 8} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_327 : Certificate {0, 1, 2, 6, 8} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 6, 8} =
      !![1, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_331 : Certificate {0, 1, 3, 6, 8} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 6, 8} =
      !![0, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_333 : Certificate {0, 2, 3, 6, 8} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 6, 8} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 0;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_334 : Certificate {1, 2, 3, 6, 8} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 6, 8} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_339 : Certificate {0, 1, 4, 6, 8} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 6, 8} =
      !![0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_341 : Certificate {0, 2, 4, 6, 8} := by
  refine ⟨!![1, 1, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 6, 8} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_342 : Certificate {1, 2, 4, 6, 8} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 6, 8} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_345 : Certificate {0, 3, 4, 6, 8} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 6, 8} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_346 : Certificate {1, 3, 4, 6, 8} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 6, 8} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_348 : Certificate {2, 3, 4, 6, 8} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 6, 8} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_355 : Certificate {0, 1, 5, 6, 8} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 6, 8} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 0, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_357 : Certificate {0, 2, 5, 6, 8} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 6, 8} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 0, 1, 0, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_358 : Certificate {1, 2, 5, 6, 8} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 6, 8} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_361 : Certificate {0, 3, 5, 6, 8} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 6, 8} =
      !![0, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_362 : Certificate {1, 3, 5, 6, 8} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 6, 8} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_364 : Certificate {2, 3, 5, 6, 8} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 1, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 6, 8} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_369 : Certificate {0, 4, 5, 6, 8} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 1;
      1, 1, 1, 0, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 6, 8} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_370 : Certificate {1, 4, 5, 6, 8} := by
  refine ⟨!![1, 0, 0, 0, 1, 1, 0;
      1, 0, 0, 1, 1, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 6, 8} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_372 : Certificate {2, 4, 5, 6, 8} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 6, 8} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_376 : Certificate {3, 4, 5, 6, 8} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 6, 8} =
      !![1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_391 : Certificate {0, 1, 2, 7, 8} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 7, 8} =
      !![1, 0, 0, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_395 : Certificate {0, 1, 3, 7, 8} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 7, 8} =
      !![0, 0, 0, 1, 1;
      0, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_397 : Certificate {0, 2, 3, 7, 8} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 7, 8} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_398 : Certificate {1, 2, 3, 7, 8} := by
  refine ⟨!![1, 0, 0, 0, 0, 1, 0;
      0, 1, 0, 0, 1, 1, 0;
      0, 1, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0;
      0, 1, 1, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 7, 8} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_403 : Certificate {0, 1, 4, 7, 8} := by
  refine ⟨!![1, 1, 0, 1, 1, 1, 0;
      1, 1, 0, 0, 1, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 0, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 7, 8} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_405 : Certificate {0, 2, 4, 7, 8} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 7, 8} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_406 : Certificate {1, 2, 4, 7, 8} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 7, 8} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_409 : Certificate {0, 3, 4, 7, 8} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 7, 8} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_410 : Certificate {1, 3, 4, 7, 8} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 7, 8} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_412 : Certificate {2, 3, 4, 7, 8} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 7, 8} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_419 : Certificate {0, 1, 5, 7, 8} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 7, 8} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_421 : Certificate {0, 2, 5, 7, 8} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 7, 8} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_422 : Certificate {1, 2, 5, 7, 8} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 7, 8} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_425 : Certificate {0, 3, 5, 7, 8} := by
  refine ⟨!![1, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 7, 8} =
      !![0, 0, 0, 1, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_426 : Certificate {1, 3, 5, 7, 8} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 7, 8} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_428 : Certificate {2, 3, 5, 7, 8} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 7, 8} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_433 : Certificate {0, 4, 5, 7, 8} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 7, 8} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_434 : Certificate {1, 4, 5, 7, 8} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 1;
      0, 1, 0, 0, 1, 0, 1;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 7, 8} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_436 : Certificate {2, 4, 5, 7, 8} := by
  refine ⟨!![1, 0, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 7, 8} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_440 : Certificate {3, 4, 5, 7, 8} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 7, 8} =
      !![1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_451 : Certificate {0, 1, 6, 7, 8} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 6, 7, 8} =
      !![0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_453 : Certificate {0, 2, 6, 7, 8} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 6, 7, 8} =
      !![0, 0, 1, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_454 : Certificate {1, 2, 6, 7, 8} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      0, 0, 0, 1, 0, 0, 1;
      1, 0, 0, 1, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 6, 7, 8} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 0, 0, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_457 : Certificate {0, 3, 6, 7, 8} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 6, 7, 8} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_458 : Certificate {1, 3, 6, 7, 8} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 6, 7, 8} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_460 : Certificate {2, 3, 6, 7, 8} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 6, 7, 8} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_465 : Certificate {0, 4, 6, 7, 8} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 6, 7, 8} =
      !![0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_466 : Certificate {1, 4, 6, 7, 8} := by
  refine ⟨!![1, 0, 0, 0, 1, 1, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 6, 7, 8} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_468 : Certificate {2, 4, 6, 7, 8} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 6, 7, 8} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_472 : Certificate {3, 4, 6, 7, 8} := by
  refine ⟨!![0, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 6, 7, 8} =
      !![1, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_481 : Certificate {0, 5, 6, 7, 8} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 6, 7, 8} =
      !![0, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_482 : Certificate {1, 5, 6, 7, 8} := by
  refine ⟨!![1, 0, 0, 0, 1, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 1, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 6, 7, 8} =
      !![0, 1, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_484 : Certificate {2, 5, 6, 7, 8} := by
  refine ⟨!![1, 0, 0, 0, 1, 1, 0;
      0, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 6, 7, 8} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_488 : Certificate {3, 5, 6, 7, 8} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 6, 7, 8} =
      !![1, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_496 : Certificate {4, 5, 6, 7, 8} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 1;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 1;
      0, 0, 1, 0, 1, 0, 1;
      0, 1, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 6, 7, 8} =
      !![0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 391 then
    if mask < 333 then
      if mask < 302 then
        if mask < 286 then
          if mask < 283 then
            if mask < 279 then
              ⟨{0, 1, 2, 3, 8}, certificate_271⟩
            else
              ⟨{0, 1, 2, 4, 8}, certificate_279⟩
          else
            if mask < 285 then
              ⟨{0, 1, 3, 4, 8}, certificate_283⟩
            else
              ⟨{0, 2, 3, 4, 8}, certificate_285⟩
        else
          if mask < 299 then
            if mask < 295 then
              ⟨{1, 2, 3, 4, 8}, certificate_286⟩
            else
              ⟨{0, 1, 2, 5, 8}, certificate_295⟩
          else
            if mask < 301 then
              ⟨{0, 1, 3, 5, 8}, certificate_299⟩
            else
              ⟨{0, 2, 3, 5, 8}, certificate_301⟩
      else
        if mask < 313 then
          if mask < 309 then
            if mask < 307 then
              ⟨{1, 2, 3, 5, 8}, certificate_302⟩
            else
              ⟨{0, 1, 4, 5, 8}, certificate_307⟩
          else
            if mask < 310 then
              ⟨{0, 2, 4, 5, 8}, certificate_309⟩
            else
              ⟨{1, 2, 4, 5, 8}, certificate_310⟩
        else
          if mask < 316 then
            if mask < 314 then
              ⟨{0, 3, 4, 5, 8}, certificate_313⟩
            else
              ⟨{1, 3, 4, 5, 8}, certificate_314⟩
          else
            if mask < 327 then
              ⟨{2, 3, 4, 5, 8}, certificate_316⟩
            else
              if mask < 331 then
                ⟨{0, 1, 2, 6, 8}, certificate_327⟩
              else
                ⟨{0, 1, 3, 6, 8}, certificate_331⟩
    else
      if mask < 357 then
        if mask < 342 then
          if mask < 339 then
            if mask < 334 then
              ⟨{0, 2, 3, 6, 8}, certificate_333⟩
            else
              ⟨{1, 2, 3, 6, 8}, certificate_334⟩
          else
            if mask < 341 then
              ⟨{0, 1, 4, 6, 8}, certificate_339⟩
            else
              ⟨{0, 2, 4, 6, 8}, certificate_341⟩
        else
          if mask < 346 then
            if mask < 345 then
              ⟨{1, 2, 4, 6, 8}, certificate_342⟩
            else
              ⟨{0, 3, 4, 6, 8}, certificate_345⟩
          else
            if mask < 348 then
              ⟨{1, 3, 4, 6, 8}, certificate_346⟩
            else
              if mask < 355 then
                ⟨{2, 3, 4, 6, 8}, certificate_348⟩
              else
                ⟨{0, 1, 5, 6, 8}, certificate_355⟩
      else
        if mask < 364 then
          if mask < 361 then
            if mask < 358 then
              ⟨{0, 2, 5, 6, 8}, certificate_357⟩
            else
              ⟨{1, 2, 5, 6, 8}, certificate_358⟩
          else
            if mask < 362 then
              ⟨{0, 3, 5, 6, 8}, certificate_361⟩
            else
              ⟨{1, 3, 5, 6, 8}, certificate_362⟩
        else
          if mask < 370 then
            if mask < 369 then
              ⟨{2, 3, 5, 6, 8}, certificate_364⟩
            else
              ⟨{0, 4, 5, 6, 8}, certificate_369⟩
          else
            if mask < 372 then
              ⟨{1, 4, 5, 6, 8}, certificate_370⟩
            else
              if mask < 376 then
                ⟨{2, 4, 5, 6, 8}, certificate_372⟩
              else
                ⟨{3, 4, 5, 6, 8}, certificate_376⟩
  else
    if mask < 434 then
      if mask < 410 then
        if mask < 403 then
          if mask < 397 then
            if mask < 395 then
              ⟨{0, 1, 2, 7, 8}, certificate_391⟩
            else
              ⟨{0, 1, 3, 7, 8}, certificate_395⟩
          else
            if mask < 398 then
              ⟨{0, 2, 3, 7, 8}, certificate_397⟩
            else
              ⟨{1, 2, 3, 7, 8}, certificate_398⟩
        else
          if mask < 406 then
            if mask < 405 then
              ⟨{0, 1, 4, 7, 8}, certificate_403⟩
            else
              ⟨{0, 2, 4, 7, 8}, certificate_405⟩
          else
            if mask < 409 then
              ⟨{1, 2, 4, 7, 8}, certificate_406⟩
            else
              ⟨{0, 3, 4, 7, 8}, certificate_409⟩
      else
        if mask < 422 then
          if mask < 419 then
            if mask < 412 then
              ⟨{1, 3, 4, 7, 8}, certificate_410⟩
            else
              ⟨{2, 3, 4, 7, 8}, certificate_412⟩
          else
            if mask < 421 then
              ⟨{0, 1, 5, 7, 8}, certificate_419⟩
            else
              ⟨{0, 2, 5, 7, 8}, certificate_421⟩
        else
          if mask < 426 then
            if mask < 425 then
              ⟨{1, 2, 5, 7, 8}, certificate_422⟩
            else
              ⟨{0, 3, 5, 7, 8}, certificate_425⟩
          else
            if mask < 428 then
              ⟨{1, 3, 5, 7, 8}, certificate_426⟩
            else
              if mask < 433 then
                ⟨{2, 3, 5, 7, 8}, certificate_428⟩
              else
                ⟨{0, 4, 5, 7, 8}, certificate_433⟩
    else
      if mask < 465 then
        if mask < 453 then
          if mask < 440 then
            if mask < 436 then
              ⟨{1, 4, 5, 7, 8}, certificate_434⟩
            else
              ⟨{2, 4, 5, 7, 8}, certificate_436⟩
          else
            if mask < 451 then
              ⟨{3, 4, 5, 7, 8}, certificate_440⟩
            else
              ⟨{0, 1, 6, 7, 8}, certificate_451⟩
        else
          if mask < 457 then
            if mask < 454 then
              ⟨{0, 2, 6, 7, 8}, certificate_453⟩
            else
              ⟨{1, 2, 6, 7, 8}, certificate_454⟩
          else
            if mask < 458 then
              ⟨{0, 3, 6, 7, 8}, certificate_457⟩
            else
              if mask < 460 then
                ⟨{1, 3, 6, 7, 8}, certificate_458⟩
              else
                ⟨{2, 3, 6, 7, 8}, certificate_460⟩
      else
        if mask < 481 then
          if mask < 468 then
            if mask < 466 then
              ⟨{0, 4, 6, 7, 8}, certificate_465⟩
            else
              ⟨{1, 4, 6, 7, 8}, certificate_466⟩
          else
            if mask < 472 then
              ⟨{2, 4, 6, 7, 8}, certificate_468⟩
            else
              ⟨{3, 4, 6, 7, 8}, certificate_472⟩
        else
          if mask < 484 then
            if mask < 482 then
              ⟨{0, 5, 6, 7, 8}, certificate_481⟩
            else
              ⟨{1, 5, 6, 7, 8}, certificate_482⟩
          else
            if mask < 488 then
              ⟨{2, 5, 6, 7, 8}, certificate_484⟩
            else
              if mask < 496 then
                ⟨{3, 5, 6, 7, 8}, certificate_488⟩
              else
                ⟨{4, 5, 6, 7, 8}, certificate_496⟩
end AMEProbe.BinaryDirect.Batch01
#print axioms AMEProbe.BinaryDirect.Batch01.lookup
