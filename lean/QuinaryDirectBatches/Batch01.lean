import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch01
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_287 : Certificate {0, 1, 2, 3, 4, 8} := by
  refine ⟨!![0, 4, 4, 0, 2, 2;
      1, 2, 1, 2, 1, 2;
      3, 4, 1, 3, 3, 2;
      2, 1, 4, 3, 1, 3;
      4, 1, 0, 4, 4, 3;
      2, 0, 2, 4, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 4, 8} =
      !![0, 4, 0, 2, 0, 4;
      4, 2, 0, 3, 3, 0;
      4, 1, 4, 2, 4, 1;
      4, 4, 1, 4, 3, 4;
      4, 4, 0, 3, 3, 4;
      3, 0, 2, 2, 3, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_303 : Certificate {0, 1, 2, 3, 5, 8} := by
  refine ⟨!![4, 0, 2, 1, 4, 1;
      3, 0, 2, 3, 4, 3;
      4, 3, 4, 1, 2, 0;
      0, 3, 4, 1, 4, 4;
      1, 4, 2, 4, 3, 1;
      1, 1, 4, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 5, 8} =
      !![0, 2, 1, 2, 0, 1;
      4, 2, 0, 3, 3, 0;
      4, 1, 4, 2, 4, 1;
      4, 4, 1, 4, 4, 4;
      4, 4, 0, 3, 3, 4;
      3, 0, 2, 2, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_311 : Certificate {0, 1, 2, 4, 5, 8} := by
  refine ⟨!![3, 1, 0, 2, 4, 1;
      1, 3, 1, 2, 2, 1;
      3, 2, 1, 3, 1, 4;
      0, 4, 2, 3, 2, 2;
      2, 3, 4, 3, 3, 1;
      2, 2, 2, 4, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 5, 8} =
      !![0, 3, 2, 2, 2, 4;
      4, 2, 0, 3, 3, 0;
      4, 1, 4, 4, 4, 1;
      4, 4, 1, 3, 4, 4;
      4, 4, 0, 3, 3, 4;
      3, 0, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_315 : Certificate {0, 1, 3, 4, 5, 8} := by
  refine ⟨!![4, 2, 4, 4, 4, 0;
      0, 4, 4, 1, 0, 3;
      4, 3, 0, 0, 1, 3;
      3, 0, 2, 3, 4, 3;
      1, 2, 0, 1, 3, 2;
      0, 4, 3, 2, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 5, 8} =
      !![0, 0, 2, 1, 0, 1;
      4, 2, 3, 3, 3, 0;
      4, 1, 2, 4, 4, 1;
      4, 4, 4, 3, 4, 4;
      4, 4, 3, 3, 3, 4;
      3, 0, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_317 : Certificate {0, 2, 3, 4, 5, 8} := by
  refine ⟨!![2, 2, 3, 2, 1, 3;
      0, 3, 3, 2, 0, 1;
      2, 0, 1, 1, 3, 0;
      4, 4, 4, 0, 3, 2;
      3, 2, 1, 3, 1, 4;
      0, 1, 0, 0, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 5, 8} =
      !![0, 0, 3, 2, 4, 4;
      4, 0, 3, 3, 3, 0;
      4, 4, 2, 4, 4, 1;
      4, 1, 4, 3, 4, 4;
      4, 0, 3, 3, 3, 4;
      3, 2, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_318 : Certificate {1, 2, 3, 4, 5, 8} := by
  refine ⟨!![2, 2, 0, 0, 3, 0;
      1, 4, 3, 2, 4, 1;
      4, 2, 3, 4, 3, 2;
      3, 3, 3, 1, 3, 1;
      0, 4, 4, 0, 2, 2;
      4, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 5, 8} =
      !![0, 0, 0, 0, 0, 4;
      2, 0, 3, 3, 3, 0;
      1, 4, 2, 4, 4, 1;
      4, 1, 4, 3, 4, 4;
      4, 0, 3, 3, 3, 4;
      0, 2, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_335 : Certificate {0, 1, 2, 3, 6, 8} := by
  refine ⟨!![0, 4, 4, 4, 1, 0;
      0, 3, 1, 4, 3, 1;
      3, 4, 2, 1, 3, 2;
      0, 3, 4, 4, 2, 0;
      3, 2, 1, 4, 1, 2;
      4, 3, 0, 1, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 6, 8} =
      !![0, 2, 1, 2, 3, 1;
      0, 4, 0, 2, 3, 4;
      4, 1, 4, 2, 3, 1;
      4, 4, 1, 4, 2, 4;
      4, 4, 0, 3, 3, 4;
      3, 0, 2, 2, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_343 : Certificate {0, 1, 2, 4, 6, 8} := by
  refine ⟨!![0, 2, 3, 3, 3, 0;
      0, 2, 3, 1, 4, 1;
      3, 1, 3, 2, 4, 3;
      0, 2, 1, 1, 3, 0;
      3, 1, 3, 1, 0, 3;
      4, 0, 1, 2, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 6, 8} =
      !![0, 3, 2, 2, 3, 4;
      0, 4, 0, 0, 3, 4;
      4, 1, 4, 4, 3, 1;
      4, 4, 1, 3, 2, 4;
      4, 4, 0, 3, 3, 4;
      3, 0, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_347 : Certificate {0, 1, 3, 4, 6, 8} := by
  refine ⟨!![4, 1, 1, 0, 0, 4;
      2, 4, 2, 2, 0, 3;
      1, 1, 2, 3, 3, 1;
      1, 3, 3, 4, 1, 1;
      1, 1, 2, 2, 4, 1;
      3, 0, 3, 0, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 6, 8} =
      !![0, 0, 2, 1, 0, 1;
      0, 4, 2, 0, 3, 4;
      4, 1, 2, 4, 3, 1;
      4, 4, 4, 3, 2, 4;
      4, 4, 3, 3, 3, 4;
      3, 0, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_349 : Certificate {0, 2, 3, 4, 6, 8} := by
  refine ⟨!![0, 3, 2, 1, 0, 3;
      4, 3, 4, 2, 1, 4;
      0, 4, 1, 2, 3, 2;
      0, 1, 2, 3, 1, 2;
      4, 2, 0, 3, 0, 1;
      2, 3, 2, 3, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 6, 8} =
      !![0, 0, 3, 2, 2, 4;
      0, 0, 2, 0, 3, 4;
      4, 4, 2, 4, 3, 1;
      4, 1, 4, 3, 2, 4;
      4, 0, 3, 3, 3, 4;
      3, 2, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_350 : Certificate {1, 2, 3, 4, 6, 8} := by
  refine ⟨!![0, 1, 4, 2, 0, 1;
      1, 0, 4, 2, 2, 4;
      0, 2, 3, 3, 3, 0;
      0, 4, 4, 4, 1, 0;
      1, 2, 2, 4, 1, 4;
      3, 3, 3, 1, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 6, 8} =
      !![0, 0, 0, 0, 4, 4;
      4, 0, 2, 0, 3, 4;
      1, 4, 2, 4, 3, 1;
      4, 1, 4, 3, 2, 4;
      4, 0, 3, 3, 3, 4;
      0, 2, 2, 3, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_359 : Certificate {0, 1, 2, 5, 6, 8} := by
  refine ⟨!![2, 3, 2, 2, 2, 4;
      4, 1, 2, 0, 0, 4;
      3, 0, 0, 4, 0, 3;
      3, 2, 0, 0, 3, 1;
      1, 2, 0, 3, 4, 4;
      1, 3, 1, 2, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 6, 8} =
      !![0, 3, 2, 2, 3, 4;
      0, 2, 1, 0, 3, 1;
      4, 1, 4, 4, 3, 1;
      4, 4, 1, 4, 2, 4;
      4, 4, 0, 3, 3, 4;
      3, 0, 2, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_363 : Certificate {0, 1, 3, 5, 6, 8} := by
  refine ⟨!![3, 4, 4, 4, 3, 4;
      1, 3, 1, 4, 2, 4;
      3, 1, 2, 3, 1, 2;
      1, 4, 4, 2, 0, 2;
      4, 0, 1, 4, 2, 4;
      0, 3, 1, 4, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 6, 8} =
      !![0, 0, 2, 0, 0, 1;
      0, 2, 2, 0, 3, 1;
      4, 1, 2, 4, 3, 1;
      4, 4, 4, 4, 2, 4;
      4, 4, 3, 3, 3, 4;
      3, 0, 2, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_365 : Certificate {0, 2, 3, 5, 6, 8} := by
  refine ⟨!![0, 0, 1, 2, 2, 2;
      2, 4, 1, 1, 1, 1;
      2, 1, 0, 2, 1, 1;
      1, 3, 1, 1, 1, 1;
      0, 3, 2, 3, 4, 3;
      4, 1, 3, 1, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 6, 8} =
      !![0, 0, 3, 4, 2, 4;
      0, 1, 2, 0, 3, 1;
      4, 4, 2, 4, 3, 1;
      4, 1, 4, 4, 2, 4;
      4, 0, 3, 3, 3, 4;
      3, 2, 2, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_366 : Certificate {1, 2, 3, 5, 6, 8} := by
  refine ⟨!![0, 0, 3, 1, 1, 1;
      2, 2, 0, 2, 2, 1;
      2, 4, 3, 1, 0, 4;
      1, 2, 1, 0, 0, 2;
      0, 3, 4, 2, 3, 2;
      4, 2, 1, 3, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 6, 8} =
      !![0, 0, 0, 0, 4, 4;
      2, 1, 2, 0, 3, 1;
      1, 4, 2, 4, 3, 1;
      4, 1, 4, 4, 2, 4;
      4, 0, 3, 3, 3, 4;
      0, 2, 2, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_371 : Certificate {0, 1, 4, 5, 6, 8} := by
  refine ⟨!![1, 1, 1, 0, 4, 2;
      2, 3, 0, 4, 4, 1;
      0, 4, 0, 2, 0, 4;
      4, 3, 1, 4, 1, 2;
      4, 3, 1, 3, 2, 2;
      1, 1, 0, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 6, 8} =
      !![0, 0, 1, 0, 0, 1;
      0, 3, 2, 2, 3, 4;
      4, 1, 4, 4, 3, 1;
      4, 4, 3, 4, 2, 4;
      4, 4, 3, 3, 3, 4;
      3, 0, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_373 : Certificate {0, 2, 4, 5, 6, 8} := by
  refine ⟨!![2, 1, 4, 4, 3, 4;
      2, 4, 3, 1, 1, 0;
      4, 2, 1, 4, 2, 4;
      2, 1, 4, 2, 4, 0;
      4, 0, 2, 2, 1, 0;
      3, 3, 2, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 6, 8} =
      !![0, 0, 2, 4, 2, 4;
      0, 2, 2, 2, 3, 4;
      4, 4, 4, 4, 3, 1;
      4, 1, 3, 4, 2, 4;
      4, 0, 3, 3, 3, 4;
      3, 2, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_374 : Certificate {1, 2, 4, 5, 6, 8} := by
  refine ⟨!![2, 4, 0, 1, 0, 3;
      4, 1, 4, 4, 3, 2;
      3, 1, 3, 0, 1, 3;
      3, 1, 0, 2, 1, 3;
      2, 2, 4, 0, 0, 0;
      2, 3, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 6, 8} =
      !![0, 0, 0, 0, 4, 4;
      3, 2, 2, 2, 3, 4;
      1, 4, 4, 4, 3, 1;
      4, 1, 3, 4, 2, 4;
      4, 0, 3, 3, 3, 4;
      0, 2, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_377 : Certificate {0, 3, 4, 5, 6, 8} := by
  refine ⟨!![3, 3, 3, 3, 2, 3;
      1, 2, 4, 2, 2, 1;
      1, 1, 4, 2, 0, 2;
      1, 4, 0, 2, 4, 2;
      2, 1, 4, 3, 2, 3;
      2, 1, 3, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 6, 8} =
      !![0, 3, 2, 4, 2, 4;
      0, 2, 1, 0, 0, 1;
      4, 2, 4, 4, 3, 1;
      4, 4, 3, 4, 2, 4;
      4, 3, 3, 3, 3, 4;
      3, 2, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_378 : Certificate {1, 3, 4, 5, 6, 8} := by
  refine ⟨!![2, 1, 1, 1, 4, 0;
      2, 2, 4, 2, 2, 0;
      3, 4, 2, 0, 2, 1;
      4, 0, 1, 3, 3, 1;
      1, 2, 0, 4, 1, 1;
      3, 3, 0, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 6, 8} =
      !![0, 0, 0, 0, 4, 4;
      0, 2, 1, 0, 0, 1;
      1, 2, 4, 4, 3, 1;
      4, 4, 3, 4, 2, 4;
      4, 3, 3, 3, 3, 4;
      0, 2, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_380 : Certificate {2, 3, 4, 5, 6, 8} := by
  refine ⟨!![4, 3, 0, 0, 0, 3;
      1, 1, 2, 0, 4, 1;
      0, 0, 3, 1, 1, 1;
      3, 3, 1, 3, 3, 4;
      3, 2, 3, 2, 3, 3;
      1, 3, 2, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 6, 8} =
      !![0, 0, 0, 0, 4, 4;
      0, 3, 2, 4, 2, 4;
      4, 2, 4, 4, 3, 1;
      1, 4, 3, 4, 2, 4;
      0, 3, 3, 3, 3, 4;
      2, 2, 3, 1, 1, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_399 : Certificate {0, 1, 2, 3, 7, 8} := by
  refine ⟨!![3, 4, 2, 1, 0, 3;
      2, 0, 1, 4, 1, 2;
      2, 1, 4, 4, 2, 0;
      3, 1, 4, 4, 4, 4;
      0, 2, 3, 2, 2, 4;
      4, 4, 4, 2, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 7, 8} =
      !![0, 2, 1, 2, 4, 1;
      0, 4, 0, 2, 4, 4;
      4, 2, 0, 3, 3, 0;
      4, 4, 1, 4, 4, 4;
      4, 4, 0, 3, 0, 4;
      3, 0, 2, 2, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_407 : Certificate {0, 1, 2, 4, 7, 8} := by
  refine ⟨!![0, 3, 3, 2, 1, 4;
      2, 1, 0, 0, 4, 3;
      3, 2, 3, 1, 2, 2;
      4, 0, 0, 4, 3, 4;
      3, 2, 3, 0, 3, 2;
      0, 1, 2, 0, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 7, 8} =
      !![0, 3, 2, 2, 2, 4;
      0, 4, 0, 0, 4, 4;
      4, 2, 0, 3, 3, 0;
      4, 4, 1, 3, 4, 4;
      4, 4, 0, 3, 0, 4;
      3, 0, 2, 3, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_411 : Certificate {0, 1, 3, 4, 7, 8} := by
  refine ⟨!![3, 3, 4, 1, 4, 0;
      4, 3, 1, 3, 0, 3;
      3, 0, 1, 4, 3, 1;
      4, 4, 4, 3, 1, 1;
      3, 0, 1, 3, 4, 1;
      4, 1, 0, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 7, 8} =
      !![0, 0, 2, 1, 4, 1;
      0, 4, 2, 0, 4, 4;
      4, 2, 3, 3, 3, 0;
      4, 4, 4, 3, 4, 4;
      4, 4, 3, 3, 0, 4;
      3, 0, 2, 3, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_413 : Certificate {0, 2, 3, 4, 7, 8} := by
  refine ⟨!![2, 2, 1, 1, 3, 2;
      1, 0, 2, 3, 2, 4;
      2, 4, 3, 4, 2, 3;
      4, 1, 1, 2, 4, 4;
      3, 4, 0, 1, 0, 2;
      1, 3, 1, 2, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 7, 8} =
      !![0, 0, 3, 2, 1, 4;
      0, 0, 2, 0, 4, 4;
      4, 0, 3, 3, 3, 0;
      4, 1, 4, 3, 4, 4;
      4, 0, 3, 3, 0, 4;
      3, 2, 2, 3, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_414 : Certificate {1, 2, 3, 4, 7, 8} := by
  refine ⟨!![1, 3, 4, 1, 3, 2;
      4, 1, 0, 4, 0, 1;
      0, 2, 2, 3, 4, 1;
      2, 3, 2, 2, 4, 4;
      4, 3, 2, 1, 0, 2;
      0, 2, 3, 4, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 7, 8} =
      !![0, 0, 0, 0, 4, 4;
      4, 0, 2, 0, 4, 4;
      2, 0, 3, 3, 3, 0;
      4, 1, 4, 3, 4, 4;
      4, 0, 3, 3, 0, 4;
      0, 2, 2, 3, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_423 : Certificate {0, 1, 2, 5, 7, 8} := by
  refine ⟨!![1, 1, 1, 1, 1, 3;
      2, 2, 1, 1, 0, 4;
      0, 4, 0, 0, 3, 1;
      2, 0, 0, 2, 4, 2;
      2, 4, 0, 1, 3, 3;
      3, 2, 3, 4, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 7, 8} =
      !![0, 3, 2, 2, 2, 4;
      0, 2, 1, 0, 4, 1;
      4, 2, 0, 3, 3, 0;
      4, 4, 1, 4, 4, 4;
      4, 4, 0, 3, 0, 4;
      3, 0, 2, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_427 : Certificate {0, 1, 3, 5, 7, 8} := by
  refine ⟨!![1, 3, 3, 3, 4, 2;
      2, 3, 0, 0, 0, 0;
      0, 1, 0, 0, 2, 4;
      2, 1, 4, 1, 4, 3;
      2, 2, 4, 0, 2, 2;
      3, 0, 4, 0, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 7, 8} =
      !![0, 0, 2, 0, 4, 1;
      0, 2, 2, 0, 4, 1;
      4, 2, 3, 3, 3, 0;
      4, 4, 4, 4, 4, 4;
      4, 4, 3, 3, 0, 4;
      3, 0, 2, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_429 : Certificate {0, 2, 3, 5, 7, 8} := by
  refine ⟨!![4, 0, 4, 2, 0, 4;
      1, 4, 4, 1, 4, 3;
      1, 0, 4, 1, 1, 2;
      0, 3, 4, 1, 4, 3;
      2, 2, 2, 2, 0, 3;
      4, 4, 0, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 7, 8} =
      !![0, 0, 3, 4, 1, 4;
      0, 1, 2, 0, 4, 1;
      4, 0, 3, 3, 3, 0;
      4, 1, 4, 4, 4, 4;
      4, 0, 3, 3, 0, 4;
      3, 2, 2, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_430 : Certificate {1, 2, 3, 5, 7, 8} := by
  refine ⟨!![3, 3, 3, 4, 2, 4;
      4, 3, 2, 0, 0, 4;
      4, 4, 2, 0, 2, 3;
      3, 1, 2, 0, 1, 2;
      1, 3, 1, 4, 4, 4;
      3, 2, 4, 1, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 7, 8} =
      !![0, 0, 0, 0, 4, 4;
      2, 1, 2, 0, 4, 1;
      2, 0, 3, 3, 3, 0;
      4, 1, 4, 4, 4, 4;
      4, 0, 3, 3, 0, 4;
      0, 2, 2, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_435 : Certificate {0, 1, 4, 5, 7, 8} := by
  refine ⟨!![3, 3, 2, 2, 1, 2;
      4, 3, 4, 4, 2, 0;
      1, 4, 2, 2, 4, 1;
      2, 0, 4, 1, 2, 4;
      2, 0, 4, 0, 3, 4;
      2, 1, 2, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 7, 8} =
      !![0, 0, 1, 0, 4, 1;
      0, 3, 2, 2, 2, 4;
      4, 2, 3, 3, 3, 0;
      4, 4, 3, 4, 4, 4;
      4, 4, 3, 3, 0, 4;
      3, 0, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_437 : Certificate {0, 2, 4, 5, 7, 8} := by
  refine ⟨!![1, 0, 2, 4, 2, 3;
      2, 1, 1, 0, 0, 2;
      1, 0, 4, 1, 1, 2;
      2, 2, 3, 4, 1, 1;
      4, 3, 4, 3, 2, 3;
      3, 1, 4, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 7, 8} =
      !![0, 0, 2, 4, 1, 4;
      0, 2, 2, 2, 2, 4;
      4, 0, 3, 3, 3, 0;
      4, 1, 3, 4, 4, 4;
      4, 0, 3, 3, 0, 4;
      3, 2, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_438 : Certificate {1, 2, 4, 5, 7, 8} := by
  refine ⟨!![2, 3, 3, 2, 2, 1;
      2, 4, 0, 4, 3, 2;
      4, 1, 3, 1, 3, 1;
      3, 4, 1, 4, 0, 4;
      0, 3, 1, 2, 4, 1;
      4, 2, 4, 3, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 7, 8} =
      !![0, 0, 0, 0, 4, 4;
      3, 2, 2, 2, 2, 4;
      2, 0, 3, 3, 3, 0;
      4, 1, 3, 4, 4, 4;
      4, 0, 3, 3, 0, 4;
      0, 2, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_441 : Certificate {0, 3, 4, 5, 7, 8} := by
  refine ⟨!![0, 4, 3, 3, 4, 2;
      3, 3, 2, 3, 4, 3;
      3, 2, 2, 3, 2, 4;
      3, 0, 1, 4, 1, 2;
      1, 3, 3, 1, 1, 0;
      2, 1, 2, 2, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 7, 8} =
      !![0, 3, 2, 4, 1, 4;
      0, 2, 1, 0, 4, 1;
      4, 3, 3, 3, 3, 0;
      4, 4, 3, 4, 4, 4;
      4, 3, 3, 3, 0, 4;
      3, 2, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_442 : Certificate {1, 3, 4, 5, 7, 8} := by
  refine ⟨!![0, 1, 2, 2, 1, 3;
      4, 2, 3, 1, 0, 2;
      4, 4, 4, 2, 1, 2;
      4, 4, 2, 2, 2, 1;
      3, 1, 0, 2, 3, 3;
      1, 4, 0, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 7, 8} =
      !![0, 0, 0, 0, 4, 4;
      0, 2, 1, 0, 4, 1;
      2, 3, 3, 3, 3, 0;
      4, 4, 3, 4, 4, 4;
      4, 3, 3, 3, 0, 4;
      0, 2, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_444 : Certificate {2, 3, 4, 5, 7, 8} := by
  refine ⟨!![1, 3, 2, 0, 3, 3;
      0, 3, 1, 2, 1, 4;
      0, 3, 3, 4, 0, 3;
      2, 4, 0, 4, 2, 3;
      3, 0, 3, 0, 2, 0;
      1, 0, 2, 0, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 7, 8} =
      !![0, 0, 0, 0, 4, 4;
      0, 3, 2, 4, 1, 4;
      0, 3, 3, 3, 3, 0;
      1, 4, 3, 4, 4, 4;
      0, 3, 3, 3, 0, 4;
      2, 2, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_455 : Certificate {0, 1, 2, 6, 7, 8} := by
  refine ⟨!![1, 4, 1, 0, 0, 2;
      0, 0, 1, 3, 0, 1;
      4, 4, 0, 4, 1, 0;
      3, 0, 0, 3, 1, 3;
      1, 4, 0, 0, 1, 2;
      3, 1, 3, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 6, 7, 8} =
      !![0, 3, 2, 3, 2, 4;
      0, 2, 1, 3, 4, 1;
      0, 4, 0, 3, 4, 4;
      4, 4, 1, 2, 4, 4;
      4, 4, 0, 3, 0, 4;
      3, 0, 2, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_459 : Certificate {0, 1, 3, 6, 7, 8} := by
  refine ⟨!![3, 3, 2, 2, 2, 0;
      3, 0, 2, 1, 1, 4;
      2, 0, 4, 2, 4, 2;
      1, 2, 2, 1, 1, 4;
      1, 3, 2, 0, 4, 3;
      3, 3, 4, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 6, 7, 8} =
      !![0, 0, 2, 0, 4, 1;
      0, 2, 2, 3, 4, 1;
      0, 4, 2, 3, 4, 4;
      4, 4, 4, 2, 4, 4;
      4, 4, 3, 3, 0, 4;
      3, 0, 2, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_461 : Certificate {0, 2, 3, 6, 7, 8} := by
  refine ⟨!![4, 2, 0, 1, 1, 1;
      1, 1, 0, 0, 0, 0;
      0, 0, 1, 3, 0, 1;
      2, 4, 3, 4, 4, 1;
      4, 2, 3, 3, 2, 0;
      2, 0, 2, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 6, 7, 8} =
      !![0, 0, 3, 2, 1, 4;
      0, 1, 2, 3, 4, 1;
      0, 0, 2, 3, 4, 4;
      4, 1, 4, 2, 4, 4;
      4, 0, 3, 3, 0, 4;
      3, 2, 2, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_462 : Certificate {1, 2, 3, 6, 7, 8} := by
  refine ⟨!![3, 1, 4, 0, 2, 2;
      3, 4, 4, 1, 3, 3;
      2, 4, 2, 3, 3, 4;
      2, 2, 4, 1, 4, 1;
      3, 1, 2, 2, 3, 1;
      4, 2, 4, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 6, 7, 8} =
      !![0, 0, 0, 4, 4, 4;
      2, 1, 2, 3, 4, 1;
      4, 0, 2, 3, 4, 4;
      4, 1, 4, 2, 4, 4;
      4, 0, 3, 3, 0, 4;
      0, 2, 2, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_467 : Certificate {0, 1, 4, 6, 7, 8} := by
  refine ⟨!![0, 2, 1, 1, 4, 2;
      1, 0, 3, 4, 2, 2;
      2, 0, 4, 2, 4, 2;
      1, 3, 2, 4, 3, 4;
      4, 2, 3, 0, 3, 1;
      3, 2, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 6, 7, 8} =
      !![0, 0, 1, 0, 4, 1;
      0, 3, 2, 3, 2, 4;
      0, 4, 0, 3, 4, 4;
      4, 4, 3, 2, 4, 4;
      4, 4, 3, 3, 0, 4;
      3, 0, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_469 : Certificate {0, 2, 4, 6, 7, 8} := by
  refine ⟨!![3, 4, 1, 3, 2, 2;
      3, 2, 0, 2, 3, 0;
      0, 0, 3, 4, 0, 3;
      0, 3, 4, 0, 1, 2;
      3, 4, 1, 1, 3, 3;
      2, 0, 0, 4, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 6, 7, 8} =
      !![0, 0, 2, 2, 1, 4;
      0, 2, 2, 3, 2, 4;
      0, 0, 0, 3, 4, 4;
      4, 1, 3, 2, 4, 4;
      4, 0, 3, 3, 0, 4;
      3, 2, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_470 : Certificate {1, 2, 4, 6, 7, 8} := by
  refine ⟨!![3, 1, 0, 0, 2, 4;
      0, 3, 4, 4, 1, 3;
      1, 2, 3, 4, 4, 1;
      3, 4, 4, 0, 3, 1;
      2, 4, 0, 3, 4, 2;
      4, 2, 1, 2, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 6, 7, 8} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 2, 4;
      4, 0, 0, 3, 4, 4;
      4, 1, 3, 2, 4, 4;
      4, 0, 3, 3, 0, 4;
      0, 2, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_473 : Certificate {0, 3, 4, 6, 7, 8} := by
  refine ⟨!![2, 1, 4, 3, 3, 4;
      0, 4, 2, 1, 3, 3;
      0, 3, 2, 1, 1, 4;
      3, 1, 2, 1, 1, 4;
      2, 3, 0, 4, 3, 4;
      2, 3, 4, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 6, 7, 8} =
      !![0, 3, 2, 2, 1, 4;
      0, 2, 1, 0, 4, 1;
      0, 2, 0, 3, 4, 4;
      4, 4, 3, 2, 4, 4;
      4, 3, 3, 3, 0, 4;
      3, 2, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_474 : Certificate {1, 3, 4, 6, 7, 8} := by
  refine ⟨!![2, 2, 4, 1, 4, 1;
      2, 1, 1, 2, 2, 4;
      3, 1, 3, 0, 2, 3;
      3, 0, 2, 3, 0, 2;
      4, 1, 4, 3, 3, 2;
      2, 4, 4, 4, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 6, 7, 8} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 1, 0, 4, 1;
      4, 2, 0, 3, 4, 4;
      4, 4, 3, 2, 4, 4;
      4, 3, 3, 3, 0, 4;
      0, 2, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_476 : Certificate {2, 3, 4, 6, 7, 8} := by
  refine ⟨!![2, 1, 1, 0, 3, 3;
      4, 4, 3, 4, 2, 3;
      3, 3, 4, 2, 4, 4;
      4, 3, 0, 3, 4, 1;
      2, 2, 4, 0, 2, 0;
      3, 0, 1, 2, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 6, 7, 8} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 2, 2, 1, 4;
      0, 2, 0, 3, 4, 4;
      1, 4, 3, 2, 4, 4;
      0, 3, 3, 3, 0, 4;
      2, 2, 3, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_483 : Certificate {0, 1, 5, 6, 7, 8} := by
  refine ⟨!![2, 4, 2, 0, 1, 4;
      2, 0, 0, 0, 4, 3;
      0, 2, 2, 2, 3, 0;
      0, 0, 2, 0, 4, 3;
      0, 2, 0, 1, 0, 2;
      1, 2, 0, 1, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 6, 7, 8} =
      !![0, 0, 0, 0, 4, 1;
      0, 3, 2, 3, 2, 4;
      0, 2, 0, 3, 4, 1;
      4, 4, 4, 2, 4, 4;
      4, 4, 3, 3, 0, 4;
      3, 0, 1, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_485 : Certificate {0, 2, 5, 6, 7, 8} := by
  refine ⟨!![2, 3, 3, 4, 3, 1;
      4, 3, 2, 3, 2, 0;
      3, 3, 1, 3, 2, 0;
      3, 1, 1, 1, 3, 3;
      4, 0, 2, 4, 2, 2;
      1, 4, 3, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 6, 7, 8} =
      !![0, 0, 4, 2, 1, 4;
      0, 2, 2, 3, 2, 4;
      0, 1, 0, 3, 4, 1;
      4, 1, 4, 2, 4, 4;
      4, 0, 3, 3, 0, 4;
      3, 2, 1, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_486 : Certificate {1, 2, 5, 6, 7, 8} := by
  refine ⟨!![1, 3, 4, 2, 4, 4;
      3, 1, 3, 1, 3, 0;
      1, 4, 3, 4, 4, 0;
      1, 2, 3, 2, 0, 3;
      3, 3, 3, 2, 3, 2;
      0, 0, 4, 1, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 6, 7, 8} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 2, 4;
      2, 1, 0, 3, 4, 1;
      4, 1, 4, 2, 4, 4;
      4, 0, 3, 3, 0, 4;
      0, 2, 1, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_489 : Certificate {0, 3, 5, 6, 7, 8} := by
  refine ⟨!![3, 0, 1, 1, 1, 1;
      0, 1, 0, 0, 2, 4;
      4, 0, 4, 0, 0, 0;
      0, 3, 2, 0, 0, 0;
      4, 3, 2, 4, 3, 4;
      4, 2, 2, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 6, 7, 8} =
      !![0, 3, 4, 2, 1, 4;
      0, 2, 0, 0, 4, 1;
      0, 2, 0, 3, 4, 1;
      4, 4, 4, 2, 4, 4;
      4, 3, 3, 3, 0, 4;
      3, 2, 1, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_490 : Certificate {1, 3, 5, 6, 7, 8} := by
  refine ⟨!![3, 4, 0, 1, 3, 2;
      1, 4, 0, 2, 3, 3;
      1, 3, 1, 4, 3, 1;
      3, 2, 2, 1, 3, 2;
      4, 0, 4, 4, 4, 2;
      2, 3, 4, 0, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 6, 7, 8} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 0, 0, 4, 1;
      2, 2, 0, 3, 4, 1;
      4, 4, 4, 2, 4, 4;
      4, 3, 3, 3, 0, 4;
      0, 2, 1, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_492 : Certificate {2, 3, 5, 6, 7, 8} := by
  refine ⟨!![0, 2, 4, 4, 4, 4;
      3, 4, 3, 4, 3, 4;
      0, 1, 3, 4, 4, 4;
      4, 1, 4, 0, 1, 3;
      4, 1, 1, 1, 1, 4;
      1, 3, 0, 4, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 6, 7, 8} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 4, 2, 1, 4;
      1, 2, 0, 3, 4, 1;
      1, 4, 4, 2, 4, 4;
      0, 3, 3, 3, 0, 4;
      2, 2, 1, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_497 : Certificate {0, 4, 5, 6, 7, 8} := by
  refine ⟨!![1, 3, 1, 2, 1, 3;
      0, 4, 0, 0, 3, 1;
      1, 0, 4, 4, 1, 0;
      1, 2, 2, 2, 1, 1;
      0, 3, 2, 1, 1, 4;
      0, 0, 2, 1, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 6, 7, 8} =
      !![0, 2, 4, 2, 1, 4;
      0, 1, 0, 0, 4, 1;
      0, 2, 2, 3, 2, 4;
      4, 3, 4, 2, 4, 4;
      4, 3, 3, 3, 0, 4;
      3, 3, 1, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_498 : Certificate {1, 4, 5, 6, 7, 8} := by
  refine ⟨!![4, 3, 0, 3, 1, 0;
      2, 3, 0, 4, 1, 1;
      2, 1, 3, 1, 3, 2;
      3, 0, 1, 1, 2, 3;
      4, 1, 2, 4, 2, 4;
      2, 4, 2, 0, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 6, 7, 8} =
      !![0, 0, 0, 4, 4, 4;
      0, 1, 0, 0, 4, 1;
      3, 2, 2, 3, 2, 4;
      4, 3, 4, 2, 4, 4;
      4, 3, 3, 3, 0, 4;
      0, 3, 1, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_500 : Certificate {2, 4, 5, 6, 7, 8} := by
  refine ⟨!![3, 3, 3, 2, 0, 4;
      4, 1, 1, 0, 0, 4;
      4, 0, 3, 0, 1, 2;
      1, 3, 4, 3, 2, 2;
      1, 0, 2, 3, 0, 4;
      2, 2, 4, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 6, 7, 8} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 4, 2, 1, 4;
      2, 2, 2, 3, 2, 4;
      1, 3, 4, 2, 4, 4;
      0, 3, 3, 3, 0, 4;
      2, 3, 1, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_504 : Certificate {3, 4, 5, 6, 7, 8} := by
  refine ⟨!![4, 0, 3, 3, 1, 0;
      4, 0, 2, 3, 4, 1;
      3, 2, 4, 2, 4, 3;
      3, 4, 2, 4, 1, 0;
      4, 3, 0, 0, 0, 3;
      2, 3, 3, 1, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 6, 7, 8} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 4, 2, 1, 4;
      2, 1, 0, 0, 4, 1;
      4, 3, 4, 2, 4, 4;
      3, 3, 3, 3, 0, 4;
      2, 3, 1, 1, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 429 then
    if mask < 366 then
      if mask < 343 then
        if mask < 315 then
          if mask < 303 then
            ⟨{0, 1, 2, 3, 4, 8}, certificate_287⟩
          else
            if mask < 311 then
              ⟨{0, 1, 2, 3, 5, 8}, certificate_303⟩
            else
              ⟨{0, 1, 2, 4, 5, 8}, certificate_311⟩
        else
          if mask < 318 then
            if mask < 317 then
              ⟨{0, 1, 3, 4, 5, 8}, certificate_315⟩
            else
              ⟨{0, 2, 3, 4, 5, 8}, certificate_317⟩
          else
            if mask < 335 then
              ⟨{1, 2, 3, 4, 5, 8}, certificate_318⟩
            else
              ⟨{0, 1, 2, 3, 6, 8}, certificate_335⟩
      else
        if mask < 350 then
          if mask < 347 then
            ⟨{0, 1, 2, 4, 6, 8}, certificate_343⟩
          else
            if mask < 349 then
              ⟨{0, 1, 3, 4, 6, 8}, certificate_347⟩
            else
              ⟨{0, 2, 3, 4, 6, 8}, certificate_349⟩
        else
          if mask < 363 then
            if mask < 359 then
              ⟨{1, 2, 3, 4, 6, 8}, certificate_350⟩
            else
              ⟨{0, 1, 2, 5, 6, 8}, certificate_359⟩
          else
            if mask < 365 then
              ⟨{0, 1, 3, 5, 6, 8}, certificate_363⟩
            else
              ⟨{0, 2, 3, 5, 6, 8}, certificate_365⟩
    else
      if mask < 399 then
        if mask < 374 then
          if mask < 371 then
            ⟨{1, 2, 3, 5, 6, 8}, certificate_366⟩
          else
            if mask < 373 then
              ⟨{0, 1, 4, 5, 6, 8}, certificate_371⟩
            else
              ⟨{0, 2, 4, 5, 6, 8}, certificate_373⟩
        else
          if mask < 378 then
            if mask < 377 then
              ⟨{1, 2, 4, 5, 6, 8}, certificate_374⟩
            else
              ⟨{0, 3, 4, 5, 6, 8}, certificate_377⟩
          else
            if mask < 380 then
              ⟨{1, 3, 4, 5, 6, 8}, certificate_378⟩
            else
              ⟨{2, 3, 4, 5, 6, 8}, certificate_380⟩
      else
        if mask < 413 then
          if mask < 407 then
            ⟨{0, 1, 2, 3, 7, 8}, certificate_399⟩
          else
            if mask < 411 then
              ⟨{0, 1, 2, 4, 7, 8}, certificate_407⟩
            else
              ⟨{0, 1, 3, 4, 7, 8}, certificate_411⟩
        else
          if mask < 423 then
            if mask < 414 then
              ⟨{0, 2, 3, 4, 7, 8}, certificate_413⟩
            else
              ⟨{1, 2, 3, 4, 7, 8}, certificate_414⟩
          else
            if mask < 427 then
              ⟨{0, 1, 2, 5, 7, 8}, certificate_423⟩
            else
              ⟨{0, 1, 3, 5, 7, 8}, certificate_427⟩
  else
    if mask < 470 then
      if mask < 444 then
        if mask < 437 then
          if mask < 430 then
            ⟨{0, 2, 3, 5, 7, 8}, certificate_429⟩
          else
            if mask < 435 then
              ⟨{1, 2, 3, 5, 7, 8}, certificate_430⟩
            else
              ⟨{0, 1, 4, 5, 7, 8}, certificate_435⟩
        else
          if mask < 441 then
            if mask < 438 then
              ⟨{0, 2, 4, 5, 7, 8}, certificate_437⟩
            else
              ⟨{1, 2, 4, 5, 7, 8}, certificate_438⟩
          else
            if mask < 442 then
              ⟨{0, 3, 4, 5, 7, 8}, certificate_441⟩
            else
              ⟨{1, 3, 4, 5, 7, 8}, certificate_442⟩
      else
        if mask < 461 then
          if mask < 455 then
            ⟨{2, 3, 4, 5, 7, 8}, certificate_444⟩
          else
            if mask < 459 then
              ⟨{0, 1, 2, 6, 7, 8}, certificate_455⟩
            else
              ⟨{0, 1, 3, 6, 7, 8}, certificate_459⟩
        else
          if mask < 467 then
            if mask < 462 then
              ⟨{0, 2, 3, 6, 7, 8}, certificate_461⟩
            else
              ⟨{1, 2, 3, 6, 7, 8}, certificate_462⟩
          else
            if mask < 469 then
              ⟨{0, 1, 4, 6, 7, 8}, certificate_467⟩
            else
              ⟨{0, 2, 4, 6, 7, 8}, certificate_469⟩
    else
      if mask < 489 then
        if mask < 476 then
          if mask < 473 then
            ⟨{1, 2, 4, 6, 7, 8}, certificate_470⟩
          else
            if mask < 474 then
              ⟨{0, 3, 4, 6, 7, 8}, certificate_473⟩
            else
              ⟨{1, 3, 4, 6, 7, 8}, certificate_474⟩
        else
          if mask < 485 then
            if mask < 483 then
              ⟨{2, 3, 4, 6, 7, 8}, certificate_476⟩
            else
              ⟨{0, 1, 5, 6, 7, 8}, certificate_483⟩
          else
            if mask < 486 then
              ⟨{0, 2, 5, 6, 7, 8}, certificate_485⟩
            else
              ⟨{1, 2, 5, 6, 7, 8}, certificate_486⟩
      else
        if mask < 497 then
          if mask < 490 then
            ⟨{0, 3, 5, 6, 7, 8}, certificate_489⟩
          else
            if mask < 492 then
              ⟨{1, 3, 5, 6, 7, 8}, certificate_490⟩
            else
              ⟨{2, 3, 5, 6, 7, 8}, certificate_492⟩
        else
          if mask < 500 then
            if mask < 498 then
              ⟨{0, 4, 5, 6, 7, 8}, certificate_497⟩
            else
              ⟨{1, 4, 5, 6, 7, 8}, certificate_498⟩
          else
            if mask < 504 then
              ⟨{2, 4, 5, 6, 7, 8}, certificate_500⟩
            else
              ⟨{3, 4, 5, 6, 7, 8}, certificate_504⟩
end AMEProbe.QuinaryDirect.Batch01
#print axioms AMEProbe.QuinaryDirect.Batch01.lookup
