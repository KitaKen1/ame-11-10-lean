import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch13
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_3335 : Certificate {0, 1, 2, 8, 10, 11} := by
  refine ⟨!![3, 3, 4, 0, 4, 0;
      4, 1, 1, 2, 1, 2;
      3, 3, 3, 0, 4, 1;
      1, 0, 0, 0, 1, 4;
      2, 2, 1, 0, 3, 2;
      4, 0, 4, 2, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 8, 10, 11} =
      !![0, 3, 2, 4, 3, 2;
      0, 2, 1, 1, 3, 3;
      0, 4, 0, 4, 3, 1;
      4, 2, 0, 0, 3, 1;
      4, 1, 4, 1, 0, 4;
      4, 4, 1, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3339 : Certificate {0, 1, 3, 8, 10, 11} := by
  refine ⟨!![2, 3, 3, 2, 0, 2;
      2, 0, 4, 4, 4, 2;
      1, 4, 1, 1, 0, 4;
      0, 4, 4, 0, 3, 2;
      1, 4, 0, 1, 2, 2;
      2, 4, 2, 4, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 8, 10, 11} =
      !![0, 0, 2, 1, 0, 2;
      0, 2, 2, 1, 3, 3;
      0, 4, 2, 4, 3, 1;
      4, 2, 3, 0, 3, 1;
      4, 1, 2, 1, 0, 4;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3341 : Certificate {0, 2, 3, 8, 10, 11} := by
  refine ⟨!![3, 1, 4, 4, 3, 2;
      1, 1, 0, 2, 4, 4;
      1, 0, 4, 1, 2, 2;
      2, 1, 4, 4, 1, 0;
      0, 4, 3, 4, 0, 1;
      0, 4, 3, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 8, 10, 11} =
      !![0, 0, 3, 4, 4, 0;
      0, 1, 2, 1, 3, 3;
      0, 0, 2, 4, 3, 1;
      4, 0, 3, 0, 3, 1;
      4, 4, 2, 1, 0, 4;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3342 : Certificate {1, 2, 3, 8, 10, 11} := by
  refine ⟨!![4, 1, 3, 3, 2, 1;
      2, 2, 1, 3, 4, 3;
      4, 4, 4, 1, 3, 4;
      4, 3, 1, 1, 1, 3;
      2, 2, 2, 3, 1, 4;
      4, 0, 1, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 8, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      2, 1, 2, 1, 3, 3;
      4, 0, 2, 4, 3, 1;
      2, 0, 3, 0, 3, 1;
      1, 4, 2, 1, 0, 4;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3347 : Certificate {0, 1, 4, 8, 10, 11} := by
  refine ⟨!![3, 3, 2, 3, 4, 2;
      1, 4, 2, 3, 1, 1;
      1, 1, 2, 1, 3, 1;
      2, 3, 4, 2, 2, 1;
      3, 3, 0, 3, 1, 1;
      4, 3, 2, 1, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 8, 10, 11} =
      !![0, 0, 1, 1, 0, 2;
      0, 3, 2, 4, 3, 2;
      0, 4, 0, 4, 3, 1;
      4, 2, 3, 0, 3, 1;
      4, 1, 4, 1, 0, 4;
      4, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3349 : Certificate {0, 2, 4, 8, 10, 11} := by
  refine ⟨!![0, 1, 1, 4, 1, 4;
      3, 1, 2, 2, 2, 1;
      4, 0, 1, 4, 3, 3;
      3, 1, 2, 3, 2, 0;
      4, 4, 0, 0, 4, 1;
      1, 4, 3, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 8, 10, 11} =
      !![0, 0, 2, 4, 4, 0;
      0, 2, 2, 4, 3, 2;
      0, 0, 0, 4, 3, 1;
      4, 0, 3, 0, 3, 1;
      4, 4, 4, 1, 0, 4;
      4, 1, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3350 : Certificate {1, 2, 4, 8, 10, 11} := by
  refine ⟨!![0, 3, 3, 2, 3, 2;
      3, 2, 3, 2, 2, 4;
      4, 1, 2, 1, 1, 4;
      3, 3, 4, 2, 3, 2;
      4, 1, 2, 1, 3, 1;
      1, 3, 2, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 8, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 4, 3, 2;
      4, 0, 0, 4, 3, 1;
      2, 0, 3, 0, 3, 1;
      1, 4, 4, 1, 0, 4;
      4, 1, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3353 : Certificate {0, 3, 4, 8, 10, 11} := by
  refine ⟨!![2, 0, 4, 2, 4, 3;
      1, 2, 3, 0, 1, 4;
      0, 2, 4, 4, 4, 2;
      1, 2, 3, 1, 1, 3;
      1, 3, 4, 2, 0, 3;
      1, 4, 1, 0, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 8, 10, 11} =
      !![0, 3, 2, 4, 4, 0;
      0, 2, 1, 1, 0, 2;
      0, 2, 0, 4, 3, 1;
      4, 3, 3, 0, 3, 1;
      4, 2, 4, 1, 0, 4;
      4, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3354 : Certificate {1, 3, 4, 8, 10, 11} := by
  refine ⟨!![1, 3, 1, 4, 1, 2;
      4, 4, 0, 0, 3, 3;
      4, 4, 3, 0, 3, 0;
      1, 0, 2, 4, 0, 1;
      1, 1, 3, 0, 4, 1;
      1, 2, 0, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 8, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 1, 1, 0, 2;
      4, 2, 0, 4, 3, 1;
      2, 3, 3, 0, 3, 1;
      1, 2, 4, 1, 0, 4;
      4, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3356 : Certificate {2, 3, 4, 8, 10, 11} := by
  refine ⟨!![0, 3, 1, 3, 1, 2;
      1, 4, 0, 2, 3, 3;
      1, 3, 1, 1, 1, 1;
      1, 2, 1, 1, 4, 4;
      4, 0, 1, 2, 2, 2;
      2, 4, 4, 1, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 8, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 2, 4, 4, 0;
      0, 2, 0, 4, 3, 1;
      0, 3, 3, 0, 3, 1;
      4, 2, 4, 1, 0, 4;
      1, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3363 : Certificate {0, 1, 5, 8, 10, 11} := by
  refine ⟨!![3, 1, 3, 3, 3, 3;
      3, 0, 4, 0, 4, 1;
      3, 2, 4, 3, 1, 1;
      4, 2, 2, 4, 4, 2;
      4, 2, 3, 4, 3, 3;
      1, 4, 4, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 8, 10, 11} =
      !![0, 0, 0, 1, 0, 2;
      0, 3, 2, 4, 3, 2;
      0, 2, 0, 1, 3, 3;
      4, 2, 3, 0, 3, 1;
      4, 1, 4, 1, 0, 4;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3365 : Certificate {0, 2, 5, 8, 10, 11} := by
  refine ⟨!![3, 4, 2, 1, 4, 4;
      3, 3, 3, 3, 0, 2;
      4, 1, 4, 2, 2, 1;
      2, 4, 2, 1, 2, 2;
      3, 0, 4, 2, 1, 2;
      2, 1, 3, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 0;
      0, 2, 2, 4, 3, 2;
      0, 1, 0, 1, 3, 3;
      4, 0, 3, 0, 3, 1;
      4, 4, 4, 1, 0, 4;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3366 : Certificate {1, 2, 5, 8, 10, 11} := by
  refine ⟨!![2, 3, 2, 0, 2, 4;
      3, 1, 4, 2, 4, 4;
      1, 3, 4, 4, 1, 1;
      3, 0, 2, 2, 4, 2;
      4, 2, 1, 1, 1, 1;
      1, 4, 1, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 8, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 4, 3, 2;
      2, 1, 0, 1, 3, 3;
      2, 0, 3, 0, 3, 1;
      1, 4, 4, 1, 0, 4;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3369 : Certificate {0, 3, 5, 8, 10, 11} := by
  refine ⟨!![4, 3, 2, 2, 3, 4;
      0, 3, 4, 0, 4, 1;
      3, 0, 3, 1, 2, 2;
      3, 3, 2, 2, 1, 2;
      3, 1, 2, 2, 4, 4;
      1, 1, 0, 4, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 8, 10, 11} =
      !![0, 3, 4, 4, 4, 0;
      0, 2, 0, 1, 0, 2;
      0, 2, 0, 1, 3, 3;
      4, 3, 3, 0, 3, 1;
      4, 2, 4, 1, 0, 4;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3370 : Certificate {1, 3, 5, 8, 10, 11} := by
  refine ⟨!![3, 0, 0, 4, 0, 2;
      2, 3, 4, 1, 4, 4;
      3, 4, 4, 1, 1, 1;
      1, 2, 3, 1, 0, 3;
      3, 0, 3, 2, 3, 3;
      0, 4, 2, 1, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 8, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 0, 1, 0, 2;
      2, 2, 0, 1, 3, 3;
      2, 3, 3, 0, 3, 1;
      1, 2, 4, 1, 0, 4;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3372 : Certificate {2, 3, 5, 8, 10, 11} := by
  refine ⟨!![4, 0, 0, 2, 0, 1;
      3, 1, 2, 2, 1, 4;
      3, 3, 3, 0, 2, 4;
      0, 4, 0, 0, 3, 3;
      1, 0, 3, 1, 3, 0;
      4, 3, 1, 2, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 8, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 4, 4, 4, 0;
      1, 2, 0, 1, 3, 3;
      0, 3, 3, 0, 3, 1;
      4, 2, 4, 1, 0, 4;
      1, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3377 : Certificate {0, 4, 5, 8, 10, 11} := by
  refine ⟨!![4, 4, 0, 2, 1, 1;
      1, 3, 1, 1, 4, 0;
      4, 2, 1, 2, 3, 0;
      4, 2, 1, 3, 3, 4;
      3, 2, 0, 2, 2, 1;
      0, 3, 4, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 8, 10, 11} =
      !![0, 2, 4, 4, 4, 0;
      0, 1, 0, 1, 0, 2;
      0, 2, 2, 4, 3, 2;
      4, 3, 3, 0, 3, 1;
      4, 4, 4, 1, 0, 4;
      4, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3378 : Certificate {1, 4, 5, 8, 10, 11} := by
  refine ⟨!![4, 2, 1, 0, 0, 2;
      3, 1, 3, 3, 0, 0;
      1, 1, 0, 0, 2, 2;
      4, 0, 2, 1, 2, 0;
      2, 0, 3, 3, 0, 0;
      4, 0, 0, 3, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 8, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 1, 0, 1, 0, 2;
      3, 2, 2, 4, 3, 2;
      2, 3, 3, 0, 3, 1;
      1, 4, 4, 1, 0, 4;
      4, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3380 : Certificate {2, 4, 5, 8, 10, 11} := by
  refine ⟨!![1, 2, 4, 1, 3, 1;
      2, 2, 4, 4, 3, 0;
      1, 4, 0, 2, 3, 3;
      2, 1, 4, 4, 1, 3;
      1, 3, 4, 2, 2, 4;
      3, 3, 1, 2, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 8, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 4, 4, 4, 0;
      2, 2, 2, 4, 3, 2;
      0, 3, 3, 0, 3, 1;
      4, 4, 4, 1, 0, 4;
      1, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3384 : Certificate {3, 4, 5, 8, 10, 11} := by
  refine ⟨!![0, 2, 2, 1, 3, 3;
      1, 0, 0, 3, 0, 4;
      1, 2, 3, 1, 0, 0;
      1, 4, 0, 3, 3, 2;
      0, 4, 3, 0, 1, 0;
      4, 1, 1, 1, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 8, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 4, 4, 4, 0;
      2, 1, 0, 1, 0, 2;
      3, 3, 3, 0, 3, 1;
      2, 4, 4, 1, 0, 4;
      4, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3395 : Certificate {0, 1, 6, 8, 10, 11} := by
  refine ⟨!![0, 2, 2, 3, 1, 3;
      3, 2, 1, 2, 0, 0;
      0, 3, 3, 3, 4, 1;
      0, 4, 3, 3, 0, 0;
      0, 3, 3, 2, 1, 4;
      3, 3, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 6, 8, 10, 11} =
      !![0, 0, 0, 1, 0, 2;
      0, 3, 3, 4, 3, 2;
      0, 2, 3, 1, 3, 3;
      0, 4, 3, 4, 3, 1;
      4, 1, 3, 1, 0, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3397 : Certificate {0, 2, 6, 8, 10, 11} := by
  refine ⟨!![2, 4, 2, 1, 2, 2;
      1, 1, 0, 4, 3, 2;
      4, 2, 3, 4, 1, 4;
      4, 3, 3, 4, 2, 3;
      3, 1, 3, 4, 0, 0;
      3, 4, 0, 1, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 6, 8, 10, 11} =
      !![0, 0, 2, 4, 4, 0;
      0, 2, 3, 4, 3, 2;
      0, 1, 3, 1, 3, 3;
      0, 0, 3, 4, 3, 1;
      4, 4, 3, 1, 0, 4;
      4, 1, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3398 : Certificate {1, 2, 6, 8, 10, 11} := by
  refine ⟨!![2, 0, 4, 1, 3, 4;
      0, 4, 4, 1, 2, 1;
      0, 4, 4, 2, 2, 0;
      0, 0, 4, 2, 3, 4;
      0, 0, 0, 0, 2, 2;
      2, 3, 1, 3, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 6, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 3, 4, 3, 2;
      2, 1, 3, 1, 3, 3;
      4, 0, 3, 4, 3, 1;
      1, 4, 3, 1, 0, 4;
      4, 1, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3401 : Certificate {0, 3, 6, 8, 10, 11} := by
  refine ⟨!![2, 4, 0, 2, 2, 2;
      4, 4, 3, 2, 2, 3;
      1, 4, 1, 3, 2, 3;
      3, 2, 2, 3, 4, 1;
      0, 3, 4, 4, 1, 4;
      2, 3, 1, 4, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 6, 8, 10, 11} =
      !![0, 3, 2, 4, 4, 0;
      0, 2, 0, 1, 0, 2;
      0, 2, 3, 1, 3, 3;
      0, 2, 3, 4, 3, 1;
      4, 2, 3, 1, 0, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3402 : Certificate {1, 3, 6, 8, 10, 11} := by
  refine ⟨!![1, 4, 4, 0, 1, 3;
      3, 3, 0, 3, 1, 3;
      1, 1, 0, 2, 2, 0;
      3, 3, 4, 0, 4, 2;
      4, 4, 0, 4, 0, 1;
      3, 1, 3, 2, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 6, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 0, 1, 0, 2;
      2, 2, 3, 1, 3, 3;
      4, 2, 3, 4, 3, 1;
      1, 2, 3, 1, 0, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3404 : Certificate {2, 3, 6, 8, 10, 11} := by
  refine ⟨!![1, 3, 4, 3, 4, 1;
      1, 0, 2, 3, 4, 2;
      3, 3, 3, 0, 2, 4;
      1, 0, 1, 0, 2, 1;
      3, 0, 1, 4, 4, 3;
      1, 1, 0, 3, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 6, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 3, 2, 4, 4, 0;
      1, 2, 3, 1, 3, 3;
      0, 2, 3, 4, 3, 1;
      4, 2, 3, 1, 0, 4;
      1, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3409 : Certificate {0, 4, 6, 8, 10, 11} := by
  refine ⟨!![1, 4, 4, 3, 4, 0;
      3, 0, 3, 2, 4, 1;
      3, 1, 0, 4, 3, 2;
      4, 1, 2, 3, 2, 3;
      2, 1, 4, 4, 2, 3;
      4, 0, 0, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 6, 8, 10, 11} =
      !![0, 2, 2, 4, 4, 0;
      0, 1, 0, 1, 0, 2;
      0, 2, 3, 4, 3, 2;
      0, 0, 3, 4, 3, 1;
      4, 4, 3, 1, 0, 4;
      4, 3, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3410 : Certificate {1, 4, 6, 8, 10, 11} := by
  refine ⟨!![2, 0, 1, 0, 1, 3;
      3, 3, 0, 3, 1, 3;
      4, 4, 0, 0, 3, 3;
      0, 0, 1, 1, 1, 3;
      3, 3, 0, 3, 3, 0;
      1, 4, 2, 3, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 6, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 1, 0, 1, 0, 2;
      3, 2, 3, 4, 3, 2;
      4, 0, 3, 4, 3, 1;
      1, 4, 3, 1, 0, 4;
      4, 3, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3412 : Certificate {2, 4, 6, 8, 10, 11} := by
  refine ⟨!![3, 0, 4, 0, 4, 2;
      1, 3, 1, 2, 2, 0;
      1, 4, 2, 2, 0, 1;
      3, 0, 0, 1, 0, 0;
      1, 3, 1, 2, 4, 2;
      2, 4, 1, 0, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 6, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 2, 4, 4, 0;
      2, 2, 3, 4, 3, 2;
      0, 0, 3, 4, 3, 1;
      4, 4, 3, 1, 0, 4;
      1, 3, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3416 : Certificate {3, 4, 6, 8, 10, 11} := by
  refine ⟨!![3, 4, 1, 2, 0, 2;
      0, 1, 2, 1, 1, 1;
      1, 1, 3, 3, 3, 1;
      2, 2, 3, 2, 0, 1;
      4, 3, 0, 2, 3, 4;
      1, 2, 2, 4, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 6, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 2, 4, 4, 0;
      2, 1, 0, 1, 0, 2;
      2, 0, 3, 4, 3, 1;
      2, 4, 3, 1, 0, 4;
      4, 3, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3425 : Certificate {0, 5, 6, 8, 10, 11} := by
  refine ⟨!![2, 1, 3, 4, 2, 2;
      2, 3, 4, 1, 1, 4;
      0, 3, 0, 4, 4, 1;
      1, 2, 3, 2, 3, 2;
      1, 1, 3, 0, 4, 1;
      2, 2, 1, 4, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 6, 8, 10, 11} =
      !![0, 4, 2, 4, 4, 0;
      0, 0, 0, 1, 0, 2;
      0, 2, 3, 4, 3, 2;
      0, 0, 3, 1, 3, 3;
      4, 4, 3, 1, 0, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3426 : Certificate {1, 5, 6, 8, 10, 11} := by
  refine ⟨!![3, 1, 2, 1, 1, 3;
      3, 3, 3, 3, 0, 0;
      2, 2, 3, 3, 3, 3;
      1, 1, 3, 2, 4, 2;
      2, 2, 2, 2, 2, 2;
      2, 0, 1, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 6, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 0, 0, 1, 0, 2;
      3, 2, 3, 4, 3, 2;
      2, 0, 3, 1, 3, 3;
      1, 4, 3, 1, 0, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3428 : Certificate {2, 5, 6, 8, 10, 11} := by
  refine ⟨!![4, 4, 2, 1, 2, 3;
      2, 3, 1, 2, 1, 2;
      1, 0, 4, 1, 1, 2;
      2, 4, 3, 2, 0, 2;
      3, 2, 4, 3, 1, 0;
      4, 2, 2, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 6, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 4, 2, 4, 4, 0;
      2, 2, 3, 4, 3, 2;
      1, 0, 3, 1, 3, 3;
      4, 4, 3, 1, 0, 4;
      1, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3432 : Certificate {3, 5, 6, 8, 10, 11} := by
  refine ⟨!![3, 2, 2, 0, 3, 0;
      1, 0, 4, 4, 1, 3;
      2, 3, 1, 4, 1, 1;
      4, 0, 2, 3, 0, 0;
      3, 1, 2, 1, 0, 4;
      0, 3, 0, 1, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 6, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 4, 2, 4, 4, 0;
      2, 0, 0, 1, 0, 2;
      2, 0, 3, 1, 3, 3;
      2, 4, 3, 1, 0, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3440 : Certificate {4, 5, 6, 8, 10, 11} := by
  refine ⟨!![1, 4, 4, 0, 1, 0;
      4, 0, 0, 2, 2, 1;
      3, 0, 4, 2, 0, 4;
      2, 3, 2, 4, 4, 1;
      2, 4, 4, 3, 1, 1;
      1, 4, 0, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 6, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      2, 4, 2, 4, 4, 0;
      1, 0, 0, 1, 0, 2;
      2, 2, 3, 4, 3, 2;
      4, 4, 3, 1, 0, 4;
      3, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3459 : Certificate {0, 1, 7, 8, 10, 11} := by
  refine ⟨!![0, 0, 0, 1, 0, 4;
      2, 2, 2, 1, 4, 1;
      2, 0, 3, 2, 2, 3;
      1, 4, 2, 4, 1, 4;
      3, 1, 3, 3, 3, 2;
      1, 3, 3, 4, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 7, 8, 10, 11} =
      !![0, 0, 4, 1, 0, 2;
      0, 3, 2, 4, 3, 2;
      0, 2, 4, 1, 3, 3;
      0, 4, 4, 4, 3, 1;
      4, 2, 3, 0, 3, 1;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3461 : Certificate {0, 2, 7, 8, 10, 11} := by
  refine ⟨!![2, 1, 0, 4, 1, 3;
      2, 1, 0, 3, 1, 4;
      2, 4, 1, 4, 4, 1;
      4, 0, 1, 2, 1, 4;
      2, 4, 0, 2, 3, 2;
      0, 2, 2, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 7, 8, 10, 11} =
      !![0, 0, 1, 4, 4, 0;
      0, 2, 2, 4, 3, 2;
      0, 1, 4, 1, 3, 3;
      0, 0, 4, 4, 3, 1;
      4, 0, 3, 0, 3, 1;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3462 : Certificate {1, 2, 7, 8, 10, 11} := by
  refine ⟨!![1, 3, 1, 4, 1, 3;
      0, 0, 0, 4, 0, 1;
      1, 1, 2, 4, 4, 1;
      3, 2, 4, 1, 2, 2;
      4, 0, 4, 4, 1, 1;
      3, 1, 0, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 7, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 2, 4, 3, 2;
      2, 1, 4, 1, 3, 3;
      4, 0, 4, 4, 3, 1;
      2, 0, 3, 0, 3, 1;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3465 : Certificate {0, 3, 7, 8, 10, 11} := by
  refine ⟨!![3, 1, 1, 1, 1, 3;
      4, 3, 3, 0, 3, 2;
      2, 1, 2, 2, 1, 4;
      1, 4, 0, 2, 0, 0;
      2, 1, 1, 0, 0, 0;
      4, 1, 3, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 7, 8, 10, 11} =
      !![0, 3, 1, 4, 4, 0;
      0, 2, 4, 1, 0, 2;
      0, 2, 4, 1, 3, 3;
      0, 2, 4, 4, 3, 1;
      4, 3, 3, 0, 3, 1;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3466 : Certificate {1, 3, 7, 8, 10, 11} := by
  refine ⟨!![3, 1, 4, 4, 0, 3;
      0, 0, 0, 2, 0, 3;
      0, 2, 3, 3, 2, 2;
      1, 4, 1, 3, 3, 0;
      4, 0, 4, 3, 1, 2;
      2, 2, 1, 3, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 7, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 4, 1, 0, 2;
      2, 2, 4, 1, 3, 3;
      4, 2, 4, 4, 3, 1;
      2, 3, 3, 0, 3, 1;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3468 : Certificate {2, 3, 7, 8, 10, 11} := by
  refine ⟨!![1, 4, 1, 1, 3, 0;
      2, 3, 2, 4, 1, 3;
      3, 1, 4, 4, 4, 1;
      1, 3, 2, 4, 4, 3;
      3, 1, 3, 2, 3, 2;
      1, 0, 3, 0, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 7, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 3, 1, 4, 4, 0;
      1, 2, 4, 1, 3, 3;
      0, 2, 4, 4, 3, 1;
      0, 3, 3, 0, 3, 1;
      1, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3473 : Certificate {0, 4, 7, 8, 10, 11} := by
  refine ⟨!![1, 0, 3, 0, 3, 1;
      2, 0, 1, 3, 1, 4;
      4, 4, 4, 4, 3, 2;
      4, 4, 4, 4, 4, 1;
      3, 0, 2, 1, 1, 4;
      4, 3, 2, 1, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 7, 8, 10, 11} =
      !![0, 2, 1, 4, 4, 0;
      0, 1, 4, 1, 0, 2;
      0, 2, 2, 4, 3, 2;
      0, 0, 4, 4, 3, 1;
      4, 3, 3, 0, 3, 1;
      4, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3474 : Certificate {1, 4, 7, 8, 10, 11} := by
  refine ⟨!![2, 3, 4, 2, 3, 0;
      0, 0, 0, 3, 0, 2;
      3, 1, 3, 2, 3, 3;
      2, 2, 1, 1, 0, 2;
      3, 2, 4, 4, 4, 1;
      3, 0, 1, 4, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 7, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 1, 4, 1, 0, 2;
      3, 2, 2, 4, 3, 2;
      4, 0, 4, 4, 3, 1;
      2, 3, 3, 0, 3, 1;
      4, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3476 : Certificate {2, 4, 7, 8, 10, 11} := by
  refine ⟨!![0, 3, 4, 0, 4, 3;
      0, 4, 2, 3, 2, 1;
      4, 1, 3, 3, 0, 4;
      4, 4, 2, 3, 0, 1;
      0, 4, 0, 1, 4, 0;
      3, 3, 0, 4, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 7, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 1, 4, 4, 0;
      2, 2, 2, 4, 3, 2;
      0, 0, 4, 4, 3, 1;
      0, 3, 3, 0, 3, 1;
      1, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3480 : Certificate {3, 4, 7, 8, 10, 11} := by
  refine ⟨!![2, 2, 3, 2, 4, 2;
      2, 2, 3, 0, 4, 4;
      1, 2, 3, 0, 1, 0;
      3, 4, 1, 2, 1, 1;
      3, 2, 2, 4, 0, 3;
      1, 1, 2, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 7, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 1, 4, 4, 0;
      2, 1, 4, 1, 0, 2;
      2, 0, 4, 4, 3, 1;
      3, 3, 3, 0, 3, 1;
      4, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3489 : Certificate {0, 5, 7, 8, 10, 11} := by
  refine ⟨!![2, 2, 3, 2, 0, 4;
      3, 1, 0, 1, 1, 4;
      1, 0, 1, 1, 1, 4;
      4, 1, 1, 2, 3, 2;
      3, 3, 0, 3, 2, 3;
      1, 0, 0, 2, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 7, 8, 10, 11} =
      !![0, 4, 1, 4, 4, 0;
      0, 0, 4, 1, 0, 2;
      0, 2, 2, 4, 3, 2;
      0, 0, 4, 1, 3, 3;
      4, 3, 3, 0, 3, 1;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3490 : Certificate {1, 5, 7, 8, 10, 11} := by
  refine ⟨!![2, 3, 4, 0, 3, 2;
      2, 1, 2, 3, 4, 0;
      3, 1, 3, 0, 3, 0;
      4, 3, 3, 3, 4, 3;
      3, 2, 4, 0, 4, 0;
      2, 2, 0, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 7, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 0, 4, 1, 0, 2;
      3, 2, 2, 4, 3, 2;
      2, 0, 4, 1, 3, 3;
      2, 3, 3, 0, 3, 1;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3492 : Certificate {2, 5, 7, 8, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 4, 3;
      1, 3, 2, 1, 0, 0;
      3, 4, 4, 4, 3, 3;
      0, 3, 2, 1, 3, 0;
      2, 2, 0, 2, 0, 3;
      2, 3, 2, 4, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 7, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 4, 1, 4, 4, 0;
      2, 2, 2, 4, 3, 2;
      1, 0, 4, 1, 3, 3;
      0, 3, 3, 0, 3, 1;
      1, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3496 : Certificate {3, 5, 7, 8, 10, 11} := by
  refine ⟨!![4, 3, 4, 3, 1, 0;
      2, 2, 3, 0, 4, 4;
      4, 0, 0, 0, 2, 1;
      0, 0, 2, 3, 3, 4;
      4, 1, 2, 1, 3, 3;
      3, 2, 3, 3, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 7, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 4, 1, 4, 4, 0;
      2, 0, 4, 1, 0, 2;
      2, 0, 4, 1, 3, 3;
      3, 3, 3, 0, 3, 1;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3504 : Certificate {4, 5, 7, 8, 10, 11} := by
  refine ⟨!![2, 0, 3, 4, 3, 2;
      0, 2, 0, 1, 1, 2;
      1, 0, 3, 4, 0, 3;
      1, 2, 3, 0, 2, 4;
      4, 0, 1, 1, 3, 1;
      4, 4, 4, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 7, 8, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      2, 4, 1, 4, 4, 0;
      1, 0, 4, 1, 0, 2;
      2, 2, 2, 4, 3, 2;
      3, 3, 3, 0, 3, 1;
      3, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3521 : Certificate {0, 6, 7, 8, 10, 11} := by
  refine ⟨!![3, 3, 2, 3, 2, 4;
      2, 2, 3, 2, 4, 0;
      0, 1, 4, 2, 4, 0;
      0, 3, 1, 4, 0, 0;
      3, 2, 4, 2, 2, 0;
      0, 2, 4, 4, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 6, 7, 8, 10, 11} =
      !![0, 2, 1, 4, 4, 0;
      0, 0, 4, 1, 0, 2;
      0, 3, 2, 4, 3, 2;
      0, 3, 4, 1, 3, 3;
      0, 3, 4, 4, 3, 1;
      4, 2, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3522 : Certificate {1, 6, 7, 8, 10, 11} := by
  refine ⟨!![3, 1, 0, 4, 2, 0;
      0, 0, 0, 0, 1, 4;
      4, 4, 4, 4, 0, 0;
      2, 2, 1, 0, 3, 0;
      1, 1, 2, 2, 4, 1;
      1, 4, 4, 2, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 6, 7, 8, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      0, 0, 4, 1, 0, 2;
      3, 3, 2, 4, 3, 2;
      2, 3, 4, 1, 3, 3;
      4, 3, 4, 4, 3, 1;
      4, 2, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3524 : Certificate {2, 6, 7, 8, 10, 11} := by
  refine ⟨!![4, 2, 3, 4, 4, 1;
      4, 2, 3, 4, 0, 0;
      3, 3, 1, 4, 3, 4;
      0, 2, 4, 1, 3, 1;
      1, 4, 3, 1, 0, 3;
      3, 2, 2, 0, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 6, 7, 8, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      0, 2, 1, 4, 4, 0;
      2, 3, 2, 4, 3, 2;
      1, 3, 4, 1, 3, 3;
      0, 3, 4, 4, 3, 1;
      1, 2, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3528 : Certificate {3, 6, 7, 8, 10, 11} := by
  refine ⟨!![2, 0, 4, 1, 3, 0;
      4, 0, 3, 2, 2, 4;
      1, 4, 2, 4, 4, 2;
      3, 1, 0, 4, 1, 3;
      2, 2, 0, 2, 1, 2;
      2, 4, 0, 4, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 6, 7, 8, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      3, 2, 1, 4, 4, 0;
      2, 0, 4, 1, 0, 2;
      2, 3, 4, 1, 3, 3;
      2, 3, 4, 4, 3, 1;
      4, 2, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3536 : Certificate {4, 6, 7, 8, 10, 11} := by
  refine ⟨!![3, 1, 2, 4, 1, 3;
      4, 3, 1, 2, 4, 3;
      3, 4, 1, 0, 2, 2;
      0, 1, 4, 0, 4, 3;
      2, 0, 3, 2, 3, 1;
      0, 1, 3, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 6, 7, 8, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      2, 2, 1, 4, 4, 0;
      1, 0, 4, 1, 0, 2;
      2, 3, 2, 4, 3, 2;
      0, 3, 4, 4, 3, 1;
      3, 2, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3552 : Certificate {5, 6, 7, 8, 10, 11} := by
  refine ⟨!![1, 4, 1, 1, 2, 2;
      0, 1, 1, 4, 1, 2;
      1, 3, 1, 1, 3, 4;
      3, 2, 1, 4, 0, 1;
      2, 3, 1, 4, 3, 0;
      4, 3, 3, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {5, 6, 7, 8, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      4, 2, 1, 4, 4, 0;
      0, 0, 4, 1, 0, 2;
      2, 3, 2, 4, 3, 2;
      0, 3, 4, 1, 3, 3;
      4, 2, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 3412 then
    if mask < 3370 then
      if mask < 3353 then
        if mask < 3342 then
          if mask < 3339 then
            ⟨{0, 1, 2, 8, 10, 11}, certificate_3335⟩
          else
            if mask < 3341 then
              ⟨{0, 1, 3, 8, 10, 11}, certificate_3339⟩
            else
              ⟨{0, 2, 3, 8, 10, 11}, certificate_3341⟩
        else
          if mask < 3349 then
            if mask < 3347 then
              ⟨{1, 2, 3, 8, 10, 11}, certificate_3342⟩
            else
              ⟨{0, 1, 4, 8, 10, 11}, certificate_3347⟩
          else
            if mask < 3350 then
              ⟨{0, 2, 4, 8, 10, 11}, certificate_3349⟩
            else
              ⟨{1, 2, 4, 8, 10, 11}, certificate_3350⟩
      else
        if mask < 3363 then
          if mask < 3354 then
            ⟨{0, 3, 4, 8, 10, 11}, certificate_3353⟩
          else
            if mask < 3356 then
              ⟨{1, 3, 4, 8, 10, 11}, certificate_3354⟩
            else
              ⟨{2, 3, 4, 8, 10, 11}, certificate_3356⟩
        else
          if mask < 3366 then
            if mask < 3365 then
              ⟨{0, 1, 5, 8, 10, 11}, certificate_3363⟩
            else
              ⟨{0, 2, 5, 8, 10, 11}, certificate_3365⟩
          else
            if mask < 3369 then
              ⟨{1, 2, 5, 8, 10, 11}, certificate_3366⟩
            else
              ⟨{0, 3, 5, 8, 10, 11}, certificate_3369⟩
    else
      if mask < 3397 then
        if mask < 3378 then
          if mask < 3372 then
            ⟨{1, 3, 5, 8, 10, 11}, certificate_3370⟩
          else
            if mask < 3377 then
              ⟨{2, 3, 5, 8, 10, 11}, certificate_3372⟩
            else
              ⟨{0, 4, 5, 8, 10, 11}, certificate_3377⟩
        else
          if mask < 3384 then
            if mask < 3380 then
              ⟨{1, 4, 5, 8, 10, 11}, certificate_3378⟩
            else
              ⟨{2, 4, 5, 8, 10, 11}, certificate_3380⟩
          else
            if mask < 3395 then
              ⟨{3, 4, 5, 8, 10, 11}, certificate_3384⟩
            else
              ⟨{0, 1, 6, 8, 10, 11}, certificate_3395⟩
      else
        if mask < 3402 then
          if mask < 3398 then
            ⟨{0, 2, 6, 8, 10, 11}, certificate_3397⟩
          else
            if mask < 3401 then
              ⟨{1, 2, 6, 8, 10, 11}, certificate_3398⟩
            else
              ⟨{0, 3, 6, 8, 10, 11}, certificate_3401⟩
        else
          if mask < 3409 then
            if mask < 3404 then
              ⟨{1, 3, 6, 8, 10, 11}, certificate_3402⟩
            else
              ⟨{2, 3, 6, 8, 10, 11}, certificate_3404⟩
          else
            if mask < 3410 then
              ⟨{0, 4, 6, 8, 10, 11}, certificate_3409⟩
            else
              ⟨{1, 4, 6, 8, 10, 11}, certificate_3410⟩
  else
    if mask < 3474 then
      if mask < 3459 then
        if mask < 3426 then
          if mask < 3416 then
            ⟨{2, 4, 6, 8, 10, 11}, certificate_3412⟩
          else
            if mask < 3425 then
              ⟨{3, 4, 6, 8, 10, 11}, certificate_3416⟩
            else
              ⟨{0, 5, 6, 8, 10, 11}, certificate_3425⟩
        else
          if mask < 3432 then
            if mask < 3428 then
              ⟨{1, 5, 6, 8, 10, 11}, certificate_3426⟩
            else
              ⟨{2, 5, 6, 8, 10, 11}, certificate_3428⟩
          else
            if mask < 3440 then
              ⟨{3, 5, 6, 8, 10, 11}, certificate_3432⟩
            else
              ⟨{4, 5, 6, 8, 10, 11}, certificate_3440⟩
      else
        if mask < 3465 then
          if mask < 3461 then
            ⟨{0, 1, 7, 8, 10, 11}, certificate_3459⟩
          else
            if mask < 3462 then
              ⟨{0, 2, 7, 8, 10, 11}, certificate_3461⟩
            else
              ⟨{1, 2, 7, 8, 10, 11}, certificate_3462⟩
        else
          if mask < 3468 then
            if mask < 3466 then
              ⟨{0, 3, 7, 8, 10, 11}, certificate_3465⟩
            else
              ⟨{1, 3, 7, 8, 10, 11}, certificate_3466⟩
          else
            if mask < 3473 then
              ⟨{2, 3, 7, 8, 10, 11}, certificate_3468⟩
            else
              ⟨{0, 4, 7, 8, 10, 11}, certificate_3473⟩
    else
      if mask < 3504 then
        if mask < 3489 then
          if mask < 3476 then
            ⟨{1, 4, 7, 8, 10, 11}, certificate_3474⟩
          else
            if mask < 3480 then
              ⟨{2, 4, 7, 8, 10, 11}, certificate_3476⟩
            else
              ⟨{3, 4, 7, 8, 10, 11}, certificate_3480⟩
        else
          if mask < 3492 then
            if mask < 3490 then
              ⟨{0, 5, 7, 8, 10, 11}, certificate_3489⟩
            else
              ⟨{1, 5, 7, 8, 10, 11}, certificate_3490⟩
          else
            if mask < 3496 then
              ⟨{2, 5, 7, 8, 10, 11}, certificate_3492⟩
            else
              ⟨{3, 5, 7, 8, 10, 11}, certificate_3496⟩
      else
        if mask < 3524 then
          if mask < 3521 then
            ⟨{4, 5, 7, 8, 10, 11}, certificate_3504⟩
          else
            if mask < 3522 then
              ⟨{0, 6, 7, 8, 10, 11}, certificate_3521⟩
            else
              ⟨{1, 6, 7, 8, 10, 11}, certificate_3522⟩
        else
          if mask < 3536 then
            if mask < 3528 then
              ⟨{2, 6, 7, 8, 10, 11}, certificate_3524⟩
            else
              ⟨{3, 6, 7, 8, 10, 11}, certificate_3528⟩
          else
            if mask < 3552 then
              ⟨{4, 6, 7, 8, 10, 11}, certificate_3536⟩
            else
              ⟨{5, 6, 7, 8, 10, 11}, certificate_3552⟩
end AMEProbe.QuinaryDirect.Batch13
#print axioms AMEProbe.QuinaryDirect.Batch13.lookup
