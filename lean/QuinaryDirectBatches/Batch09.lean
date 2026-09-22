import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch09
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_2319 : Certificate {0, 1, 2, 3, 8, 11} := by
  refine ⟨!![4, 2, 3, 2, 3, 1;
      2, 4, 2, 0, 3, 0;
      3, 3, 1, 2, 0, 2;
      3, 4, 1, 0, 2, 2;
      0, 0, 2, 2, 2, 4;
      1, 2, 2, 2, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 8, 11} =
      !![0, 2, 1, 2, 1, 3;
      0, 4, 0, 2, 4, 1;
      4, 2, 0, 3, 0, 1;
      4, 1, 4, 2, 1, 4;
      4, 4, 1, 4, 4, 1;
      4, 4, 0, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2327 : Certificate {0, 1, 2, 4, 8, 11} := by
  refine ⟨!![1, 0, 3, 1, 4, 1;
      0, 3, 3, 0, 0, 2;
      3, 4, 4, 4, 4, 3;
      1, 0, 3, 4, 2, 1;
      3, 0, 1, 4, 3, 2;
      3, 4, 4, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 8, 11} =
      !![0, 3, 2, 2, 4, 2;
      0, 4, 0, 0, 4, 1;
      4, 2, 0, 3, 0, 1;
      4, 1, 4, 4, 1, 4;
      4, 4, 1, 3, 4, 1;
      4, 4, 0, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2331 : Certificate {0, 1, 3, 4, 8, 11} := by
  refine ⟨!![1, 4, 3, 2, 0, 4;
      4, 1, 0, 1, 1, 3;
      1, 2, 3, 4, 4, 4;
      3, 3, 4, 3, 1, 2;
      4, 4, 4, 1, 0, 0;
      1, 2, 3, 4, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 8, 11} =
      !![0, 0, 2, 1, 1, 2;
      0, 4, 2, 0, 4, 1;
      4, 2, 3, 3, 0, 1;
      4, 1, 2, 4, 1, 4;
      4, 4, 4, 3, 4, 1;
      4, 4, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2333 : Certificate {0, 2, 3, 4, 8, 11} := by
  refine ⟨!![4, 3, 1, 0, 0, 3;
      2, 4, 4, 1, 2, 3;
      0, 3, 3, 0, 0, 2;
      4, 4, 2, 3, 3, 2;
      2, 2, 3, 1, 1, 0;
      2, 2, 2, 1, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 8, 11} =
      !![0, 0, 3, 2, 4, 0;
      0, 0, 2, 0, 4, 1;
      4, 0, 3, 3, 0, 1;
      4, 4, 2, 4, 1, 4;
      4, 1, 4, 3, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2334 : Certificate {1, 2, 3, 4, 8, 11} := by
  refine ⟨!![3, 2, 4, 4, 4, 0;
      4, 1, 3, 3, 4, 4;
      2, 1, 4, 1, 1, 2;
      4, 2, 3, 0, 0, 4;
      2, 1, 1, 2, 2, 1;
      1, 2, 2, 4, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 8, 11} =
      !![0, 0, 0, 0, 4, 3;
      4, 0, 2, 0, 4, 1;
      2, 0, 3, 3, 0, 1;
      1, 4, 2, 4, 1, 4;
      4, 1, 4, 3, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2343 : Certificate {0, 1, 2, 5, 8, 11} := by
  refine ⟨!![3, 0, 4, 4, 3, 3;
      3, 4, 0, 2, 2, 1;
      4, 2, 1, 3, 4, 2;
      2, 0, 1, 3, 4, 2;
      2, 0, 3, 0, 1, 1;
      1, 2, 2, 1, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 8, 11} =
      !![0, 3, 2, 2, 4, 2;
      0, 2, 1, 0, 1, 3;
      4, 2, 0, 3, 0, 1;
      4, 1, 4, 4, 1, 4;
      4, 4, 1, 4, 4, 1;
      4, 4, 0, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2347 : Certificate {0, 1, 3, 5, 8, 11} := by
  refine ⟨!![4, 3, 3, 2, 1, 3;
      2, 1, 1, 3, 2, 4;
      1, 3, 4, 1, 4, 1;
      4, 1, 4, 3, 3, 0;
      4, 1, 1, 0, 0, 4;
      0, 4, 3, 4, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 8, 11} =
      !![0, 0, 2, 0, 1, 2;
      0, 2, 2, 0, 1, 3;
      4, 2, 3, 3, 0, 1;
      4, 1, 2, 4, 1, 4;
      4, 4, 4, 4, 4, 1;
      4, 4, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2349 : Certificate {0, 2, 3, 5, 8, 11} := by
  refine ⟨!![2, 2, 2, 1, 4, 2;
      4, 2, 2, 0, 4, 4;
      1, 3, 4, 2, 4, 0;
      1, 2, 0, 2, 0, 3;
      1, 2, 2, 4, 2, 2;
      1, 2, 1, 4, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 8, 11} =
      !![0, 0, 3, 4, 4, 0;
      0, 1, 2, 0, 1, 3;
      4, 0, 3, 3, 0, 1;
      4, 4, 2, 4, 1, 4;
      4, 1, 4, 4, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2350 : Certificate {1, 2, 3, 5, 8, 11} := by
  refine ⟨!![1, 3, 1, 3, 0, 0;
      1, 1, 4, 1, 1, 0;
      2, 3, 0, 0, 2, 4;
      1, 4, 0, 2, 3, 2;
      1, 4, 2, 4, 0, 1;
      4, 3, 4, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 8, 11} =
      !![0, 0, 0, 0, 4, 3;
      2, 1, 2, 0, 1, 3;
      2, 0, 3, 3, 0, 1;
      1, 4, 2, 4, 1, 4;
      4, 1, 4, 4, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2355 : Certificate {0, 1, 4, 5, 8, 11} := by
  refine ⟨!![1, 2, 4, 3, 1, 1;
      3, 2, 3, 3, 3, 1;
      2, 3, 0, 3, 1, 1;
      1, 1, 1, 2, 2, 0;
      2, 0, 3, 3, 2, 2;
      1, 1, 1, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 8, 11} =
      !![0, 0, 1, 0, 1, 2;
      0, 3, 2, 2, 4, 2;
      4, 2, 3, 3, 0, 1;
      4, 1, 4, 4, 1, 4;
      4, 4, 3, 4, 4, 1;
      4, 4, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2357 : Certificate {0, 2, 4, 5, 8, 11} := by
  refine ⟨!![1, 2, 3, 2, 3, 1;
      1, 4, 0, 0, 3, 2;
      2, 3, 3, 1, 0, 1;
      1, 1, 0, 1, 4, 0;
      2, 0, 1, 1, 1, 2;
      2, 0, 0, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 8, 11} =
      !![0, 0, 2, 4, 4, 0;
      0, 2, 2, 2, 4, 2;
      4, 0, 3, 3, 0, 1;
      4, 4, 4, 4, 1, 4;
      4, 1, 3, 4, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2358 : Certificate {1, 2, 4, 5, 8, 11} := by
  refine ⟨!![4, 2, 2, 4, 0, 3;
      2, 3, 3, 0, 0, 0;
      0, 4, 2, 2, 4, 4;
      0, 4, 2, 4, 1, 4;
      0, 1, 0, 2, 0, 0;
      2, 2, 0, 4, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 8, 11} =
      !![0, 0, 0, 0, 4, 3;
      3, 2, 2, 2, 4, 2;
      2, 0, 3, 3, 0, 1;
      1, 4, 4, 4, 1, 4;
      4, 1, 3, 4, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2361 : Certificate {0, 3, 4, 5, 8, 11} := by
  refine ⟨!![1, 2, 0, 4, 0, 0;
      4, 1, 1, 1, 3, 0;
      3, 2, 0, 3, 0, 2;
      4, 3, 3, 4, 1, 2;
      3, 4, 0, 0, 3, 2;
      3, 4, 4, 0, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 8, 11} =
      !![0, 3, 2, 4, 4, 0;
      0, 2, 1, 0, 1, 2;
      4, 3, 3, 3, 0, 1;
      4, 2, 4, 4, 1, 4;
      4, 4, 3, 4, 4, 1;
      4, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2362 : Certificate {1, 3, 4, 5, 8, 11} := by
  refine ⟨!![2, 3, 1, 3, 3, 1;
      2, 1, 2, 3, 1, 1;
      2, 4, 1, 4, 3, 3;
      3, 2, 2, 0, 3, 1;
      4, 4, 2, 4, 4, 4;
      0, 3, 4, 3, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 8, 11} =
      !![0, 0, 0, 0, 4, 3;
      0, 2, 1, 0, 1, 2;
      2, 3, 3, 3, 0, 1;
      1, 2, 4, 4, 1, 4;
      4, 4, 3, 4, 4, 1;
      4, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2364 : Certificate {2, 3, 4, 5, 8, 11} := by
  refine ⟨!![2, 1, 1, 2, 3, 1;
      2, 2, 2, 1, 1, 1;
      3, 1, 4, 2, 2, 1;
      4, 2, 0, 2, 2, 4;
      3, 0, 4, 0, 0, 1;
      3, 0, 3, 0, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 8, 11} =
      !![0, 0, 0, 0, 4, 3;
      0, 3, 2, 4, 4, 0;
      0, 3, 3, 3, 0, 1;
      4, 2, 4, 4, 1, 4;
      1, 4, 3, 4, 4, 1;
      0, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2375 : Certificate {0, 1, 2, 6, 8, 11} := by
  refine ⟨!![0, 0, 0, 2, 2, 0;
      2, 3, 2, 3, 1, 1;
      4, 4, 1, 3, 2, 0;
      4, 4, 2, 1, 4, 0;
      0, 4, 2, 2, 3, 0;
      0, 0, 4, 2, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 6, 8, 11} =
      !![0, 3, 2, 3, 4, 2;
      0, 2, 1, 3, 1, 3;
      0, 4, 0, 3, 4, 1;
      4, 1, 4, 3, 1, 4;
      4, 4, 1, 2, 4, 1;
      4, 4, 0, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2379 : Certificate {0, 1, 3, 6, 8, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 3;
      3, 4, 4, 1, 4, 0;
      2, 2, 0, 3, 1, 1;
      3, 3, 1, 0, 1, 4;
      4, 3, 2, 3, 0, 2;
      4, 4, 4, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 6, 8, 11} =
      !![0, 0, 2, 0, 1, 2;
      0, 2, 2, 3, 1, 3;
      0, 4, 2, 3, 4, 1;
      4, 1, 2, 3, 1, 4;
      4, 4, 4, 2, 4, 1;
      4, 4, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2381 : Certificate {0, 2, 3, 6, 8, 11} := by
  refine ⟨!![1, 3, 1, 4, 1, 4;
      4, 0, 1, 0, 1, 4;
      2, 1, 2, 4, 3, 3;
      2, 4, 0, 4, 0, 1;
      4, 1, 1, 0, 4, 1;
      4, 2, 3, 0, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 6, 8, 11} =
      !![0, 0, 3, 2, 4, 0;
      0, 1, 2, 3, 1, 3;
      0, 0, 2, 3, 4, 1;
      4, 4, 2, 3, 1, 4;
      4, 1, 4, 2, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2382 : Certificate {1, 2, 3, 6, 8, 11} := by
  refine ⟨!![2, 4, 1, 1, 2, 0;
      4, 1, 4, 1, 1, 3;
      0, 0, 0, 1, 1, 0;
      4, 1, 0, 3, 2, 3;
      0, 4, 2, 4, 0, 0;
      0, 0, 4, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 6, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      2, 1, 2, 3, 1, 3;
      4, 0, 2, 3, 4, 1;
      1, 4, 2, 3, 1, 4;
      4, 1, 4, 2, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2387 : Certificate {0, 1, 4, 6, 8, 11} := by
  refine ⟨!![1, 4, 1, 4, 2, 3;
      0, 4, 0, 2, 2, 1;
      1, 4, 1, 2, 0, 3;
      2, 3, 3, 2, 2, 1;
      4, 2, 0, 2, 1, 2;
      3, 2, 2, 3, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 6, 8, 11} =
      !![0, 0, 1, 0, 1, 2;
      0, 3, 2, 3, 4, 2;
      0, 4, 0, 3, 4, 1;
      4, 1, 4, 3, 1, 4;
      4, 4, 3, 2, 4, 1;
      4, 4, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2389 : Certificate {0, 2, 4, 6, 8, 11} := by
  refine ⟨!![3, 4, 2, 4, 1, 4;
      0, 3, 0, 4, 4, 2;
      3, 4, 2, 2, 4, 4;
      1, 1, 0, 1, 4, 0;
      2, 0, 4, 1, 1, 3;
      4, 2, 0, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 6, 8, 11} =
      !![0, 0, 2, 2, 4, 0;
      0, 2, 2, 3, 4, 2;
      0, 0, 0, 3, 4, 1;
      4, 4, 4, 3, 1, 4;
      4, 1, 3, 2, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2390 : Certificate {1, 2, 4, 6, 8, 11} := by
  refine ⟨!![4, 3, 0, 0, 4, 4;
      2, 2, 0, 4, 1, 4;
      0, 0, 0, 3, 3, 0;
      2, 2, 1, 3, 4, 4;
      2, 3, 1, 0, 4, 4;
      0, 0, 4, 1, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 6, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 3, 4, 2;
      4, 0, 0, 3, 4, 1;
      1, 4, 4, 3, 1, 4;
      4, 1, 3, 2, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2393 : Certificate {0, 3, 4, 6, 8, 11} := by
  refine ⟨!![1, 4, 3, 2, 3, 4;
      1, 3, 2, 0, 3, 2;
      3, 0, 2, 0, 2, 3;
      0, 2, 3, 3, 3, 4;
      3, 3, 1, 1, 4, 0;
      1, 1, 4, 2, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 6, 8, 11} =
      !![0, 3, 2, 2, 4, 0;
      0, 2, 1, 0, 1, 2;
      0, 2, 0, 3, 4, 1;
      4, 2, 4, 3, 1, 4;
      4, 4, 3, 2, 4, 1;
      4, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2394 : Certificate {1, 3, 4, 6, 8, 11} := by
  refine ⟨!![4, 3, 3, 2, 0, 3;
      1, 1, 1, 1, 0, 0;
      2, 2, 2, 0, 3, 0;
      3, 3, 4, 2, 3, 0;
      0, 1, 2, 0, 0, 3;
      3, 3, 2, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 6, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 1, 0, 1, 2;
      4, 2, 0, 3, 4, 1;
      1, 2, 4, 3, 1, 4;
      4, 4, 3, 2, 4, 1;
      4, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2396 : Certificate {2, 3, 4, 6, 8, 11} := by
  refine ⟨!![4, 3, 2, 3, 4, 0;
      1, 1, 4, 3, 3, 4;
      2, 2, 3, 4, 4, 3;
      2, 1, 0, 1, 1, 2;
      1, 3, 3, 4, 4, 2;
      3, 3, 1, 0, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 6, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 2, 2, 4, 0;
      0, 2, 0, 3, 4, 1;
      4, 2, 4, 3, 1, 4;
      1, 4, 3, 2, 4, 1;
      0, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2403 : Certificate {0, 1, 5, 6, 8, 11} := by
  refine ⟨!![2, 0, 2, 0, 3, 1;
      4, 4, 4, 3, 4, 3;
      3, 0, 3, 2, 4, 4;
      4, 1, 0, 1, 2, 2;
      3, 2, 4, 3, 3, 4;
      4, 4, 3, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 6, 8, 11} =
      !![0, 0, 0, 0, 1, 2;
      0, 3, 2, 3, 4, 2;
      0, 2, 0, 3, 1, 3;
      4, 1, 4, 3, 1, 4;
      4, 4, 4, 2, 4, 1;
      4, 4, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2405 : Certificate {0, 2, 5, 6, 8, 11} := by
  refine ⟨!![4, 1, 1, 4, 1, 4;
      1, 2, 4, 2, 0, 3;
      1, 4, 4, 3, 1, 1;
      0, 2, 1, 3, 3, 4;
      3, 0, 3, 3, 0, 2;
      2, 4, 2, 2, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 6, 8, 11} =
      !![0, 0, 4, 2, 4, 0;
      0, 2, 2, 3, 4, 2;
      0, 1, 0, 3, 1, 3;
      4, 4, 4, 3, 1, 4;
      4, 1, 4, 2, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2406 : Certificate {1, 2, 5, 6, 8, 11} := by
  refine ⟨!![4, 3, 0, 2, 1, 4;
      2, 2, 0, 2, 4, 4;
      0, 0, 0, 2, 2, 0;
      4, 0, 1, 0, 4, 3;
      4, 1, 1, 2, 4, 3;
      3, 2, 4, 4, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 6, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 3, 4, 2;
      2, 1, 0, 3, 1, 3;
      1, 4, 4, 3, 1, 4;
      4, 1, 4, 2, 4, 1;
      4, 0, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2409 : Certificate {0, 3, 5, 6, 8, 11} := by
  refine ⟨!![4, 4, 0, 2, 0, 2;
      2, 1, 4, 1, 1, 3;
      2, 4, 2, 3, 0, 2;
      3, 2, 0, 3, 0, 2;
      4, 3, 0, 1, 3, 1;
      1, 3, 1, 1, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 6, 8, 11} =
      !![0, 3, 4, 2, 4, 0;
      0, 2, 0, 0, 1, 2;
      0, 2, 0, 3, 1, 3;
      4, 2, 4, 3, 1, 4;
      4, 4, 4, 2, 4, 1;
      4, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2410 : Certificate {1, 3, 5, 6, 8, 11} := by
  refine ⟨!![1, 2, 2, 4, 3, 4;
      0, 4, 4, 0, 1, 2;
      0, 2, 2, 2, 0, 1;
      4, 2, 3, 0, 2, 4;
      3, 0, 1, 1, 2, 1;
      1, 4, 3, 2, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 6, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 0, 0, 1, 2;
      2, 2, 0, 3, 1, 3;
      1, 2, 4, 3, 1, 4;
      4, 4, 4, 2, 4, 1;
      4, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2412 : Certificate {2, 3, 5, 6, 8, 11} := by
  refine ⟨!![3, 4, 1, 4, 4, 4;
      4, 3, 2, 0, 3, 2;
      2, 4, 1, 2, 1, 1;
      1, 4, 2, 0, 3, 4;
      2, 2, 4, 3, 4, 3;
      3, 2, 2, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 6, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 4, 2, 4, 0;
      1, 2, 0, 3, 1, 3;
      4, 2, 4, 3, 1, 4;
      1, 4, 4, 2, 4, 1;
      0, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2417 : Certificate {0, 4, 5, 6, 8, 11} := by
  refine ⟨!![2, 2, 4, 4, 3, 2;
      2, 2, 1, 3, 2, 0;
      0, 0, 2, 1, 1, 3;
      1, 0, 4, 0, 3, 2;
      0, 4, 3, 0, 4, 1;
      4, 0, 3, 1, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 6, 8, 11} =
      !![0, 2, 4, 2, 4, 0;
      0, 1, 0, 0, 1, 2;
      0, 2, 2, 3, 4, 2;
      4, 4, 4, 3, 1, 4;
      4, 3, 4, 2, 4, 1;
      4, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2418 : Certificate {1, 4, 5, 6, 8, 11} := by
  refine ⟨!![1, 0, 0, 4, 0, 3;
      2, 0, 2, 2, 4, 4;
      2, 0, 2, 4, 1, 4;
      1, 4, 2, 2, 4, 4;
      1, 4, 3, 4, 4, 4;
      1, 1, 0, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 6, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 1, 0, 0, 1, 2;
      3, 2, 2, 3, 4, 2;
      1, 4, 4, 3, 1, 4;
      4, 3, 4, 2, 4, 1;
      4, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2420 : Certificate {2, 4, 5, 6, 8, 11} := by
  refine ⟨!![1, 0, 0, 4, 0, 3;
      1, 0, 2, 3, 4, 1;
      1, 0, 2, 0, 1, 1;
      4, 1, 4, 1, 3, 4;
      4, 1, 0, 3, 3, 4;
      3, 4, 3, 3, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 6, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 4, 2, 4, 0;
      2, 2, 2, 3, 4, 2;
      4, 4, 4, 3, 1, 4;
      1, 3, 4, 2, 4, 1;
      0, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2424 : Certificate {3, 4, 5, 6, 8, 11} := by
  refine ⟨!![3, 0, 0, 2, 0, 4;
      0, 4, 4, 2, 0, 2;
      4, 4, 4, 0, 2, 4;
      0, 4, 3, 1, 0, 0;
      0, 1, 0, 2, 3, 2;
      2, 0, 1, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 6, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 4, 2, 4, 0;
      2, 1, 0, 0, 1, 2;
      2, 4, 4, 3, 1, 4;
      4, 3, 4, 2, 4, 1;
      3, 3, 3, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2439 : Certificate {0, 1, 2, 7, 8, 11} := by
  refine ⟨!![2, 3, 4, 2, 3, 4;
      0, 3, 2, 4, 2, 4;
      2, 3, 3, 2, 4, 4;
      0, 2, 1, 4, 3, 3;
      2, 1, 3, 0, 0, 0;
      2, 1, 2, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 7, 8, 11} =
      !![0, 3, 2, 2, 4, 2;
      0, 2, 1, 4, 1, 3;
      0, 4, 0, 4, 4, 1;
      4, 2, 0, 3, 0, 1;
      4, 4, 1, 4, 4, 1;
      4, 4, 0, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2443 : Certificate {0, 1, 3, 7, 8, 11} := by
  refine ⟨!![3, 4, 0, 2, 4, 3;
      2, 4, 3, 2, 2, 1;
      4, 2, 2, 1, 0, 4;
      4, 4, 3, 0, 3, 2;
      2, 4, 1, 1, 1, 3;
      0, 3, 4, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 7, 8, 11} =
      !![0, 0, 2, 4, 1, 2;
      0, 2, 2, 4, 1, 3;
      0, 4, 2, 4, 4, 1;
      4, 2, 3, 3, 0, 1;
      4, 4, 4, 4, 4, 1;
      4, 4, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2445 : Certificate {0, 2, 3, 7, 8, 11} := by
  refine ⟨!![4, 1, 0, 2, 4, 3;
      4, 3, 2, 3, 3, 4;
      0, 4, 1, 2, 1, 2;
      0, 1, 2, 1, 4, 0;
      4, 3, 0, 2, 2, 1;
      4, 1, 1, 4, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 7, 8, 11} =
      !![0, 0, 3, 1, 4, 0;
      0, 1, 2, 4, 1, 3;
      0, 0, 2, 4, 4, 1;
      4, 0, 3, 3, 0, 1;
      4, 1, 4, 4, 4, 1;
      4, 0, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2446 : Certificate {1, 2, 3, 7, 8, 11} := by
  refine ⟨!![4, 2, 1, 0, 3, 4;
      4, 4, 3, 1, 2, 0;
      3, 3, 3, 2, 2, 0;
      3, 0, 4, 1, 0, 3;
      3, 1, 2, 0, 4, 1;
      4, 2, 2, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 7, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      2, 1, 2, 4, 1, 3;
      4, 0, 2, 4, 4, 1;
      2, 0, 3, 3, 0, 1;
      4, 1, 4, 4, 4, 1;
      4, 0, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2451 : Certificate {0, 1, 4, 7, 8, 11} := by
  refine ⟨!![4, 2, 1, 3, 3, 3;
      2, 4, 4, 1, 0, 4;
      3, 4, 0, 1, 3, 1;
      3, 1, 4, 2, 0, 3;
      2, 4, 2, 0, 4, 1;
      2, 4, 1, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 7, 8, 11} =
      !![0, 0, 1, 4, 1, 2;
      0, 3, 2, 2, 4, 2;
      0, 4, 0, 4, 4, 1;
      4, 2, 3, 3, 0, 1;
      4, 4, 3, 4, 4, 1;
      4, 4, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2453 : Certificate {0, 2, 4, 7, 8, 11} := by
  refine ⟨!![4, 0, 1, 4, 0, 0;
      1, 4, 2, 2, 3, 0;
      1, 2, 1, 4, 1, 0;
      0, 0, 3, 3, 0, 2;
      1, 4, 0, 1, 2, 2;
      1, 4, 4, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 7, 8, 11} =
      !![0, 0, 2, 1, 4, 0;
      0, 2, 2, 2, 4, 2;
      0, 0, 0, 4, 4, 1;
      4, 0, 3, 3, 0, 1;
      4, 1, 3, 4, 4, 1;
      4, 0, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2454 : Certificate {1, 2, 4, 7, 8, 11} := by
  refine ⟨!![3, 1, 2, 2, 3, 1;
      1, 1, 2, 0, 4, 2;
      3, 3, 4, 0, 4, 1;
      2, 4, 1, 1, 2, 1;
      4, 2, 2, 1, 1, 0;
      4, 2, 1, 4, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 7, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 2, 4, 2;
      4, 0, 0, 4, 4, 1;
      2, 0, 3, 3, 0, 1;
      4, 1, 3, 4, 4, 1;
      4, 0, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2457 : Certificate {0, 3, 4, 7, 8, 11} := by
  refine ⟨!![2, 4, 0, 2, 4, 3;
      2, 1, 1, 2, 1, 2;
      1, 4, 4, 1, 1, 3;
      3, 4, 2, 1, 4, 0;
      0, 0, 3, 4, 4, 2;
      4, 2, 4, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 7, 8, 11} =
      !![0, 3, 2, 1, 4, 0;
      0, 2, 1, 4, 1, 2;
      0, 2, 0, 4, 4, 1;
      4, 3, 3, 3, 0, 1;
      4, 4, 3, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2458 : Certificate {1, 3, 4, 7, 8, 11} := by
  refine ⟨!![3, 3, 4, 3, 4, 2;
      1, 3, 4, 1, 0, 3;
      1, 3, 2, 1, 2, 3;
      1, 4, 0, 4, 1, 2;
      3, 3, 2, 2, 3, 4;
      0, 4, 4, 2, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 7, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 1, 4, 1, 2;
      4, 2, 0, 4, 4, 1;
      2, 3, 3, 3, 0, 1;
      4, 4, 3, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2460 : Certificate {2, 3, 4, 7, 8, 11} := by
  refine ⟨!![3, 1, 4, 4, 1, 1;
      0, 4, 1, 4, 0, 0;
      4, 2, 1, 1, 0, 3;
      0, 1, 2, 4, 0, 2;
      3, 1, 2, 3, 0, 3;
      3, 4, 3, 4, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 7, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 2, 1, 4, 0;
      0, 2, 0, 4, 4, 1;
      0, 3, 3, 3, 0, 1;
      1, 4, 3, 4, 4, 1;
      0, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2467 : Certificate {0, 1, 5, 7, 8, 11} := by
  refine ⟨!![0, 1, 4, 1, 1, 2;
      0, 2, 1, 1, 1, 3;
      3, 4, 0, 1, 3, 1;
      4, 3, 1, 3, 4, 3;
      2, 1, 3, 2, 3, 0;
      4, 1, 4, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 7, 8, 11} =
      !![0, 0, 0, 4, 1, 2;
      0, 3, 2, 2, 4, 2;
      0, 2, 0, 4, 1, 3;
      4, 2, 3, 3, 0, 1;
      4, 4, 4, 4, 4, 1;
      4, 4, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2469 : Certificate {0, 2, 5, 7, 8, 11} := by
  refine ⟨!![0, 2, 2, 4, 4, 1;
      0, 2, 1, 1, 1, 3;
      2, 4, 2, 4, 0, 1;
      1, 2, 4, 4, 2, 4;
      3, 3, 2, 0, 2, 3;
      1, 4, 4, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 7, 8, 11} =
      !![0, 0, 4, 1, 4, 0;
      0, 2, 2, 2, 4, 2;
      0, 1, 0, 4, 1, 3;
      4, 0, 3, 3, 0, 1;
      4, 1, 4, 4, 4, 1;
      4, 0, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2470 : Certificate {1, 2, 5, 7, 8, 11} := by
  refine ⟨!![0, 4, 4, 3, 3, 2;
      0, 3, 2, 3, 3, 1;
      3, 1, 2, 3, 1, 2;
      4, 0, 1, 0, 4, 3;
      2, 2, 3, 3, 3, 0;
      4, 4, 3, 1, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 7, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 2, 4, 2;
      2, 1, 0, 4, 1, 3;
      2, 0, 3, 3, 0, 1;
      4, 1, 4, 4, 4, 1;
      4, 0, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2473 : Certificate {0, 3, 5, 7, 8, 11} := by
  refine ⟨!![1, 1, 2, 2, 4, 3;
      2, 2, 2, 3, 2, 0;
      4, 2, 2, 0, 0, 0;
      1, 0, 3, 3, 1, 1;
      2, 4, 2, 2, 2, 1;
      0, 4, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 7, 8, 11} =
      !![0, 3, 4, 1, 4, 0;
      0, 2, 0, 4, 1, 2;
      0, 2, 0, 4, 1, 3;
      4, 3, 3, 3, 0, 1;
      4, 4, 4, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2474 : Certificate {1, 3, 5, 7, 8, 11} := by
  refine ⟨!![1, 4, 1, 4, 1, 3;
      4, 1, 2, 0, 3, 1;
      0, 3, 4, 2, 4, 3;
      1, 3, 2, 0, 3, 1;
      2, 0, 0, 1, 1, 1;
      3, 1, 4, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 7, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 0, 4, 1, 2;
      2, 2, 0, 4, 1, 3;
      2, 3, 3, 3, 0, 1;
      4, 4, 4, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2476 : Certificate {2, 3, 5, 7, 8, 11} := by
  refine ⟨!![2, 2, 1, 2, 0, 2;
      1, 1, 1, 0, 4, 0;
      0, 2, 3, 1, 2, 4;
      2, 3, 4, 0, 1, 3;
      0, 3, 4, 4, 1, 4;
      1, 2, 1, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 7, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 4, 1, 4, 0;
      1, 2, 0, 4, 1, 3;
      0, 3, 3, 3, 0, 1;
      1, 4, 4, 4, 4, 1;
      0, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2481 : Certificate {0, 4, 5, 7, 8, 11} := by
  refine ⟨!![3, 3, 2, 1, 2, 1;
      4, 4, 2, 2, 0, 3;
      1, 4, 2, 4, 3, 3;
      1, 0, 4, 0, 3, 2;
      2, 4, 1, 0, 0, 0;
      0, 4, 3, 4, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 7, 8, 11} =
      !![0, 2, 4, 1, 4, 0;
      0, 1, 0, 4, 1, 2;
      0, 2, 2, 2, 4, 2;
      4, 3, 3, 3, 0, 1;
      4, 3, 4, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2482 : Certificate {1, 4, 5, 7, 8, 11} := by
  refine ⟨!![3, 2, 2, 1, 2, 0;
      4, 1, 2, 2, 0, 0;
      1, 2, 2, 4, 3, 1;
      4, 0, 1, 1, 0, 0;
      1, 1, 2, 3, 1, 1;
      2, 2, 1, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 7, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 1, 0, 4, 1, 2;
      3, 2, 2, 2, 4, 2;
      2, 3, 3, 3, 0, 1;
      4, 3, 4, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2484 : Certificate {2, 4, 5, 7, 8, 11} := by
  refine ⟨!![4, 4, 2, 1, 2, 3;
      1, 1, 4, 3, 2, 2;
      4, 1, 3, 2, 4, 3;
      1, 2, 2, 4, 1, 4;
      4, 2, 2, 3, 1, 0;
      2, 3, 3, 4, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 7, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 4, 1, 4, 0;
      2, 2, 2, 2, 4, 2;
      0, 3, 3, 3, 0, 1;
      1, 3, 4, 4, 4, 1;
      0, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2488 : Certificate {3, 4, 5, 7, 8, 11} := by
  refine ⟨!![3, 2, 4, 0, 0, 4;
      2, 4, 2, 1, 3, 3;
      0, 3, 1, 3, 1, 2;
      1, 4, 2, 3, 4, 3;
      4, 4, 2, 2, 4, 4;
      2, 1, 3, 0, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 7, 8, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 4, 1, 4, 0;
      2, 1, 0, 4, 1, 2;
      3, 3, 3, 3, 0, 1;
      4, 3, 4, 4, 4, 1;
      3, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2499 : Certificate {0, 1, 6, 7, 8, 11} := by
  refine ⟨!![3, 3, 1, 2, 0, 4;
      4, 0, 0, 4, 2, 3;
      2, 2, 4, 4, 4, 1;
      3, 4, 2, 1, 1, 4;
      4, 1, 4, 1, 3, 2;
      0, 4, 4, 0, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 6, 7, 8, 11} =
      !![0, 0, 0, 4, 1, 2;
      0, 3, 3, 2, 4, 2;
      0, 2, 3, 4, 1, 3;
      0, 4, 3, 4, 4, 1;
      4, 4, 2, 4, 4, 1;
      4, 4, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2501 : Certificate {0, 2, 6, 7, 8, 11} := by
  refine ⟨!![4, 0, 2, 4, 3, 1;
      2, 1, 3, 0, 1, 4;
      3, 1, 1, 2, 2, 3;
      1, 2, 1, 3, 0, 0;
      1, 4, 3, 2, 4, 1;
      3, 3, 1, 0, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 6, 7, 8, 11} =
      !![0, 0, 2, 1, 4, 0;
      0, 2, 3, 2, 4, 2;
      0, 1, 3, 4, 1, 3;
      0, 0, 3, 4, 4, 1;
      4, 1, 2, 4, 4, 1;
      4, 0, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2502 : Certificate {1, 2, 6, 7, 8, 11} := by
  refine ⟨!![3, 4, 2, 3, 0, 2;
      2, 2, 0, 0, 2, 4;
      2, 2, 0, 1, 1, 4;
      2, 3, 1, 4, 3, 4;
      4, 1, 1, 0, 2, 3;
      3, 2, 4, 0, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 6, 7, 8, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 3, 2, 4, 2;
      2, 1, 3, 4, 1, 3;
      4, 0, 3, 4, 4, 1;
      4, 1, 2, 4, 4, 1;
      4, 0, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2505 : Certificate {0, 3, 6, 7, 8, 11} := by
  refine ⟨!![4, 3, 2, 2, 2, 2;
      0, 3, 0, 3, 4, 1;
      1, 3, 3, 0, 0, 0;
      2, 0, 0, 3, 3, 2;
      3, 0, 1, 2, 0, 0;
      2, 0, 2, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 6, 7, 8, 11} =
      !![0, 3, 2, 1, 4, 0;
      0, 2, 0, 4, 1, 2;
      0, 2, 3, 4, 1, 3;
      0, 2, 3, 4, 4, 1;
      4, 4, 2, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2506 : Certificate {1, 3, 6, 7, 8, 11} := by
  refine ⟨!![1, 3, 3, 0, 3, 2;
      3, 2, 4, 3, 3, 2;
      1, 4, 3, 2, 0, 4;
      2, 2, 0, 2, 3, 0;
      1, 2, 0, 3, 4, 3;
      0, 1, 1, 4, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 6, 7, 8, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 0, 4, 1, 2;
      2, 2, 3, 4, 1, 3;
      4, 2, 3, 4, 4, 1;
      4, 4, 2, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2508 : Certificate {2, 3, 6, 7, 8, 11} := by
  refine ⟨!![3, 3, 3, 4, 3, 0;
      0, 1, 3, 1, 2, 4;
      3, 0, 4, 2, 1, 3;
      1, 3, 1, 1, 4, 2;
      2, 0, 3, 3, 2, 0;
      4, 1, 1, 2, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 6, 7, 8, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 3, 2, 1, 4, 0;
      1, 2, 3, 4, 1, 3;
      0, 2, 3, 4, 4, 1;
      1, 4, 2, 4, 4, 1;
      0, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2513 : Certificate {0, 4, 6, 7, 8, 11} := by
  refine ⟨!![1, 4, 1, 3, 1, 3;
      0, 1, 0, 1, 3, 2;
      4, 4, 4, 1, 2, 3;
      2, 1, 0, 4, 1, 4;
      4, 1, 3, 3, 1, 4;
      4, 0, 1, 0, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 6, 7, 8, 11} =
      !![0, 2, 2, 1, 4, 0;
      0, 1, 0, 4, 1, 2;
      0, 2, 3, 2, 4, 2;
      0, 0, 3, 4, 4, 1;
      4, 3, 2, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2514 : Certificate {1, 4, 6, 7, 8, 11} := by
  refine ⟨!![1, 4, 1, 4, 3, 0;
      1, 0, 1, 0, 1, 2;
      3, 0, 3, 1, 2, 1;
      1, 2, 4, 2, 2, 3;
      3, 2, 2, 3, 1, 2;
      1, 3, 3, 2, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 6, 7, 8, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 1, 0, 4, 1, 2;
      3, 2, 3, 2, 4, 2;
      4, 0, 3, 4, 4, 1;
      4, 3, 2, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2516 : Certificate {2, 4, 6, 7, 8, 11} := by
  refine ⟨!![3, 2, 0, 3, 1, 1;
      2, 4, 1, 1, 3, 4;
      4, 4, 3, 2, 4, 3;
      3, 0, 1, 0, 3, 3;
      0, 0, 4, 1, 2, 2;
      1, 3, 1, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 6, 7, 8, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 2, 1, 4, 0;
      2, 2, 3, 2, 4, 2;
      0, 0, 3, 4, 4, 1;
      1, 3, 2, 4, 4, 1;
      0, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2520 : Certificate {3, 4, 6, 7, 8, 11} := by
  refine ⟨!![2, 3, 0, 2, 4, 4;
      1, 4, 1, 2, 0, 4;
      2, 3, 3, 1, 2, 0;
      1, 1, 1, 0, 3, 1;
      3, 3, 4, 2, 4, 1;
      4, 4, 1, 1, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 6, 7, 8, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 2, 1, 4, 0;
      2, 1, 0, 4, 1, 2;
      2, 0, 3, 4, 4, 1;
      4, 3, 2, 4, 4, 1;
      3, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2529 : Certificate {0, 5, 6, 7, 8, 11} := by
  refine ⟨!![1, 1, 1, 0, 2, 2;
      2, 0, 1, 3, 1, 4;
      3, 3, 1, 1, 1, 4;
      3, 2, 3, 4, 2, 3;
      1, 3, 4, 3, 3, 2;
      1, 0, 2, 3, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 6, 7, 8, 11} =
      !![0, 4, 2, 1, 4, 0;
      0, 0, 0, 4, 1, 2;
      0, 2, 3, 2, 4, 2;
      0, 0, 3, 4, 1, 3;
      4, 4, 2, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2530 : Certificate {1, 5, 6, 7, 8, 11} := by
  refine ⟨!![2, 3, 1, 3, 4, 4;
      3, 0, 3, 0, 3, 1;
      4, 1, 0, 2, 3, 1;
      0, 4, 0, 4, 1, 2;
      2, 0, 4, 1, 0, 4;
      4, 0, 3, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 6, 7, 8, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 0, 0, 4, 1, 2;
      3, 2, 3, 2, 4, 2;
      2, 0, 3, 4, 1, 3;
      4, 4, 2, 4, 4, 1;
      4, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2532 : Certificate {2, 5, 6, 7, 8, 11} := by
  refine ⟨!![1, 1, 4, 4, 4, 4;
      4, 1, 2, 4, 2, 0;
      3, 3, 0, 3, 2, 0;
      1, 2, 0, 3, 2, 3;
      3, 1, 3, 0, 4, 3;
      1, 2, 1, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 6, 7, 8, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 4, 2, 1, 4, 0;
      2, 2, 3, 2, 4, 2;
      1, 0, 3, 4, 1, 3;
      1, 4, 2, 4, 4, 1;
      0, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2536 : Certificate {3, 5, 6, 7, 8, 11} := by
  refine ⟨!![2, 4, 2, 3, 2, 2;
      2, 0, 1, 1, 1, 4;
      2, 1, 4, 4, 1, 4;
      3, 1, 2, 1, 4, 0;
      1, 4, 0, 2, 1, 0;
      4, 2, 2, 4, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 6, 7, 8, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 4, 2, 1, 4, 0;
      2, 0, 0, 4, 1, 2;
      2, 0, 3, 4, 1, 3;
      4, 4, 2, 4, 4, 1;
      3, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2544 : Certificate {4, 5, 6, 7, 8, 11} := by
  refine ⟨!![0, 3, 3, 3, 1, 1;
      3, 1, 1, 4, 0, 3;
      1, 4, 3, 0, 0, 3;
      4, 2, 2, 4, 3, 4;
      3, 4, 3, 1, 0, 4;
      3, 0, 1, 0, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 6, 7, 8, 11} =
      !![0, 0, 4, 4, 4, 3;
      2, 4, 2, 1, 4, 0;
      1, 0, 0, 4, 1, 2;
      2, 2, 3, 2, 4, 2;
      3, 4, 2, 4, 4, 1;
      3, 3, 3, 0, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 2439 then
    if mask < 2381 then
      if mask < 2350 then
        if mask < 2334 then
          if mask < 2331 then
            if mask < 2327 then
              ⟨{0, 1, 2, 3, 8, 11}, certificate_2319⟩
            else
              ⟨{0, 1, 2, 4, 8, 11}, certificate_2327⟩
          else
            if mask < 2333 then
              ⟨{0, 1, 3, 4, 8, 11}, certificate_2331⟩
            else
              ⟨{0, 2, 3, 4, 8, 11}, certificate_2333⟩
        else
          if mask < 2347 then
            if mask < 2343 then
              ⟨{1, 2, 3, 4, 8, 11}, certificate_2334⟩
            else
              ⟨{0, 1, 2, 5, 8, 11}, certificate_2343⟩
          else
            if mask < 2349 then
              ⟨{0, 1, 3, 5, 8, 11}, certificate_2347⟩
            else
              ⟨{0, 2, 3, 5, 8, 11}, certificate_2349⟩
      else
        if mask < 2361 then
          if mask < 2357 then
            if mask < 2355 then
              ⟨{1, 2, 3, 5, 8, 11}, certificate_2350⟩
            else
              ⟨{0, 1, 4, 5, 8, 11}, certificate_2355⟩
          else
            if mask < 2358 then
              ⟨{0, 2, 4, 5, 8, 11}, certificate_2357⟩
            else
              ⟨{1, 2, 4, 5, 8, 11}, certificate_2358⟩
        else
          if mask < 2364 then
            if mask < 2362 then
              ⟨{0, 3, 4, 5, 8, 11}, certificate_2361⟩
            else
              ⟨{1, 3, 4, 5, 8, 11}, certificate_2362⟩
          else
            if mask < 2375 then
              ⟨{2, 3, 4, 5, 8, 11}, certificate_2364⟩
            else
              if mask < 2379 then
                ⟨{0, 1, 2, 6, 8, 11}, certificate_2375⟩
              else
                ⟨{0, 1, 3, 6, 8, 11}, certificate_2379⟩
    else
      if mask < 2405 then
        if mask < 2390 then
          if mask < 2387 then
            if mask < 2382 then
              ⟨{0, 2, 3, 6, 8, 11}, certificate_2381⟩
            else
              ⟨{1, 2, 3, 6, 8, 11}, certificate_2382⟩
          else
            if mask < 2389 then
              ⟨{0, 1, 4, 6, 8, 11}, certificate_2387⟩
            else
              ⟨{0, 2, 4, 6, 8, 11}, certificate_2389⟩
        else
          if mask < 2394 then
            if mask < 2393 then
              ⟨{1, 2, 4, 6, 8, 11}, certificate_2390⟩
            else
              ⟨{0, 3, 4, 6, 8, 11}, certificate_2393⟩
          else
            if mask < 2396 then
              ⟨{1, 3, 4, 6, 8, 11}, certificate_2394⟩
            else
              if mask < 2403 then
                ⟨{2, 3, 4, 6, 8, 11}, certificate_2396⟩
              else
                ⟨{0, 1, 5, 6, 8, 11}, certificate_2403⟩
      else
        if mask < 2412 then
          if mask < 2409 then
            if mask < 2406 then
              ⟨{0, 2, 5, 6, 8, 11}, certificate_2405⟩
            else
              ⟨{1, 2, 5, 6, 8, 11}, certificate_2406⟩
          else
            if mask < 2410 then
              ⟨{0, 3, 5, 6, 8, 11}, certificate_2409⟩
            else
              ⟨{1, 3, 5, 6, 8, 11}, certificate_2410⟩
        else
          if mask < 2418 then
            if mask < 2417 then
              ⟨{2, 3, 5, 6, 8, 11}, certificate_2412⟩
            else
              ⟨{0, 4, 5, 6, 8, 11}, certificate_2417⟩
          else
            if mask < 2420 then
              ⟨{1, 4, 5, 6, 8, 11}, certificate_2418⟩
            else
              if mask < 2424 then
                ⟨{2, 4, 5, 6, 8, 11}, certificate_2420⟩
              else
                ⟨{3, 4, 5, 6, 8, 11}, certificate_2424⟩
  else
    if mask < 2482 then
      if mask < 2458 then
        if mask < 2451 then
          if mask < 2445 then
            if mask < 2443 then
              ⟨{0, 1, 2, 7, 8, 11}, certificate_2439⟩
            else
              ⟨{0, 1, 3, 7, 8, 11}, certificate_2443⟩
          else
            if mask < 2446 then
              ⟨{0, 2, 3, 7, 8, 11}, certificate_2445⟩
            else
              ⟨{1, 2, 3, 7, 8, 11}, certificate_2446⟩
        else
          if mask < 2454 then
            if mask < 2453 then
              ⟨{0, 1, 4, 7, 8, 11}, certificate_2451⟩
            else
              ⟨{0, 2, 4, 7, 8, 11}, certificate_2453⟩
          else
            if mask < 2457 then
              ⟨{1, 2, 4, 7, 8, 11}, certificate_2454⟩
            else
              ⟨{0, 3, 4, 7, 8, 11}, certificate_2457⟩
      else
        if mask < 2470 then
          if mask < 2467 then
            if mask < 2460 then
              ⟨{1, 3, 4, 7, 8, 11}, certificate_2458⟩
            else
              ⟨{2, 3, 4, 7, 8, 11}, certificate_2460⟩
          else
            if mask < 2469 then
              ⟨{0, 1, 5, 7, 8, 11}, certificate_2467⟩
            else
              ⟨{0, 2, 5, 7, 8, 11}, certificate_2469⟩
        else
          if mask < 2474 then
            if mask < 2473 then
              ⟨{1, 2, 5, 7, 8, 11}, certificate_2470⟩
            else
              ⟨{0, 3, 5, 7, 8, 11}, certificate_2473⟩
          else
            if mask < 2476 then
              ⟨{1, 3, 5, 7, 8, 11}, certificate_2474⟩
            else
              if mask < 2481 then
                ⟨{2, 3, 5, 7, 8, 11}, certificate_2476⟩
              else
                ⟨{0, 4, 5, 7, 8, 11}, certificate_2481⟩
    else
      if mask < 2513 then
        if mask < 2501 then
          if mask < 2488 then
            if mask < 2484 then
              ⟨{1, 4, 5, 7, 8, 11}, certificate_2482⟩
            else
              ⟨{2, 4, 5, 7, 8, 11}, certificate_2484⟩
          else
            if mask < 2499 then
              ⟨{3, 4, 5, 7, 8, 11}, certificate_2488⟩
            else
              ⟨{0, 1, 6, 7, 8, 11}, certificate_2499⟩
        else
          if mask < 2505 then
            if mask < 2502 then
              ⟨{0, 2, 6, 7, 8, 11}, certificate_2501⟩
            else
              ⟨{1, 2, 6, 7, 8, 11}, certificate_2502⟩
          else
            if mask < 2506 then
              ⟨{0, 3, 6, 7, 8, 11}, certificate_2505⟩
            else
              if mask < 2508 then
                ⟨{1, 3, 6, 7, 8, 11}, certificate_2506⟩
              else
                ⟨{2, 3, 6, 7, 8, 11}, certificate_2508⟩
      else
        if mask < 2529 then
          if mask < 2516 then
            if mask < 2514 then
              ⟨{0, 4, 6, 7, 8, 11}, certificate_2513⟩
            else
              ⟨{1, 4, 6, 7, 8, 11}, certificate_2514⟩
          else
            if mask < 2520 then
              ⟨{2, 4, 6, 7, 8, 11}, certificate_2516⟩
            else
              ⟨{3, 4, 6, 7, 8, 11}, certificate_2520⟩
        else
          if mask < 2532 then
            if mask < 2530 then
              ⟨{0, 5, 6, 7, 8, 11}, certificate_2529⟩
            else
              ⟨{1, 5, 6, 7, 8, 11}, certificate_2530⟩
          else
            if mask < 2536 then
              ⟨{2, 5, 6, 7, 8, 11}, certificate_2532⟩
            else
              if mask < 2544 then
                ⟨{3, 5, 6, 7, 8, 11}, certificate_2536⟩
              else
                ⟨{4, 5, 6, 7, 8, 11}, certificate_2544⟩
end AMEProbe.QuinaryDirect.Batch09
#print axioms AMEProbe.QuinaryDirect.Batch09.lookup
