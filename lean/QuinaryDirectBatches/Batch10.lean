import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch10
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_2575 : Certificate {0, 1, 2, 3, 9, 11} := by
  refine ⟨!![0, 4, 4, 3, 3, 4;
      2, 4, 4, 2, 0, 4;
      0, 2, 4, 0, 1, 0;
      2, 2, 0, 4, 2, 4;
      4, 3, 1, 1, 2, 1;
      2, 4, 0, 0, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 9, 11} =
      !![0, 2, 1, 2, 3, 3;
      0, 4, 0, 2, 4, 1;
      4, 2, 0, 3, 2, 1;
      4, 1, 4, 2, 4, 4;
      4, 4, 1, 4, 4, 4;
      4, 4, 0, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2583 : Certificate {0, 1, 2, 4, 9, 11} := by
  refine ⟨!![4, 4, 3, 1, 3, 2;
      2, 2, 1, 2, 3, 4;
      3, 2, 2, 1, 1, 1;
      4, 0, 4, 3, 0, 3;
      2, 4, 3, 2, 3, 2;
      4, 2, 4, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 9, 11} =
      !![0, 3, 2, 2, 4, 2;
      0, 4, 0, 0, 4, 1;
      4, 2, 0, 3, 2, 1;
      4, 1, 4, 4, 4, 4;
      4, 4, 1, 1, 4, 4;
      4, 4, 0, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2587 : Certificate {0, 1, 3, 4, 9, 11} := by
  refine ⟨!![0, 3, 2, 3, 0, 4;
      1, 2, 4, 3, 2, 1;
      1, 3, 1, 0, 3, 1;
      0, 4, 3, 0, 2, 0;
      2, 2, 2, 3, 0, 0;
      1, 4, 4, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 9, 11} =
      !![0, 0, 2, 1, 1, 2;
      0, 4, 2, 0, 4, 1;
      4, 2, 3, 3, 2, 1;
      4, 1, 2, 4, 4, 4;
      4, 4, 4, 1, 4, 4;
      4, 4, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2589 : Certificate {0, 2, 3, 4, 9, 11} := by
  refine ⟨!![1, 0, 4, 4, 4, 2;
      2, 4, 4, 2, 3, 1;
      2, 0, 1, 4, 4, 1;
      1, 1, 0, 1, 1, 3;
      2, 2, 3, 4, 4, 4;
      3, 3, 1, 1, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 9, 11} =
      !![0, 0, 3, 2, 4, 0;
      0, 0, 2, 0, 4, 1;
      4, 0, 3, 3, 2, 1;
      4, 4, 2, 4, 4, 4;
      4, 1, 4, 1, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2590 : Certificate {1, 2, 3, 4, 9, 11} := by
  refine ⟨!![1, 3, 3, 4, 4, 2;
      0, 4, 1, 4, 0, 2;
      1, 3, 1, 0, 0, 4;
      0, 1, 1, 2, 2, 1;
      2, 3, 1, 4, 4, 4;
      1, 1, 2, 3, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 9, 11} =
      !![0, 0, 0, 0, 4, 3;
      4, 0, 2, 0, 4, 1;
      2, 0, 3, 3, 2, 1;
      1, 4, 2, 4, 4, 4;
      4, 1, 4, 1, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2599 : Certificate {0, 1, 2, 5, 9, 11} := by
  refine ⟨!![1, 1, 0, 2, 4, 3;
      0, 3, 4, 4, 1, 1;
      0, 3, 4, 1, 4, 1;
      4, 0, 4, 3, 0, 3;
      4, 1, 0, 3, 4, 3;
      1, 3, 1, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 9, 11} =
      !![0, 3, 2, 2, 4, 2;
      0, 2, 1, 0, 3, 3;
      4, 2, 0, 3, 2, 1;
      4, 1, 4, 4, 4, 4;
      4, 4, 1, 4, 4, 4;
      4, 4, 0, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2603 : Certificate {0, 1, 3, 5, 9, 11} := by
  refine ⟨!![1, 3, 0, 4, 4, 1;
      0, 2, 1, 2, 3, 4;
      0, 2, 1, 4, 1, 4;
      4, 2, 1, 4, 2, 3;
      4, 1, 1, 0, 0, 4;
      1, 0, 1, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 9, 11} =
      !![0, 0, 2, 0, 1, 2;
      0, 2, 2, 0, 3, 3;
      4, 2, 3, 3, 2, 1;
      4, 1, 2, 4, 4, 4;
      4, 4, 4, 4, 4, 4;
      4, 4, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2605 : Certificate {0, 2, 3, 5, 9, 11} := by
  refine ⟨!![3, 4, 2, 0, 1, 1;
      0, 4, 2, 4, 1, 3;
      0, 1, 3, 3, 2, 2;
      2, 4, 3, 1, 2, 4;
      2, 4, 1, 3, 4, 2;
      3, 1, 3, 2, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 9, 11} =
      !![0, 0, 3, 4, 4, 0;
      0, 1, 2, 0, 3, 3;
      4, 0, 3, 3, 2, 1;
      4, 4, 2, 4, 4, 4;
      4, 1, 4, 4, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2606 : Certificate {1, 2, 3, 5, 9, 11} := by
  refine ⟨!![3, 1, 0, 1, 0, 2;
      4, 2, 2, 2, 1, 4;
      4, 4, 3, 1, 2, 3;
      3, 4, 0, 2, 3, 2;
      4, 1, 3, 1, 0, 4;
      0, 2, 1, 2, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 9, 11} =
      !![0, 0, 0, 0, 4, 3;
      2, 1, 2, 0, 3, 3;
      2, 0, 3, 3, 2, 1;
      1, 4, 2, 4, 4, 4;
      4, 1, 4, 4, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2611 : Certificate {0, 1, 4, 5, 9, 11} := by
  refine ⟨!![2, 4, 0, 1, 4, 4;
      4, 1, 1, 0, 3, 1;
      4, 1, 1, 2, 1, 1;
      1, 3, 3, 1, 4, 2;
      2, 2, 0, 2, 4, 4;
      0, 1, 2, 3, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 9, 11} =
      !![0, 0, 1, 0, 1, 2;
      0, 3, 2, 2, 4, 2;
      4, 2, 3, 3, 2, 1;
      4, 1, 4, 4, 4, 4;
      4, 4, 1, 4, 4, 4;
      4, 4, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2613 : Certificate {0, 2, 4, 5, 9, 11} := by
  refine ⟨!![3, 0, 0, 3, 3, 3;
      2, 1, 2, 3, 2, 3;
      3, 4, 3, 4, 1, 2;
      2, 0, 1, 4, 4, 1;
      3, 3, 0, 4, 3, 3;
      2, 2, 4, 1, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 9, 11} =
      !![0, 0, 2, 4, 4, 0;
      0, 2, 2, 2, 4, 2;
      4, 0, 3, 3, 2, 1;
      4, 4, 4, 4, 4, 4;
      4, 1, 1, 4, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2614 : Certificate {1, 2, 4, 5, 9, 11} := by
  refine ⟨!![4, 3, 2, 1, 0, 3;
      2, 0, 3, 4, 0, 0;
      2, 3, 4, 4, 3, 3;
      3, 1, 0, 4, 2, 0;
      0, 3, 0, 1, 0, 0;
      2, 1, 0, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 9, 11} =
      !![0, 0, 0, 0, 4, 3;
      3, 2, 2, 2, 4, 2;
      2, 0, 3, 3, 2, 1;
      1, 4, 4, 4, 4, 4;
      4, 1, 1, 4, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2617 : Certificate {0, 3, 4, 5, 9, 11} := by
  refine ⟨!![0, 1, 1, 1, 2, 0;
      3, 4, 4, 2, 1, 3;
      2, 1, 1, 0, 2, 2;
      4, 1, 2, 2, 3, 3;
      3, 3, 2, 4, 4, 0;
      2, 2, 2, 1, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 9, 11} =
      !![0, 3, 2, 4, 4, 0;
      0, 2, 1, 0, 1, 2;
      4, 3, 3, 3, 2, 1;
      4, 2, 4, 4, 4, 4;
      4, 4, 1, 4, 4, 4;
      4, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2618 : Certificate {1, 3, 4, 5, 9, 11} := by
  refine ⟨!![0, 1, 1, 1, 2, 0;
      1, 0, 4, 2, 0, 0;
      4, 1, 2, 1, 0, 0;
      3, 2, 0, 0, 1, 4;
      1, 1, 4, 1, 2, 2;
      4, 2, 3, 2, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 9, 11} =
      !![0, 0, 0, 0, 4, 3;
      0, 2, 1, 0, 1, 2;
      2, 3, 3, 3, 2, 1;
      1, 2, 4, 4, 4, 4;
      4, 4, 1, 4, 4, 4;
      4, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2620 : Certificate {2, 3, 4, 5, 9, 11} := by
  refine ⟨!![2, 4, 3, 3, 4, 4;
      0, 3, 0, 3, 3, 3;
      3, 3, 2, 1, 1, 3;
      0, 4, 1, 1, 1, 3;
      1, 0, 3, 0, 0, 2;
      4, 0, 1, 0, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 9, 11} =
      !![0, 0, 0, 0, 4, 3;
      0, 3, 2, 4, 4, 0;
      0, 3, 3, 3, 2, 1;
      4, 2, 4, 4, 4, 4;
      1, 4, 1, 4, 4, 4;
      0, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2631 : Certificate {0, 1, 2, 6, 9, 11} := by
  refine ⟨!![1, 4, 3, 3, 2, 4;
      1, 0, 2, 0, 3, 2;
      1, 3, 0, 3, 4, 3;
      0, 2, 2, 4, 2, 4;
      4, 0, 4, 1, 3, 1;
      0, 4, 1, 4, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 6, 9, 11} =
      !![0, 3, 2, 3, 4, 2;
      0, 2, 1, 3, 3, 3;
      0, 4, 0, 3, 4, 1;
      4, 1, 4, 3, 4, 4;
      4, 4, 1, 0, 4, 4;
      4, 4, 0, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2635 : Certificate {0, 1, 3, 6, 9, 11} := by
  refine ⟨!![4, 2, 4, 2, 0, 2;
      0, 2, 2, 2, 4, 4;
      2, 3, 3, 1, 1, 3;
      3, 4, 4, 3, 1, 1;
      1, 2, 3, 2, 0, 3;
      3, 1, 3, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 6, 9, 11} =
      !![0, 0, 2, 0, 1, 2;
      0, 2, 2, 3, 3, 3;
      0, 4, 2, 3, 4, 1;
      4, 1, 2, 3, 4, 4;
      4, 4, 4, 0, 4, 4;
      4, 4, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2637 : Certificate {0, 2, 3, 6, 9, 11} := by
  refine ⟨!![4, 3, 4, 0, 2, 2;
      0, 3, 3, 3, 1, 1;
      2, 2, 4, 1, 4, 0;
      3, 0, 3, 3, 3, 4;
      1, 1, 3, 4, 3, 3;
      3, 2, 2, 3, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 6, 9, 11} =
      !![0, 0, 3, 2, 4, 0;
      0, 1, 2, 3, 3, 3;
      0, 0, 2, 3, 4, 1;
      4, 4, 2, 3, 4, 4;
      4, 1, 4, 0, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2638 : Certificate {1, 2, 3, 6, 9, 11} := by
  refine ⟨!![1, 0, 0, 3, 3, 4;
      1, 3, 3, 1, 4, 0;
      2, 3, 2, 2, 4, 2;
      3, 4, 0, 2, 3, 2;
      0, 4, 2, 4, 0, 0;
      3, 1, 4, 2, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 6, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      2, 1, 2, 3, 3, 3;
      4, 0, 2, 3, 4, 1;
      1, 4, 2, 3, 4, 4;
      4, 1, 4, 0, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2643 : Certificate {0, 1, 4, 6, 9, 11} := by
  refine ⟨!![4, 1, 4, 0, 4, 0;
      2, 0, 0, 3, 0, 2;
      3, 1, 2, 2, 3, 0;
      4, 4, 3, 3, 0, 2;
      1, 1, 3, 0, 4, 1;
      1, 4, 0, 4, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 6, 9, 11} =
      !![0, 0, 1, 0, 1, 2;
      0, 3, 2, 3, 4, 2;
      0, 4, 0, 3, 4, 1;
      4, 1, 4, 3, 4, 4;
      4, 4, 1, 0, 4, 4;
      4, 4, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2645 : Certificate {0, 2, 4, 6, 9, 11} := by
  refine ⟨!![1, 2, 2, 1, 2, 1;
      2, 2, 1, 4, 1, 0;
      0, 1, 2, 0, 3, 2;
      3, 2, 2, 3, 4, 3;
      0, 1, 3, 1, 4, 0;
      1, 0, 3, 2, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 6, 9, 11} =
      !![0, 0, 2, 2, 4, 0;
      0, 2, 2, 3, 4, 2;
      0, 0, 0, 3, 4, 1;
      4, 4, 4, 3, 4, 4;
      4, 1, 1, 0, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2646 : Certificate {1, 2, 4, 6, 9, 11} := by
  refine ⟨!![4, 2, 4, 2, 3, 0;
      4, 0, 1, 4, 0, 3;
      1, 4, 3, 3, 0, 2;
      4, 3, 0, 2, 1, 0;
      2, 2, 0, 2, 3, 0;
      4, 0, 0, 3, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 6, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 3, 4, 2;
      4, 0, 0, 3, 4, 1;
      1, 4, 4, 3, 4, 4;
      4, 1, 1, 0, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2649 : Certificate {0, 3, 4, 6, 9, 11} := by
  refine ⟨!![4, 0, 1, 2, 1, 1;
      0, 2, 0, 3, 0, 2;
      4, 1, 4, 2, 0, 3;
      1, 2, 1, 2, 3, 0;
      4, 2, 0, 2, 1, 2;
      1, 2, 3, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 6, 9, 11} =
      !![0, 3, 2, 2, 4, 0;
      0, 2, 1, 0, 1, 2;
      0, 2, 0, 3, 4, 1;
      4, 2, 4, 3, 4, 4;
      4, 4, 1, 0, 4, 4;
      4, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2650 : Certificate {1, 3, 4, 6, 9, 11} := by
  refine ⟨!![4, 2, 1, 2, 0, 0;
      1, 0, 4, 1, 0, 2;
      1, 4, 2, 3, 4, 2;
      2, 3, 0, 0, 4, 1;
      0, 2, 4, 0, 0, 1;
      1, 0, 3, 0, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 6, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 1, 0, 1, 2;
      4, 2, 0, 3, 4, 1;
      1, 2, 4, 3, 4, 4;
      4, 4, 1, 0, 4, 4;
      4, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2652 : Certificate {2, 3, 4, 6, 9, 11} := by
  refine ⟨!![0, 1, 4, 3, 4, 4;
      1, 1, 3, 4, 4, 1;
      3, 0, 0, 4, 4, 2;
      1, 3, 3, 1, 1, 3;
      1, 3, 0, 2, 2, 3;
      1, 2, 1, 1, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 6, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 2, 2, 4, 0;
      0, 2, 0, 3, 4, 1;
      4, 2, 4, 3, 4, 4;
      1, 4, 1, 0, 4, 4;
      0, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2659 : Certificate {0, 1, 5, 6, 9, 11} := by
  refine ⟨!![3, 3, 2, 3, 4, 2;
      2, 3, 4, 2, 2, 1;
      0, 4, 2, 2, 1, 2;
      2, 3, 4, 4, 0, 1;
      4, 0, 4, 1, 4, 0;
      1, 0, 3, 2, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 6, 9, 11} =
      !![0, 0, 0, 0, 1, 2;
      0, 3, 2, 3, 4, 2;
      0, 2, 0, 3, 3, 3;
      4, 1, 4, 3, 4, 4;
      4, 4, 4, 0, 4, 4;
      4, 4, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2661 : Certificate {0, 2, 5, 6, 9, 11} := by
  refine ⟨!![4, 3, 3, 0, 1, 3;
      4, 2, 2, 0, 0, 0;
      4, 1, 4, 2, 1, 2;
      1, 3, 3, 2, 3, 0;
      2, 0, 2, 2, 0, 3;
      4, 3, 3, 1, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 6, 9, 11} =
      !![0, 0, 4, 2, 4, 0;
      0, 2, 2, 3, 4, 2;
      0, 1, 0, 3, 3, 3;
      4, 4, 4, 3, 4, 4;
      4, 1, 4, 0, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2662 : Certificate {1, 2, 5, 6, 9, 11} := by
  refine ⟨!![3, 1, 2, 3, 4, 0;
      3, 0, 1, 3, 3, 2;
      3, 4, 3, 0, 4, 4;
      0, 1, 1, 2, 4, 3;
      0, 1, 3, 2, 2, 4;
      2, 4, 3, 3, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 6, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 3, 4, 2;
      2, 1, 0, 3, 3, 3;
      1, 4, 4, 3, 4, 4;
      4, 1, 4, 0, 4, 4;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2665 : Certificate {0, 3, 5, 6, 9, 11} := by
  refine ⟨!![2, 2, 1, 2, 3, 4;
      3, 4, 2, 4, 4, 2;
      4, 1, 1, 3, 2, 0;
      2, 1, 3, 3, 4, 3;
      3, 3, 1, 0, 3, 2;
      3, 0, 0, 1, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 6, 9, 11} =
      !![0, 3, 4, 2, 4, 0;
      0, 2, 0, 0, 1, 2;
      0, 2, 0, 3, 3, 3;
      4, 2, 4, 3, 4, 4;
      4, 4, 4, 0, 4, 4;
      4, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2666 : Certificate {1, 3, 5, 6, 9, 11} := by
  refine ⟨!![3, 4, 3, 2, 1, 1;
      3, 0, 1, 3, 3, 2;
      3, 1, 2, 1, 2, 3;
      0, 4, 2, 1, 1, 4;
      3, 4, 0, 4, 2, 2;
      3, 1, 4, 0, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 6, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 0, 0, 1, 2;
      2, 2, 0, 3, 3, 3;
      1, 2, 4, 3, 4, 4;
      4, 4, 4, 0, 4, 4;
      4, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2668 : Certificate {2, 3, 5, 6, 9, 11} := by
  refine ⟨!![1, 2, 2, 1, 0, 1;
      2, 3, 4, 2, 3, 1;
      1, 0, 0, 3, 3, 4;
      2, 0, 4, 4, 0, 3;
      4, 3, 0, 1, 1, 0;
      4, 1, 3, 0, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 6, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 4, 2, 4, 0;
      1, 2, 0, 3, 3, 3;
      4, 2, 4, 3, 4, 4;
      1, 4, 4, 0, 4, 4;
      0, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2673 : Certificate {0, 4, 5, 6, 9, 11} := by
  refine ⟨!![2, 4, 3, 4, 0, 0;
      1, 1, 2, 1, 1, 3;
      0, 4, 0, 1, 0, 4;
      4, 4, 3, 1, 2, 2;
      4, 1, 0, 3, 1, 1;
      0, 2, 4, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 6, 9, 11} =
      !![0, 2, 4, 2, 4, 0;
      0, 1, 0, 0, 1, 2;
      0, 2, 2, 3, 4, 2;
      4, 4, 4, 3, 4, 4;
      4, 1, 4, 0, 4, 4;
      4, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2674 : Certificate {1, 4, 5, 6, 9, 11} := by
  refine ⟨!![1, 3, 4, 4, 1, 4;
      1, 2, 2, 3, 2, 2;
      3, 3, 2, 3, 3, 1;
      0, 1, 2, 3, 2, 2;
      0, 3, 4, 0, 1, 1;
      2, 3, 2, 1, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 6, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 1, 0, 0, 1, 2;
      3, 2, 2, 3, 4, 2;
      1, 4, 4, 3, 4, 4;
      4, 1, 4, 0, 4, 4;
      4, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2676 : Certificate {2, 4, 5, 6, 9, 11} := by
  refine ⟨!![1, 1, 3, 1, 1, 4;
      4, 2, 2, 4, 0, 4;
      3, 1, 1, 0, 3, 1;
      0, 2, 0, 2, 2, 2;
      0, 1, 3, 2, 1, 1;
      2, 1, 1, 3, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 6, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 4, 2, 4, 0;
      2, 2, 2, 3, 4, 2;
      4, 4, 4, 3, 4, 4;
      1, 1, 4, 0, 4, 4;
      0, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2680 : Certificate {3, 4, 5, 6, 9, 11} := by
  refine ⟨!![4, 1, 4, 3, 4, 1;
      2, 1, 2, 4, 3, 1;
      2, 3, 1, 0, 2, 2;
      4, 3, 4, 0, 1, 3;
      2, 2, 3, 2, 3, 4;
      4, 0, 4, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 6, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 4, 2, 4, 0;
      2, 1, 0, 0, 1, 2;
      2, 4, 4, 3, 4, 4;
      4, 1, 4, 0, 4, 4;
      3, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2695 : Certificate {0, 1, 2, 7, 9, 11} := by
  refine ⟨!![0, 1, 0, 4, 4, 1;
      3, 3, 0, 2, 1, 2;
      4, 1, 3, 3, 2, 0;
      1, 4, 4, 1, 4, 0;
      4, 2, 1, 0, 0, 0;
      3, 4, 1, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 7, 9, 11} =
      !![0, 3, 2, 2, 4, 2;
      0, 2, 1, 4, 3, 3;
      0, 4, 0, 4, 4, 1;
      4, 2, 0, 3, 2, 1;
      4, 4, 1, 1, 4, 4;
      4, 4, 0, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2699 : Certificate {0, 1, 3, 7, 9, 11} := by
  refine ⟨!![2, 1, 3, 0, 1, 3;
      3, 1, 1, 0, 0, 0;
      1, 0, 4, 3, 1, 1;
      0, 0, 2, 4, 1, 0;
      4, 1, 4, 4, 2, 4;
      0, 2, 0, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 7, 9, 11} =
      !![0, 0, 2, 4, 1, 2;
      0, 2, 2, 4, 3, 3;
      0, 4, 2, 4, 4, 1;
      4, 2, 3, 3, 2, 1;
      4, 4, 4, 1, 4, 4;
      4, 4, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2701 : Certificate {0, 2, 3, 7, 9, 11} := by
  refine ⟨!![1, 1, 2, 1, 4, 4;
      3, 2, 4, 3, 4, 3;
      3, 0, 1, 1, 0, 4;
      2, 3, 3, 1, 2, 2;
      0, 3, 1, 4, 2, 4;
      1, 1, 3, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 7, 9, 11} =
      !![0, 0, 3, 1, 4, 0;
      0, 1, 2, 4, 3, 3;
      0, 0, 2, 4, 4, 1;
      4, 0, 3, 3, 2, 1;
      4, 1, 4, 1, 4, 4;
      4, 0, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2702 : Certificate {1, 2, 3, 7, 9, 11} := by
  refine ⟨!![2, 3, 4, 4, 2, 2;
      1, 3, 0, 2, 3, 2;
      0, 2, 0, 3, 3, 2;
      4, 2, 2, 2, 3, 3;
      1, 2, 3, 1, 3, 0;
      2, 3, 0, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 7, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      2, 1, 2, 4, 3, 3;
      4, 0, 2, 4, 4, 1;
      2, 0, 3, 3, 2, 1;
      4, 1, 4, 1, 4, 4;
      4, 0, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2707 : Certificate {0, 1, 4, 7, 9, 11} := by
  refine ⟨!![0, 1, 2, 1, 2, 1;
      2, 1, 4, 4, 2, 4;
      4, 0, 1, 2, 4, 4;
      3, 0, 4, 3, 4, 3;
      0, 1, 0, 4, 1, 0;
      0, 2, 4, 1, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 7, 9, 11} =
      !![0, 0, 1, 4, 1, 2;
      0, 3, 2, 2, 4, 2;
      0, 4, 0, 4, 4, 1;
      4, 2, 3, 3, 2, 1;
      4, 4, 1, 1, 4, 4;
      4, 4, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2709 : Certificate {0, 2, 4, 7, 9, 11} := by
  refine ⟨!![2, 4, 4, 4, 2, 3;
      2, 3, 2, 3, 0, 2;
      3, 0, 1, 1, 0, 4;
      4, 2, 2, 3, 1, 1;
      4, 2, 4, 0, 1, 4;
      3, 4, 2, 3, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 7, 9, 11} =
      !![0, 0, 2, 1, 4, 0;
      0, 2, 2, 2, 4, 2;
      0, 0, 0, 4, 4, 1;
      4, 0, 3, 3, 2, 1;
      4, 1, 1, 1, 4, 4;
      4, 0, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2710 : Certificate {1, 2, 4, 7, 9, 11} := by
  refine ⟨!![1, 4, 2, 1, 2, 4;
      0, 4, 3, 4, 3, 4;
      2, 2, 4, 2, 1, 0;
      4, 0, 2, 4, 0, 1;
      0, 4, 1, 2, 2, 3;
      0, 3, 1, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 7, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 2, 4, 2;
      4, 0, 0, 4, 4, 1;
      2, 0, 3, 3, 2, 1;
      4, 1, 1, 1, 4, 4;
      4, 0, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2713 : Certificate {0, 3, 4, 7, 9, 11} := by
  refine ⟨!![4, 1, 3, 4, 3, 2;
      4, 3, 0, 2, 3, 0;
      4, 2, 1, 4, 2, 4;
      3, 4, 4, 2, 0, 3;
      2, 2, 1, 1, 3, 1;
      2, 0, 1, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 7, 9, 11} =
      !![0, 3, 2, 1, 4, 0;
      0, 2, 1, 4, 1, 2;
      0, 2, 0, 4, 4, 1;
      4, 3, 3, 3, 2, 1;
      4, 4, 1, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2714 : Certificate {1, 3, 4, 7, 9, 11} := by
  refine ⟨!![1, 0, 4, 2, 4, 0;
      4, 2, 3, 1, 1, 3;
      4, 1, 4, 3, 0, 2;
      3, 2, 0, 0, 1, 4;
      3, 4, 4, 0, 1, 0;
      4, 2, 3, 0, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 7, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 1, 4, 1, 2;
      4, 2, 0, 4, 4, 1;
      2, 3, 3, 3, 2, 1;
      4, 4, 1, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2716 : Certificate {2, 3, 4, 7, 9, 11} := by
  refine ⟨!![4, 0, 1, 3, 1, 0;
      4, 2, 2, 3, 0, 4;
      1, 1, 4, 3, 0, 0;
      3, 2, 4, 2, 0, 0;
      2, 4, 3, 2, 0, 2;
      2, 2, 4, 3, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 7, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 2, 1, 4, 0;
      0, 2, 0, 4, 4, 1;
      0, 3, 3, 3, 2, 1;
      1, 4, 1, 1, 4, 4;
      0, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2723 : Certificate {0, 1, 5, 7, 9, 11} := by
  refine ⟨!![4, 2, 4, 0, 4, 0;
      3, 2, 4, 4, 1, 0;
      1, 3, 2, 4, 0, 1;
      4, 1, 4, 3, 3, 4;
      2, 2, 4, 2, 1, 2;
      4, 2, 0, 3, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 7, 9, 11} =
      !![0, 0, 0, 4, 1, 2;
      0, 3, 2, 2, 4, 2;
      0, 2, 0, 4, 3, 3;
      4, 2, 3, 3, 2, 1;
      4, 4, 4, 1, 4, 4;
      4, 4, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2725 : Certificate {0, 2, 5, 7, 9, 11} := by
  refine ⟨!![0, 1, 2, 3, 1, 0;
      1, 3, 0, 1, 0, 4;
      0, 4, 4, 1, 3, 1;
      3, 4, 2, 4, 0, 1;
      2, 0, 3, 3, 2, 0;
      2, 2, 3, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 7, 9, 11} =
      !![0, 0, 4, 1, 4, 0;
      0, 2, 2, 2, 4, 2;
      0, 1, 0, 4, 3, 3;
      4, 0, 3, 3, 2, 1;
      4, 1, 4, 1, 4, 4;
      4, 0, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2726 : Certificate {1, 2, 5, 7, 9, 11} := by
  refine ⟨!![0, 3, 1, 4, 3, 0;
      1, 0, 4, 1, 2, 3;
      0, 0, 1, 4, 4, 1;
      3, 4, 2, 1, 0, 3;
      2, 1, 0, 4, 3, 3;
      2, 0, 4, 0, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 7, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 2, 4, 2;
      2, 1, 0, 4, 3, 3;
      2, 0, 3, 3, 2, 1;
      4, 1, 4, 1, 4, 4;
      4, 0, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2729 : Certificate {0, 3, 5, 7, 9, 11} := by
  refine ⟨!![1, 4, 4, 1, 4, 4;
      2, 1, 3, 0, 2, 3;
      3, 3, 3, 3, 4, 3;
      2, 1, 0, 1, 2, 2;
      4, 1, 1, 3, 4, 3;
      2, 2, 4, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 7, 9, 11} =
      !![0, 3, 4, 1, 4, 0;
      0, 2, 0, 4, 1, 2;
      0, 2, 0, 4, 3, 3;
      4, 3, 3, 3, 2, 1;
      4, 4, 4, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2730 : Certificate {1, 3, 5, 7, 9, 11} := by
  refine ⟨!![4, 4, 1, 3, 0, 2;
      2, 0, 3, 2, 4, 1;
      4, 0, 2, 3, 2, 3;
      4, 2, 3, 2, 4, 1;
      3, 3, 2, 0, 3, 1;
      1, 0, 0, 4, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 7, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 0, 4, 1, 2;
      2, 2, 0, 4, 3, 3;
      2, 3, 3, 3, 2, 1;
      4, 4, 4, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2732 : Certificate {2, 3, 5, 7, 9, 11} := by
  refine ⟨!![3, 3, 4, 4, 2, 1;
      1, 4, 0, 4, 0, 4;
      2, 3, 1, 2, 4, 4;
      0, 3, 4, 2, 1, 1;
      1, 1, 3, 2, 2, 4;
      4, 3, 4, 3, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 7, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 4, 1, 4, 0;
      1, 2, 0, 4, 3, 3;
      0, 3, 3, 3, 2, 1;
      1, 4, 4, 1, 4, 4;
      0, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2737 : Certificate {0, 4, 5, 7, 9, 11} := by
  refine ⟨!![1, 1, 3, 2, 3, 4;
      2, 0, 1, 2, 0, 3;
      1, 2, 0, 3, 2, 0;
      0, 1, 4, 4, 2, 4;
      2, 4, 1, 0, 0, 0;
      3, 4, 1, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 7, 9, 11} =
      !![0, 2, 4, 1, 4, 0;
      0, 1, 0, 4, 1, 2;
      0, 2, 2, 2, 4, 2;
      4, 3, 3, 3, 2, 1;
      4, 1, 4, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2738 : Certificate {1, 4, 5, 7, 9, 11} := by
  refine ⟨!![1, 0, 3, 0, 0, 3;
      3, 3, 4, 3, 4, 4;
      2, 1, 3, 1, 4, 2;
      1, 1, 2, 4, 2, 2;
      4, 2, 2, 1, 4, 4;
      2, 1, 3, 0, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 7, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 1, 0, 4, 1, 2;
      3, 2, 2, 2, 4, 2;
      2, 3, 3, 3, 2, 1;
      4, 1, 4, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2740 : Certificate {2, 4, 5, 7, 9, 11} := by
  refine ⟨!![1, 0, 3, 0, 0, 3;
      3, 2, 0, 2, 0, 2;
      1, 4, 2, 4, 1, 0;
      4, 4, 3, 2, 4, 2;
      4, 3, 1, 2, 3, 1;
      3, 4, 3, 3, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 7, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 4, 1, 4, 0;
      2, 2, 2, 2, 4, 2;
      0, 3, 3, 3, 2, 1;
      1, 1, 4, 1, 4, 4;
      0, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2744 : Certificate {3, 4, 5, 7, 9, 11} := by
  refine ⟨!![4, 1, 1, 2, 3, 1;
      1, 4, 2, 1, 1, 4;
      4, 2, 3, 0, 0, 1;
      4, 3, 4, 0, 1, 3;
      4, 1, 3, 3, 2, 3;
      3, 3, 4, 1, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 7, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 4, 1, 4, 0;
      2, 1, 0, 4, 1, 2;
      3, 3, 3, 3, 2, 1;
      4, 1, 4, 1, 4, 4;
      3, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2755 : Certificate {0, 1, 6, 7, 9, 11} := by
  refine ⟨!![1, 4, 2, 2, 2, 2;
      2, 4, 2, 0, 1, 4;
      1, 1, 4, 1, 4, 1;
      1, 4, 1, 4, 4, 1;
      4, 3, 3, 0, 1, 4;
      4, 3, 4, 2, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 6, 7, 9, 11} =
      !![0, 0, 0, 4, 1, 2;
      0, 3, 3, 2, 4, 2;
      0, 2, 3, 4, 3, 3;
      0, 4, 3, 4, 4, 1;
      4, 4, 0, 1, 4, 4;
      4, 4, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2757 : Certificate {0, 2, 6, 7, 9, 11} := by
  refine ⟨!![4, 2, 3, 3, 3, 1;
      4, 0, 2, 1, 4, 1;
      2, 4, 4, 4, 3, 2;
      0, 2, 0, 4, 1, 4;
      3, 0, 3, 2, 2, 3;
      2, 0, 1, 0, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 6, 7, 9, 11} =
      !![0, 0, 2, 1, 4, 0;
      0, 2, 3, 2, 4, 2;
      0, 1, 3, 4, 3, 3;
      0, 0, 3, 4, 4, 1;
      4, 1, 0, 1, 4, 4;
      4, 0, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2758 : Certificate {1, 2, 6, 7, 9, 11} := by
  refine ⟨!![1, 4, 1, 2, 1, 0;
      2, 1, 1, 2, 3, 0;
      4, 4, 4, 3, 3, 4;
      3, 4, 3, 0, 4, 4;
      1, 0, 3, 3, 2, 1;
      3, 1, 0, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 6, 7, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 3, 2, 4, 2;
      2, 1, 3, 4, 3, 3;
      4, 0, 3, 4, 4, 1;
      4, 1, 0, 1, 4, 4;
      4, 0, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2761 : Certificate {0, 3, 6, 7, 9, 11} := by
  refine ⟨!![0, 4, 0, 2, 1, 3;
      2, 0, 1, 3, 2, 3;
      0, 3, 1, 1, 0, 0;
      1, 4, 2, 3, 4, 1;
      1, 0, 2, 4, 0, 0;
      3, 0, 4, 4, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 6, 7, 9, 11} =
      !![0, 3, 2, 1, 4, 0;
      0, 2, 0, 4, 1, 2;
      0, 2, 3, 4, 3, 3;
      0, 2, 3, 4, 4, 1;
      4, 4, 0, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2762 : Certificate {1, 3, 6, 7, 9, 11} := by
  refine ⟨!![0, 1, 0, 3, 4, 2;
      1, 3, 4, 2, 0, 1;
      0, 2, 1, 3, 1, 3;
      3, 4, 1, 3, 2, 2;
      3, 1, 1, 2, 2, 3;
      4, 4, 1, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 6, 7, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 0, 4, 1, 2;
      2, 2, 3, 4, 3, 3;
      4, 2, 3, 4, 4, 1;
      4, 4, 0, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2764 : Certificate {2, 3, 6, 7, 9, 11} := by
  refine ⟨!![4, 2, 2, 0, 4, 3;
      3, 1, 0, 3, 0, 4;
      4, 2, 3, 2, 2, 2;
      0, 1, 2, 1, 3, 3;
      2, 2, 3, 4, 2, 4;
      4, 0, 1, 4, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 6, 7, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 3, 2, 1, 4, 0;
      1, 2, 3, 4, 3, 3;
      0, 2, 3, 4, 4, 1;
      1, 4, 0, 1, 4, 4;
      0, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2769 : Certificate {0, 4, 6, 7, 9, 11} := by
  refine ⟨!![2, 3, 3, 0, 0, 4;
      2, 4, 3, 3, 4, 1;
      2, 1, 1, 4, 1, 4;
      1, 2, 1, 3, 3, 2;
      3, 2, 4, 2, 3, 2;
      3, 1, 2, 4, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 6, 7, 9, 11} =
      !![0, 2, 2, 1, 4, 0;
      0, 1, 0, 4, 1, 2;
      0, 2, 3, 2, 4, 2;
      0, 0, 3, 4, 4, 1;
      4, 1, 0, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2770 : Certificate {1, 4, 6, 7, 9, 11} := by
  refine ⟨!![2, 3, 4, 4, 1, 1;
      3, 3, 1, 4, 3, 1;
      2, 1, 2, 3, 2, 1;
      0, 3, 2, 3, 3, 0;
      0, 0, 2, 2, 3, 1;
      1, 3, 2, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 6, 7, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 1, 0, 4, 1, 2;
      3, 2, 3, 2, 4, 2;
      4, 0, 3, 4, 4, 1;
      4, 1, 0, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2772 : Certificate {2, 4, 6, 7, 9, 11} := by
  refine ⟨!![4, 1, 2, 3, 2, 4;
      2, 4, 0, 2, 0, 1;
      1, 2, 3, 1, 4, 2;
      1, 2, 2, 0, 1, 2;
      2, 3, 3, 1, 4, 3;
      0, 4, 1, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 6, 7, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 2, 1, 4, 0;
      2, 2, 3, 2, 4, 2;
      0, 0, 3, 4, 4, 1;
      1, 1, 0, 1, 4, 4;
      0, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2776 : Certificate {3, 4, 6, 7, 9, 11} := by
  refine ⟨!![3, 1, 1, 1, 4, 1;
      0, 0, 1, 3, 4, 2;
      3, 4, 1, 0, 0, 2;
      1, 4, 3, 0, 1, 1;
      1, 4, 0, 4, 1, 2;
      2, 4, 3, 3, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 6, 7, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 2, 1, 4, 0;
      2, 1, 0, 4, 1, 2;
      2, 0, 3, 4, 4, 1;
      4, 1, 0, 1, 4, 4;
      3, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2785 : Certificate {0, 5, 6, 7, 9, 11} := by
  refine ⟨!![2, 0, 2, 2, 1, 3;
      0, 3, 1, 3, 4, 1;
      1, 3, 0, 4, 1, 4;
      4, 0, 2, 2, 0, 0;
      0, 3, 1, 2, 3, 2;
      2, 4, 3, 0, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 6, 7, 9, 11} =
      !![0, 4, 2, 1, 4, 0;
      0, 0, 0, 4, 1, 2;
      0, 2, 3, 2, 4, 2;
      0, 0, 3, 4, 3, 3;
      4, 4, 0, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2786 : Certificate {1, 5, 6, 7, 9, 11} := by
  refine ⟨!![1, 4, 0, 4, 4, 3;
      1, 2, 1, 2, 3, 4;
      0, 3, 4, 3, 3, 0;
      2, 3, 3, 1, 1, 0;
      3, 0, 1, 4, 0, 1;
      2, 2, 1, 1, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 6, 7, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 0, 0, 4, 1, 2;
      3, 2, 3, 2, 4, 2;
      2, 0, 3, 4, 3, 3;
      4, 4, 0, 1, 4, 4;
      4, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2788 : Certificate {2, 5, 6, 7, 9, 11} := by
  refine ⟨!![0, 1, 1, 1, 3, 4;
      3, 2, 3, 2, 2, 3;
      3, 2, 1, 2, 1, 2;
      0, 3, 1, 1, 2, 1;
      3, 4, 0, 3, 2, 2;
      4, 3, 4, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 6, 7, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 4, 2, 1, 4, 0;
      2, 2, 3, 2, 4, 2;
      1, 0, 3, 4, 3, 3;
      1, 4, 0, 1, 4, 4;
      0, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2792 : Certificate {3, 5, 6, 7, 9, 11} := by
  refine ⟨!![1, 0, 4, 4, 4, 3;
      3, 4, 0, 4, 3, 1;
      2, 1, 1, 2, 4, 0;
      2, 2, 3, 3, 2, 3;
      1, 4, 2, 0, 4, 1;
      2, 4, 2, 0, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 6, 7, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 4, 2, 1, 4, 0;
      2, 0, 0, 4, 1, 2;
      2, 0, 3, 4, 3, 3;
      4, 4, 0, 1, 4, 4;
      3, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2800 : Certificate {4, 5, 6, 7, 9, 11} := by
  refine ⟨!![1, 1, 4, 1, 2, 2;
      0, 2, 3, 3, 0, 4;
      3, 0, 0, 4, 0, 4;
      1, 3, 4, 1, 1, 4;
      4, 2, 4, 3, 0, 2;
      3, 0, 1, 1, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 6, 7, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      2, 4, 2, 1, 4, 0;
      1, 0, 0, 4, 1, 2;
      2, 2, 3, 2, 4, 2;
      1, 4, 0, 1, 4, 4;
      3, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 2695 then
    if mask < 2637 then
      if mask < 2606 then
        if mask < 2590 then
          if mask < 2587 then
            if mask < 2583 then
              ⟨{0, 1, 2, 3, 9, 11}, certificate_2575⟩
            else
              ⟨{0, 1, 2, 4, 9, 11}, certificate_2583⟩
          else
            if mask < 2589 then
              ⟨{0, 1, 3, 4, 9, 11}, certificate_2587⟩
            else
              ⟨{0, 2, 3, 4, 9, 11}, certificate_2589⟩
        else
          if mask < 2603 then
            if mask < 2599 then
              ⟨{1, 2, 3, 4, 9, 11}, certificate_2590⟩
            else
              ⟨{0, 1, 2, 5, 9, 11}, certificate_2599⟩
          else
            if mask < 2605 then
              ⟨{0, 1, 3, 5, 9, 11}, certificate_2603⟩
            else
              ⟨{0, 2, 3, 5, 9, 11}, certificate_2605⟩
      else
        if mask < 2617 then
          if mask < 2613 then
            if mask < 2611 then
              ⟨{1, 2, 3, 5, 9, 11}, certificate_2606⟩
            else
              ⟨{0, 1, 4, 5, 9, 11}, certificate_2611⟩
          else
            if mask < 2614 then
              ⟨{0, 2, 4, 5, 9, 11}, certificate_2613⟩
            else
              ⟨{1, 2, 4, 5, 9, 11}, certificate_2614⟩
        else
          if mask < 2620 then
            if mask < 2618 then
              ⟨{0, 3, 4, 5, 9, 11}, certificate_2617⟩
            else
              ⟨{1, 3, 4, 5, 9, 11}, certificate_2618⟩
          else
            if mask < 2631 then
              ⟨{2, 3, 4, 5, 9, 11}, certificate_2620⟩
            else
              if mask < 2635 then
                ⟨{0, 1, 2, 6, 9, 11}, certificate_2631⟩
              else
                ⟨{0, 1, 3, 6, 9, 11}, certificate_2635⟩
    else
      if mask < 2661 then
        if mask < 2646 then
          if mask < 2643 then
            if mask < 2638 then
              ⟨{0, 2, 3, 6, 9, 11}, certificate_2637⟩
            else
              ⟨{1, 2, 3, 6, 9, 11}, certificate_2638⟩
          else
            if mask < 2645 then
              ⟨{0, 1, 4, 6, 9, 11}, certificate_2643⟩
            else
              ⟨{0, 2, 4, 6, 9, 11}, certificate_2645⟩
        else
          if mask < 2650 then
            if mask < 2649 then
              ⟨{1, 2, 4, 6, 9, 11}, certificate_2646⟩
            else
              ⟨{0, 3, 4, 6, 9, 11}, certificate_2649⟩
          else
            if mask < 2652 then
              ⟨{1, 3, 4, 6, 9, 11}, certificate_2650⟩
            else
              if mask < 2659 then
                ⟨{2, 3, 4, 6, 9, 11}, certificate_2652⟩
              else
                ⟨{0, 1, 5, 6, 9, 11}, certificate_2659⟩
      else
        if mask < 2668 then
          if mask < 2665 then
            if mask < 2662 then
              ⟨{0, 2, 5, 6, 9, 11}, certificate_2661⟩
            else
              ⟨{1, 2, 5, 6, 9, 11}, certificate_2662⟩
          else
            if mask < 2666 then
              ⟨{0, 3, 5, 6, 9, 11}, certificate_2665⟩
            else
              ⟨{1, 3, 5, 6, 9, 11}, certificate_2666⟩
        else
          if mask < 2674 then
            if mask < 2673 then
              ⟨{2, 3, 5, 6, 9, 11}, certificate_2668⟩
            else
              ⟨{0, 4, 5, 6, 9, 11}, certificate_2673⟩
          else
            if mask < 2676 then
              ⟨{1, 4, 5, 6, 9, 11}, certificate_2674⟩
            else
              if mask < 2680 then
                ⟨{2, 4, 5, 6, 9, 11}, certificate_2676⟩
              else
                ⟨{3, 4, 5, 6, 9, 11}, certificate_2680⟩
  else
    if mask < 2738 then
      if mask < 2714 then
        if mask < 2707 then
          if mask < 2701 then
            if mask < 2699 then
              ⟨{0, 1, 2, 7, 9, 11}, certificate_2695⟩
            else
              ⟨{0, 1, 3, 7, 9, 11}, certificate_2699⟩
          else
            if mask < 2702 then
              ⟨{0, 2, 3, 7, 9, 11}, certificate_2701⟩
            else
              ⟨{1, 2, 3, 7, 9, 11}, certificate_2702⟩
        else
          if mask < 2710 then
            if mask < 2709 then
              ⟨{0, 1, 4, 7, 9, 11}, certificate_2707⟩
            else
              ⟨{0, 2, 4, 7, 9, 11}, certificate_2709⟩
          else
            if mask < 2713 then
              ⟨{1, 2, 4, 7, 9, 11}, certificate_2710⟩
            else
              ⟨{0, 3, 4, 7, 9, 11}, certificate_2713⟩
      else
        if mask < 2726 then
          if mask < 2723 then
            if mask < 2716 then
              ⟨{1, 3, 4, 7, 9, 11}, certificate_2714⟩
            else
              ⟨{2, 3, 4, 7, 9, 11}, certificate_2716⟩
          else
            if mask < 2725 then
              ⟨{0, 1, 5, 7, 9, 11}, certificate_2723⟩
            else
              ⟨{0, 2, 5, 7, 9, 11}, certificate_2725⟩
        else
          if mask < 2730 then
            if mask < 2729 then
              ⟨{1, 2, 5, 7, 9, 11}, certificate_2726⟩
            else
              ⟨{0, 3, 5, 7, 9, 11}, certificate_2729⟩
          else
            if mask < 2732 then
              ⟨{1, 3, 5, 7, 9, 11}, certificate_2730⟩
            else
              if mask < 2737 then
                ⟨{2, 3, 5, 7, 9, 11}, certificate_2732⟩
              else
                ⟨{0, 4, 5, 7, 9, 11}, certificate_2737⟩
    else
      if mask < 2769 then
        if mask < 2757 then
          if mask < 2744 then
            if mask < 2740 then
              ⟨{1, 4, 5, 7, 9, 11}, certificate_2738⟩
            else
              ⟨{2, 4, 5, 7, 9, 11}, certificate_2740⟩
          else
            if mask < 2755 then
              ⟨{3, 4, 5, 7, 9, 11}, certificate_2744⟩
            else
              ⟨{0, 1, 6, 7, 9, 11}, certificate_2755⟩
        else
          if mask < 2761 then
            if mask < 2758 then
              ⟨{0, 2, 6, 7, 9, 11}, certificate_2757⟩
            else
              ⟨{1, 2, 6, 7, 9, 11}, certificate_2758⟩
          else
            if mask < 2762 then
              ⟨{0, 3, 6, 7, 9, 11}, certificate_2761⟩
            else
              if mask < 2764 then
                ⟨{1, 3, 6, 7, 9, 11}, certificate_2762⟩
              else
                ⟨{2, 3, 6, 7, 9, 11}, certificate_2764⟩
      else
        if mask < 2785 then
          if mask < 2772 then
            if mask < 2770 then
              ⟨{0, 4, 6, 7, 9, 11}, certificate_2769⟩
            else
              ⟨{1, 4, 6, 7, 9, 11}, certificate_2770⟩
          else
            if mask < 2776 then
              ⟨{2, 4, 6, 7, 9, 11}, certificate_2772⟩
            else
              ⟨{3, 4, 6, 7, 9, 11}, certificate_2776⟩
        else
          if mask < 2788 then
            if mask < 2786 then
              ⟨{0, 5, 6, 7, 9, 11}, certificate_2785⟩
            else
              ⟨{1, 5, 6, 7, 9, 11}, certificate_2786⟩
          else
            if mask < 2792 then
              ⟨{2, 5, 6, 7, 9, 11}, certificate_2788⟩
            else
              if mask < 2800 then
                ⟨{3, 5, 6, 7, 9, 11}, certificate_2792⟩
              else
                ⟨{4, 5, 6, 7, 9, 11}, certificate_2800⟩
end AMEProbe.QuinaryDirect.Batch10
#print axioms AMEProbe.QuinaryDirect.Batch10.lookup
