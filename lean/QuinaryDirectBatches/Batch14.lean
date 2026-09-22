import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch14
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_3591 : Certificate {0, 1, 2, 9, 10, 11} := by
  refine ⟨!![4, 4, 3, 3, 4, 2;
      0, 0, 2, 4, 3, 3;
      3, 2, 4, 2, 0, 3;
      3, 3, 2, 4, 0, 1;
      1, 4, 4, 1, 0, 4;
      0, 1, 3, 0, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 9, 10, 11} =
      !![0, 3, 2, 4, 3, 2;
      0, 2, 1, 3, 3, 3;
      0, 4, 0, 4, 3, 1;
      4, 2, 0, 2, 3, 1;
      4, 1, 4, 4, 0, 4;
      4, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3595 : Certificate {0, 1, 3, 9, 10, 11} := by
  refine ⟨!![3, 4, 4, 1, 1, 2;
      3, 1, 0, 3, 0, 2;
      3, 1, 3, 4, 2, 4;
      2, 0, 0, 3, 3, 4;
      0, 0, 1, 2, 0, 3;
      4, 4, 2, 2, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 9, 10, 11} =
      !![0, 0, 2, 1, 0, 2;
      0, 2, 2, 3, 3, 3;
      0, 4, 2, 4, 3, 1;
      4, 2, 3, 2, 3, 1;
      4, 1, 2, 4, 0, 4;
      4, 4, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3597 : Certificate {0, 2, 3, 9, 10, 11} := by
  refine ⟨!![4, 2, 2, 3, 4, 2;
      3, 3, 1, 0, 1, 4;
      0, 0, 3, 1, 2, 2;
      3, 4, 1, 1, 4, 0;
      1, 1, 3, 2, 2, 1;
      0, 1, 2, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 9, 10, 11} =
      !![0, 0, 3, 4, 4, 0;
      0, 1, 2, 3, 3, 3;
      0, 0, 2, 4, 3, 1;
      4, 0, 3, 2, 3, 1;
      4, 4, 2, 4, 0, 4;
      4, 1, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3598 : Certificate {1, 2, 3, 9, 10, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 0;
      3, 4, 0, 2, 3, 0;
      1, 0, 4, 2, 2, 2;
      2, 0, 4, 2, 1, 1;
      1, 3, 1, 1, 1, 3;
      3, 1, 0, 1, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 9, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      2, 1, 2, 3, 3, 3;
      4, 0, 2, 4, 3, 1;
      2, 0, 3, 2, 3, 1;
      1, 4, 2, 4, 0, 4;
      4, 1, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3603 : Certificate {0, 1, 4, 9, 10, 11} := by
  refine ⟨!![0, 3, 0, 4, 4, 1;
      2, 4, 1, 1, 1, 3;
      4, 3, 3, 4, 1, 0;
      4, 4, 4, 0, 1, 4;
      4, 3, 4, 1, 1, 3;
      4, 4, 4, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 9, 10, 11} =
      !![0, 0, 1, 1, 0, 2;
      0, 3, 2, 4, 3, 2;
      0, 4, 0, 4, 3, 1;
      4, 2, 3, 2, 3, 1;
      4, 1, 4, 4, 0, 4;
      4, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3605 : Certificate {0, 2, 4, 9, 10, 11} := by
  refine ⟨!![3, 1, 1, 3, 4, 2;
      4, 4, 3, 2, 0, 3;
      0, 0, 1, 2, 4, 4;
      1, 2, 4, 1, 4, 0;
      3, 3, 3, 3, 4, 3;
      2, 3, 1, 2, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 9, 10, 11} =
      !![0, 0, 2, 4, 4, 0;
      0, 2, 2, 4, 3, 2;
      0, 0, 0, 4, 3, 1;
      4, 0, 3, 2, 3, 1;
      4, 4, 4, 4, 0, 4;
      4, 1, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3606 : Certificate {1, 2, 4, 9, 10, 11} := by
  refine ⟨!![3, 0, 4, 0, 4, 4;
      0, 1, 0, 3, 3, 2;
      1, 0, 4, 2, 2, 2;
      1, 0, 0, 0, 4, 4;
      1, 2, 0, 0, 3, 4;
      1, 4, 0, 0, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 9, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 4, 3, 2;
      4, 0, 0, 4, 3, 1;
      2, 0, 3, 2, 3, 1;
      1, 4, 4, 4, 0, 4;
      4, 1, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3609 : Certificate {0, 3, 4, 9, 10, 11} := by
  refine ⟨!![1, 3, 1, 1, 3, 0;
      3, 1, 4, 2, 3, 0;
      4, 3, 3, 3, 3, 4;
      2, 1, 4, 2, 2, 1;
      4, 3, 4, 0, 3, 2;
      4, 0, 0, 3, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 9, 10, 11} =
      !![0, 3, 2, 4, 4, 0;
      0, 2, 1, 1, 0, 2;
      0, 2, 0, 4, 3, 1;
      4, 3, 3, 2, 3, 1;
      4, 2, 4, 4, 0, 4;
      4, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3610 : Certificate {1, 3, 4, 9, 10, 11} := by
  refine ⟨!![2, 4, 3, 3, 4, 1;
      3, 3, 3, 1, 0, 4;
      3, 2, 1, 1, 2, 3;
      4, 3, 3, 1, 4, 3;
      3, 2, 2, 3, 2, 1;
      1, 0, 0, 3, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 9, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 1, 1, 0, 2;
      4, 2, 0, 4, 3, 1;
      2, 3, 3, 2, 3, 1;
      1, 2, 4, 4, 0, 4;
      4, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3612 : Certificate {2, 3, 4, 9, 10, 11} := by
  refine ⟨!![2, 2, 0, 0, 0, 1;
      4, 0, 2, 0, 2, 2;
      2, 0, 2, 2, 0, 0;
      0, 0, 2, 0, 1, 1;
      1, 4, 3, 4, 0, 0;
      4, 3, 0, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 9, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 2, 4, 4, 0;
      0, 2, 0, 4, 3, 1;
      0, 3, 3, 2, 3, 1;
      4, 2, 4, 4, 0, 4;
      1, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3619 : Certificate {0, 1, 5, 9, 10, 11} := by
  refine ⟨!![2, 4, 3, 4, 2, 3;
      1, 4, 3, 3, 2, 0;
      1, 3, 4, 0, 4, 1;
      0, 4, 2, 3, 0, 2;
      3, 2, 4, 4, 2, 4;
      3, 3, 4, 1, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 9, 10, 11} =
      !![0, 0, 0, 1, 0, 2;
      0, 3, 2, 4, 3, 2;
      0, 2, 0, 3, 3, 3;
      4, 2, 3, 2, 3, 1;
      4, 1, 4, 4, 0, 4;
      4, 4, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3621 : Certificate {0, 2, 5, 9, 10, 11} := by
  refine ⟨!![2, 2, 3, 3, 4, 2;
      2, 1, 1, 0, 1, 4;
      4, 1, 3, 2, 4, 4;
      1, 2, 0, 3, 3, 4;
      4, 2, 2, 0, 3, 2;
      1, 4, 3, 2, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 0;
      0, 2, 2, 4, 3, 2;
      0, 1, 0, 3, 3, 3;
      4, 0, 3, 2, 3, 1;
      4, 4, 4, 4, 0, 4;
      4, 1, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3622 : Certificate {1, 2, 5, 9, 10, 11} := by
  refine ⟨!![2, 0, 0, 3, 2, 2;
      1, 4, 3, 1, 3, 3;
      4, 2, 2, 2, 0, 4;
      3, 1, 1, 1, 4, 1;
      3, 3, 1, 1, 3, 1;
      4, 3, 4, 4, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 9, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 4, 3, 2;
      2, 1, 0, 3, 3, 3;
      2, 0, 3, 2, 3, 1;
      1, 4, 4, 4, 0, 4;
      4, 1, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3625 : Certificate {0, 3, 5, 9, 10, 11} := by
  refine ⟨!![3, 0, 1, 3, 2, 4;
      1, 3, 2, 4, 4, 2;
      0, 4, 3, 4, 0, 1;
      0, 4, 4, 0, 3, 2;
      2, 1, 4, 3, 4, 3;
      4, 3, 1, 1, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 9, 10, 11} =
      !![0, 3, 4, 4, 4, 0;
      0, 2, 0, 1, 0, 2;
      0, 2, 0, 3, 3, 3;
      4, 3, 3, 2, 3, 1;
      4, 2, 4, 4, 0, 4;
      4, 4, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3626 : Certificate {1, 3, 5, 9, 10, 11} := by
  refine ⟨!![3, 3, 0, 0, 3, 2;
      4, 2, 0, 3, 4, 0;
      1, 0, 3, 4, 1, 0;
      3, 2, 4, 0, 1, 4;
      2, 3, 0, 1, 3, 0;
      2, 0, 3, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 9, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 0, 1, 0, 2;
      2, 2, 0, 3, 3, 3;
      2, 3, 3, 2, 3, 1;
      1, 2, 4, 4, 0, 4;
      4, 4, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3628 : Certificate {2, 3, 5, 9, 10, 11} := by
  refine ⟨!![0, 1, 2, 1, 4, 3;
      2, 0, 0, 3, 2, 2;
      1, 3, 4, 2, 3, 4;
      1, 4, 2, 4, 0, 3;
      4, 2, 4, 3, 3, 4;
      2, 2, 2, 4, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 9, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 4, 4, 4, 0;
      1, 2, 0, 3, 3, 3;
      0, 3, 3, 2, 3, 1;
      4, 2, 4, 4, 0, 4;
      1, 4, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3633 : Certificate {0, 4, 5, 9, 10, 11} := by
  refine ⟨!![3, 3, 2, 2, 3, 4;
      1, 4, 4, 2, 1, 2;
      4, 4, 2, 4, 2, 4;
      0, 1, 3, 1, 2, 2;
      2, 3, 3, 4, 3, 3;
      2, 3, 4, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 9, 10, 11} =
      !![0, 2, 4, 4, 4, 0;
      0, 1, 0, 1, 0, 2;
      0, 2, 2, 4, 3, 2;
      4, 3, 3, 2, 3, 1;
      4, 4, 4, 4, 0, 4;
      4, 1, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3634 : Certificate {1, 4, 5, 9, 10, 11} := by
  refine ⟨!![4, 1, 0, 2, 4, 2;
      2, 1, 0, 4, 2, 0;
      0, 0, 1, 3, 3, 2;
      1, 0, 3, 4, 3, 0;
      1, 0, 0, 4, 2, 0;
      1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 9, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 1, 0, 1, 0, 2;
      3, 2, 2, 4, 3, 2;
      2, 3, 3, 2, 3, 1;
      1, 4, 4, 4, 0, 4;
      4, 1, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3636 : Certificate {2, 4, 5, 9, 10, 11} := by
  refine ⟨!![3, 3, 2, 1, 1, 3;
      3, 0, 0, 2, 3, 3;
      2, 2, 4, 2, 2, 4;
      2, 1, 2, 1, 0, 1;
      2, 1, 4, 1, 4, 1;
      0, 4, 2, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 9, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 4, 4, 4, 0;
      2, 2, 2, 4, 3, 2;
      0, 3, 3, 2, 3, 1;
      4, 4, 4, 4, 0, 4;
      1, 1, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3640 : Certificate {3, 4, 5, 9, 10, 11} := by
  refine ⟨!![1, 0, 4, 3, 1, 3;
      4, 0, 4, 0, 4, 1;
      1, 1, 0, 0, 0, 3;
      0, 3, 4, 3, 0, 1;
      0, 0, 1, 1, 1, 2;
      2, 1, 0, 3, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 9, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 4, 4, 4, 0;
      2, 1, 0, 1, 0, 2;
      3, 3, 3, 2, 3, 1;
      2, 4, 4, 4, 0, 4;
      4, 1, 4, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3651 : Certificate {0, 1, 6, 9, 10, 11} := by
  refine ⟨!![1, 0, 0, 2, 3, 1;
      3, 3, 3, 4, 0, 0;
      2, 1, 3, 0, 3, 2;
      0, 2, 4, 4, 0, 0;
      3, 1, 0, 2, 2, 3;
      3, 4, 3, 3, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 6, 9, 10, 11} =
      !![0, 0, 0, 1, 0, 2;
      0, 3, 3, 4, 3, 2;
      0, 2, 3, 3, 3, 3;
      0, 4, 3, 4, 3, 1;
      4, 1, 3, 4, 0, 4;
      4, 4, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3653 : Certificate {0, 2, 6, 9, 10, 11} := by
  refine ⟨!![0, 4, 4, 4, 3, 1;
      1, 2, 4, 4, 1, 4;
      2, 3, 4, 2, 0, 0;
      2, 1, 2, 2, 2, 3;
      1, 0, 1, 2, 3, 2;
      3, 2, 2, 1, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 6, 9, 10, 11} =
      !![0, 0, 2, 4, 4, 0;
      0, 2, 3, 4, 3, 2;
      0, 1, 3, 3, 3, 3;
      0, 0, 3, 4, 3, 1;
      4, 4, 3, 4, 0, 4;
      4, 1, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3654 : Certificate {1, 2, 6, 9, 10, 11} := by
  refine ⟨!![0, 3, 3, 3, 1, 2;
      4, 3, 2, 0, 3, 1;
      3, 2, 2, 1, 3, 2;
      3, 3, 3, 4, 1, 2;
      4, 4, 2, 1, 1, 1;
      2, 3, 4, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 6, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 3, 4, 3, 2;
      2, 1, 3, 3, 3, 3;
      4, 0, 3, 4, 3, 1;
      1, 4, 3, 4, 0, 4;
      4, 1, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3657 : Certificate {0, 3, 6, 9, 10, 11} := by
  refine ⟨!![2, 2, 4, 3, 0, 4;
      3, 4, 1, 4, 3, 2;
      3, 0, 3, 1, 1, 4;
      2, 4, 1, 4, 2, 3;
      2, 3, 3, 0, 4, 1;
      1, 2, 1, 4, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 6, 9, 10, 11} =
      !![0, 3, 2, 4, 4, 0;
      0, 2, 0, 1, 0, 2;
      0, 2, 3, 3, 3, 3;
      0, 2, 3, 4, 3, 1;
      4, 2, 3, 4, 0, 4;
      4, 4, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3658 : Certificate {1, 3, 6, 9, 10, 11} := by
  refine ⟨!![1, 2, 1, 2, 4, 3;
      0, 1, 0, 2, 3, 1;
      2, 1, 4, 3, 4, 4;
      4, 0, 1, 4, 3, 1;
      2, 0, 1, 1, 2, 3;
      3, 2, 2, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 6, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 0, 1, 0, 2;
      2, 2, 3, 3, 3, 3;
      4, 2, 3, 4, 3, 1;
      1, 2, 3, 4, 0, 4;
      4, 4, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3660 : Certificate {2, 3, 6, 9, 10, 11} := by
  refine ⟨!![3, 4, 1, 2, 2, 2;
      3, 3, 4, 0, 0, 1;
      2, 4, 2, 4, 4, 2;
      2, 4, 2, 1, 0, 3;
      1, 2, 4, 2, 3, 4;
      2, 0, 1, 4, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 6, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 3, 2, 4, 4, 0;
      1, 2, 3, 3, 3, 3;
      0, 2, 3, 4, 3, 1;
      4, 2, 3, 4, 0, 4;
      1, 4, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3665 : Certificate {0, 4, 6, 9, 10, 11} := by
  refine ⟨!![3, 4, 4, 3, 1, 3;
      3, 3, 4, 1, 3, 2;
      3, 2, 2, 2, 1, 4;
      4, 0, 0, 0, 4, 1;
      2, 0, 2, 1, 4, 1;
      4, 4, 3, 2, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 6, 9, 10, 11} =
      !![0, 2, 2, 4, 4, 0;
      0, 1, 0, 1, 0, 2;
      0, 2, 3, 4, 3, 2;
      0, 0, 3, 4, 3, 1;
      4, 4, 3, 4, 0, 4;
      4, 1, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3666 : Certificate {1, 4, 6, 9, 10, 11} := by
  refine ⟨!![4, 1, 1, 0, 2, 4;
      0, 4, 0, 3, 2, 4;
      4, 4, 4, 4, 2, 0;
      2, 1, 1, 1, 2, 4;
      0, 4, 1, 4, 0, 4;
      4, 3, 2, 3, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 6, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 1, 0, 1, 0, 2;
      3, 2, 3, 4, 3, 2;
      4, 0, 3, 4, 3, 1;
      1, 4, 3, 4, 0, 4;
      4, 1, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3668 : Certificate {2, 4, 6, 9, 10, 11} := by
  refine ⟨!![1, 2, 0, 2, 2, 3;
      3, 3, 1, 1, 2, 0;
      3, 0, 0, 4, 4, 4;
      3, 0, 0, 1, 0, 0;
      4, 0, 2, 4, 2, 3;
      2, 0, 4, 3, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 6, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 2, 4, 4, 0;
      2, 2, 3, 4, 3, 2;
      0, 0, 3, 4, 3, 1;
      4, 4, 3, 4, 0, 4;
      1, 1, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3672 : Certificate {3, 4, 6, 9, 10, 11} := by
  refine ⟨!![1, 2, 0, 2, 2, 3;
      1, 2, 4, 0, 4, 2;
      1, 1, 0, 0, 0, 3;
      1, 1, 0, 2, 1, 4;
      1, 0, 3, 4, 3, 0;
      3, 4, 1, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 6, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 2, 4, 4, 0;
      2, 1, 0, 1, 0, 2;
      2, 0, 3, 4, 3, 1;
      2, 4, 3, 4, 0, 4;
      4, 1, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3681 : Certificate {0, 5, 6, 9, 10, 11} := by
  refine ⟨!![1, 4, 0, 2, 4, 0;
      3, 1, 2, 3, 3, 2;
      4, 0, 2, 2, 2, 3;
      1, 4, 3, 2, 1, 4;
      3, 0, 4, 4, 0, 0;
      2, 1, 1, 4, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 6, 9, 10, 11} =
      !![0, 4, 2, 4, 4, 0;
      0, 0, 0, 1, 0, 2;
      0, 2, 3, 4, 3, 2;
      0, 0, 3, 3, 3, 3;
      4, 4, 3, 4, 0, 4;
      4, 4, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3682 : Certificate {1, 5, 6, 9, 10, 11} := by
  refine ⟨!![2, 1, 2, 4, 3, 1;
      2, 0, 4, 1, 4, 3;
      1, 2, 3, 1, 0, 1;
      1, 3, 4, 2, 1, 2;
      3, 2, 2, 4, 0, 4;
      2, 4, 3, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 6, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 0, 0, 1, 0, 2;
      3, 2, 3, 4, 3, 2;
      2, 0, 3, 3, 3, 3;
      1, 4, 3, 4, 0, 4;
      4, 4, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3684 : Certificate {2, 5, 6, 9, 10, 11} := by
  refine ⟨!![3, 4, 3, 4, 3, 4;
      3, 3, 0, 4, 0, 1;
      4, 1, 1, 4, 1, 0;
      1, 3, 4, 3, 3, 2;
      4, 0, 3, 1, 4, 2;
      0, 3, 1, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 6, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 4, 2, 4, 4, 0;
      2, 2, 3, 4, 3, 2;
      1, 0, 3, 3, 3, 3;
      4, 4, 3, 4, 0, 4;
      1, 4, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3688 : Certificate {3, 5, 6, 9, 10, 11} := by
  refine ⟨!![0, 2, 3, 4, 3, 0;
      3, 1, 2, 0, 2, 1;
      3, 0, 3, 0, 3, 2;
      2, 0, 1, 4, 0, 0;
      1, 4, 2, 3, 3, 3;
      4, 3, 2, 4, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 6, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 4, 2, 4, 4, 0;
      2, 0, 0, 1, 0, 2;
      2, 0, 3, 3, 3, 3;
      2, 4, 3, 4, 0, 4;
      4, 4, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3696 : Certificate {4, 5, 6, 9, 10, 11} := by
  refine ⟨!![3, 2, 2, 3, 0, 4;
      4, 0, 1, 1, 2, 4;
      2, 1, 4, 4, 3, 4;
      1, 4, 4, 4, 2, 2;
      0, 1, 2, 4, 2, 0;
      3, 2, 0, 4, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 6, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      2, 4, 2, 4, 4, 0;
      1, 0, 0, 1, 0, 2;
      2, 2, 3, 4, 3, 2;
      4, 4, 3, 4, 0, 4;
      1, 4, 0, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3715 : Certificate {0, 1, 7, 9, 10, 11} := by
  refine ⟨!![4, 1, 0, 3, 3, 1;
      3, 1, 0, 3, 2, 3;
      0, 2, 3, 1, 3, 2;
      0, 0, 1, 3, 2, 3;
      0, 4, 1, 3, 3, 2;
      3, 1, 1, 4, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 7, 9, 10, 11} =
      !![0, 0, 4, 1, 0, 2;
      0, 3, 2, 4, 3, 2;
      0, 2, 4, 3, 3, 3;
      0, 4, 4, 4, 3, 1;
      4, 2, 3, 2, 3, 1;
      4, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3717 : Certificate {0, 2, 7, 9, 10, 11} := by
  refine ⟨!![2, 2, 3, 4, 1, 3;
      1, 2, 4, 0, 2, 3;
      1, 4, 2, 1, 0, 0;
      1, 2, 0, 3, 4, 1;
      4, 2, 2, 3, 1, 4;
      0, 0, 1, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 7, 9, 10, 11} =
      !![0, 0, 1, 4, 4, 0;
      0, 2, 2, 4, 3, 2;
      0, 1, 4, 3, 3, 3;
      0, 0, 4, 4, 3, 1;
      4, 0, 3, 2, 3, 1;
      4, 1, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3718 : Certificate {1, 2, 7, 9, 10, 11} := by
  refine ⟨!![3, 1, 1, 1, 2, 2;
      3, 2, 1, 4, 1, 1;
      3, 4, 4, 0, 4, 3;
      3, 2, 2, 2, 3, 4;
      2, 2, 0, 4, 2, 1;
      3, 1, 2, 2, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 7, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 2, 4, 3, 2;
      2, 1, 4, 3, 3, 3;
      4, 0, 4, 4, 3, 1;
      2, 0, 3, 2, 3, 1;
      4, 1, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3721 : Certificate {0, 3, 7, 9, 10, 11} := by
  refine ⟨!![2, 4, 3, 3, 2, 2;
      4, 1, 1, 1, 2, 3;
      0, 4, 3, 0, 4, 1;
      1, 4, 0, 2, 0, 0;
      0, 3, 1, 1, 0, 0;
      3, 2, 3, 3, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 7, 9, 10, 11} =
      !![0, 3, 1, 4, 4, 0;
      0, 2, 4, 1, 0, 2;
      0, 2, 4, 3, 3, 3;
      0, 2, 4, 4, 3, 1;
      4, 3, 3, 2, 3, 1;
      4, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3722 : Certificate {1, 3, 7, 9, 10, 11} := by
  refine ⟨!![2, 2, 4, 2, 4, 3;
      1, 4, 2, 1, 0, 3;
      4, 3, 1, 4, 2, 2;
      4, 1, 4, 2, 2, 0;
      3, 1, 2, 4, 1, 2;
      4, 0, 4, 0, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 7, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 4, 1, 0, 2;
      2, 2, 4, 3, 3, 3;
      4, 2, 4, 4, 3, 1;
      2, 3, 3, 2, 3, 1;
      4, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3724 : Certificate {2, 3, 7, 9, 10, 11} := by
  refine ⟨!![1, 2, 0, 4, 4, 1;
      1, 3, 4, 3, 3, 1;
      1, 0, 0, 1, 1, 0;
      0, 4, 2, 4, 3, 3;
      4, 4, 0, 1, 2, 0;
      2, 1, 4, 2, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 7, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 3, 1, 4, 4, 0;
      1, 2, 4, 3, 3, 3;
      0, 2, 4, 4, 3, 1;
      0, 3, 3, 2, 3, 1;
      1, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3729 : Certificate {0, 4, 7, 9, 10, 11} := by
  refine ⟨!![0, 2, 2, 1, 0, 4;
      0, 2, 4, 2, 3, 2;
      3, 0, 3, 1, 4, 1;
      1, 2, 1, 0, 2, 3;
      1, 2, 0, 0, 3, 2;
      1, 1, 4, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 7, 9, 10, 11} =
      !![0, 2, 1, 4, 4, 0;
      0, 1, 4, 1, 0, 2;
      0, 2, 2, 4, 3, 2;
      0, 0, 4, 4, 3, 1;
      4, 3, 3, 2, 3, 1;
      4, 1, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3730 : Certificate {1, 4, 7, 9, 10, 11} := by
  refine ⟨!![0, 2, 2, 1, 0, 4;
      0, 4, 1, 3, 3, 1;
      1, 1, 0, 1, 2, 3;
      2, 1, 2, 1, 3, 1;
      2, 1, 1, 1, 4, 0;
      2, 1, 1, 1, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 7, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 1, 4, 1, 0, 2;
      3, 2, 2, 4, 3, 2;
      4, 0, 4, 4, 3, 1;
      2, 3, 3, 2, 3, 1;
      4, 1, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3732 : Certificate {2, 4, 7, 9, 10, 11} := by
  refine ⟨!![3, 1, 3, 1, 4, 0;
      4, 3, 1, 4, 0, 3;
      4, 1, 2, 4, 1, 1;
      4, 4, 3, 2, 4, 4;
      3, 2, 1, 0, 2, 3;
      4, 4, 2, 2, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 7, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 1, 4, 4, 0;
      2, 2, 2, 4, 3, 2;
      0, 0, 4, 4, 3, 1;
      0, 3, 3, 2, 3, 1;
      1, 1, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3736 : Certificate {3, 4, 7, 9, 10, 11} := by
  refine ⟨!![2, 4, 3, 3, 1, 1;
      3, 1, 0, 2, 2, 3;
      2, 2, 0, 0, 0, 1;
      2, 0, 4, 0, 3, 2;
      2, 0, 0, 3, 4, 3;
      4, 4, 3, 1, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 7, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 1, 4, 4, 0;
      2, 1, 4, 1, 0, 2;
      2, 0, 4, 4, 3, 1;
      3, 3, 3, 2, 3, 1;
      4, 1, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3745 : Certificate {0, 5, 7, 9, 10, 11} := by
  refine ⟨!![0, 1, 0, 0, 1, 3;
      1, 0, 2, 4, 2, 3;
      4, 4, 3, 4, 2, 3;
      2, 2, 3, 4, 4, 1;
      0, 2, 3, 1, 1, 4;
      1, 4, 0, 0, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 7, 9, 10, 11} =
      !![0, 4, 1, 4, 4, 0;
      0, 0, 4, 1, 0, 2;
      0, 2, 2, 4, 3, 2;
      0, 0, 4, 3, 3, 3;
      4, 3, 3, 2, 3, 1;
      4, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3746 : Certificate {1, 5, 7, 9, 10, 11} := by
  refine ⟨!![0, 4, 0, 0, 4, 2;
      3, 3, 4, 1, 2, 3;
      2, 4, 1, 2, 0, 2;
      1, 2, 2, 3, 3, 3;
      0, 1, 3, 1, 0, 1;
      3, 4, 2, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 7, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 0, 4, 1, 0, 2;
      3, 2, 2, 4, 3, 2;
      2, 0, 4, 3, 3, 3;
      2, 3, 3, 2, 3, 1;
      4, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3748 : Certificate {2, 5, 7, 9, 10, 11} := by
  refine ⟨!![4, 2, 1, 1, 1, 3;
      1, 4, 1, 3, 1, 0;
      1, 2, 2, 3, 2, 3;
      0, 2, 3, 4, 2, 0;
      0, 0, 3, 1, 4, 3;
      4, 3, 1, 1, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 7, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 4, 1, 4, 4, 0;
      2, 2, 2, 4, 3, 2;
      1, 0, 4, 3, 3, 3;
      0, 3, 3, 2, 3, 1;
      1, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3752 : Certificate {3, 5, 7, 9, 10, 11} := by
  refine ⟨!![0, 0, 3, 0, 3, 4;
      2, 2, 1, 2, 1, 0;
      3, 3, 3, 1, 3, 1;
      3, 1, 2, 1, 1, 2;
      3, 4, 4, 3, 0, 1;
      0, 1, 3, 0, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 7, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 4, 1, 4, 4, 0;
      2, 0, 4, 1, 0, 2;
      2, 0, 4, 3, 3, 3;
      3, 3, 3, 2, 3, 1;
      4, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3760 : Certificate {4, 5, 7, 9, 10, 11} := by
  refine ⟨!![0, 0, 3, 0, 3, 4;
      4, 3, 4, 3, 2, 3;
      4, 1, 2, 4, 1, 0;
      4, 4, 1, 4, 4, 1;
      1, 3, 3, 2, 1, 4;
      0, 1, 2, 0, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 7, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      2, 4, 1, 4, 4, 0;
      1, 0, 4, 1, 0, 2;
      2, 2, 2, 4, 3, 2;
      3, 3, 3, 2, 3, 1;
      1, 4, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3777 : Certificate {0, 6, 7, 9, 10, 11} := by
  refine ⟨!![2, 1, 4, 3, 0, 4;
      2, 4, 2, 3, 4, 0;
      0, 3, 3, 3, 4, 0;
      0, 2, 4, 1, 0, 0;
      3, 4, 3, 3, 2, 0;
      0, 1, 2, 1, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 6, 7, 9, 10, 11} =
      !![0, 2, 1, 4, 4, 0;
      0, 0, 4, 1, 0, 2;
      0, 3, 2, 4, 3, 2;
      0, 3, 4, 3, 3, 3;
      0, 3, 4, 4, 3, 1;
      4, 0, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3778 : Certificate {1, 6, 7, 9, 10, 11} := by
  refine ⟨!![2, 0, 2, 4, 3, 0;
      2, 3, 0, 4, 2, 1;
      3, 3, 1, 4, 1, 0;
      2, 2, 1, 0, 3, 0;
      1, 0, 3, 3, 1, 4;
      3, 1, 0, 2, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 6, 7, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      0, 0, 4, 1, 0, 2;
      3, 3, 2, 4, 3, 2;
      2, 3, 4, 3, 3, 3;
      4, 3, 4, 4, 3, 1;
      4, 0, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3780 : Certificate {2, 6, 7, 9, 10, 11} := by
  refine ⟨!![4, 0, 4, 3, 1, 0;
      2, 4, 3, 0, 2, 4;
      4, 4, 0, 2, 0, 3;
      4, 1, 0, 3, 1, 2;
      4, 0, 1, 4, 3, 4;
      0, 3, 3, 3, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 6, 7, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      0, 2, 1, 4, 4, 0;
      2, 3, 2, 4, 3, 2;
      1, 3, 4, 3, 3, 3;
      0, 3, 4, 4, 3, 1;
      1, 0, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3784 : Certificate {3, 6, 7, 9, 10, 11} := by
  refine ⟨!![3, 1, 3, 0, 2, 2;
      1, 3, 2, 4, 3, 2;
      0, 1, 1, 2, 4, 2;
      2, 2, 3, 3, 3, 4;
      4, 2, 1, 2, 3, 3;
      1, 1, 4, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 6, 7, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      3, 2, 1, 4, 4, 0;
      2, 0, 4, 1, 0, 2;
      2, 3, 4, 3, 3, 3;
      2, 3, 4, 4, 3, 1;
      4, 0, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3792 : Certificate {4, 6, 7, 9, 10, 11} := by
  refine ⟨!![4, 3, 4, 0, 1, 1;
      0, 0, 3, 3, 4, 1;
      2, 2, 4, 4, 2, 4;
      1, 3, 1, 1, 4, 1;
      4, 4, 2, 4, 3, 2;
      1, 3, 0, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 6, 7, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      2, 2, 1, 4, 4, 0;
      1, 0, 4, 1, 0, 2;
      2, 3, 2, 4, 3, 2;
      0, 3, 4, 4, 3, 1;
      1, 0, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3808 : Certificate {5, 6, 7, 9, 10, 11} := by
  refine ⟨!![0, 1, 3, 2, 4, 2;
      4, 2, 4, 1, 1, 0;
      4, 1, 1, 4, 0, 2;
      0, 2, 3, 3, 4, 4;
      2, 1, 3, 1, 4, 1;
      2, 2, 2, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {5, 6, 7, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      4, 2, 1, 4, 4, 0;
      0, 0, 4, 1, 0, 2;
      2, 3, 2, 4, 3, 2;
      0, 3, 4, 3, 3, 3;
      4, 0, 1, 4, 4, 4] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 3668 then
    if mask < 3626 then
      if mask < 3609 then
        if mask < 3598 then
          if mask < 3595 then
            ⟨{0, 1, 2, 9, 10, 11}, certificate_3591⟩
          else
            if mask < 3597 then
              ⟨{0, 1, 3, 9, 10, 11}, certificate_3595⟩
            else
              ⟨{0, 2, 3, 9, 10, 11}, certificate_3597⟩
        else
          if mask < 3605 then
            if mask < 3603 then
              ⟨{1, 2, 3, 9, 10, 11}, certificate_3598⟩
            else
              ⟨{0, 1, 4, 9, 10, 11}, certificate_3603⟩
          else
            if mask < 3606 then
              ⟨{0, 2, 4, 9, 10, 11}, certificate_3605⟩
            else
              ⟨{1, 2, 4, 9, 10, 11}, certificate_3606⟩
      else
        if mask < 3619 then
          if mask < 3610 then
            ⟨{0, 3, 4, 9, 10, 11}, certificate_3609⟩
          else
            if mask < 3612 then
              ⟨{1, 3, 4, 9, 10, 11}, certificate_3610⟩
            else
              ⟨{2, 3, 4, 9, 10, 11}, certificate_3612⟩
        else
          if mask < 3622 then
            if mask < 3621 then
              ⟨{0, 1, 5, 9, 10, 11}, certificate_3619⟩
            else
              ⟨{0, 2, 5, 9, 10, 11}, certificate_3621⟩
          else
            if mask < 3625 then
              ⟨{1, 2, 5, 9, 10, 11}, certificate_3622⟩
            else
              ⟨{0, 3, 5, 9, 10, 11}, certificate_3625⟩
    else
      if mask < 3653 then
        if mask < 3634 then
          if mask < 3628 then
            ⟨{1, 3, 5, 9, 10, 11}, certificate_3626⟩
          else
            if mask < 3633 then
              ⟨{2, 3, 5, 9, 10, 11}, certificate_3628⟩
            else
              ⟨{0, 4, 5, 9, 10, 11}, certificate_3633⟩
        else
          if mask < 3640 then
            if mask < 3636 then
              ⟨{1, 4, 5, 9, 10, 11}, certificate_3634⟩
            else
              ⟨{2, 4, 5, 9, 10, 11}, certificate_3636⟩
          else
            if mask < 3651 then
              ⟨{3, 4, 5, 9, 10, 11}, certificate_3640⟩
            else
              ⟨{0, 1, 6, 9, 10, 11}, certificate_3651⟩
      else
        if mask < 3658 then
          if mask < 3654 then
            ⟨{0, 2, 6, 9, 10, 11}, certificate_3653⟩
          else
            if mask < 3657 then
              ⟨{1, 2, 6, 9, 10, 11}, certificate_3654⟩
            else
              ⟨{0, 3, 6, 9, 10, 11}, certificate_3657⟩
        else
          if mask < 3665 then
            if mask < 3660 then
              ⟨{1, 3, 6, 9, 10, 11}, certificate_3658⟩
            else
              ⟨{2, 3, 6, 9, 10, 11}, certificate_3660⟩
          else
            if mask < 3666 then
              ⟨{0, 4, 6, 9, 10, 11}, certificate_3665⟩
            else
              ⟨{1, 4, 6, 9, 10, 11}, certificate_3666⟩
  else
    if mask < 3730 then
      if mask < 3715 then
        if mask < 3682 then
          if mask < 3672 then
            ⟨{2, 4, 6, 9, 10, 11}, certificate_3668⟩
          else
            if mask < 3681 then
              ⟨{3, 4, 6, 9, 10, 11}, certificate_3672⟩
            else
              ⟨{0, 5, 6, 9, 10, 11}, certificate_3681⟩
        else
          if mask < 3688 then
            if mask < 3684 then
              ⟨{1, 5, 6, 9, 10, 11}, certificate_3682⟩
            else
              ⟨{2, 5, 6, 9, 10, 11}, certificate_3684⟩
          else
            if mask < 3696 then
              ⟨{3, 5, 6, 9, 10, 11}, certificate_3688⟩
            else
              ⟨{4, 5, 6, 9, 10, 11}, certificate_3696⟩
      else
        if mask < 3721 then
          if mask < 3717 then
            ⟨{0, 1, 7, 9, 10, 11}, certificate_3715⟩
          else
            if mask < 3718 then
              ⟨{0, 2, 7, 9, 10, 11}, certificate_3717⟩
            else
              ⟨{1, 2, 7, 9, 10, 11}, certificate_3718⟩
        else
          if mask < 3724 then
            if mask < 3722 then
              ⟨{0, 3, 7, 9, 10, 11}, certificate_3721⟩
            else
              ⟨{1, 3, 7, 9, 10, 11}, certificate_3722⟩
          else
            if mask < 3729 then
              ⟨{2, 3, 7, 9, 10, 11}, certificate_3724⟩
            else
              ⟨{0, 4, 7, 9, 10, 11}, certificate_3729⟩
    else
      if mask < 3760 then
        if mask < 3745 then
          if mask < 3732 then
            ⟨{1, 4, 7, 9, 10, 11}, certificate_3730⟩
          else
            if mask < 3736 then
              ⟨{2, 4, 7, 9, 10, 11}, certificate_3732⟩
            else
              ⟨{3, 4, 7, 9, 10, 11}, certificate_3736⟩
        else
          if mask < 3748 then
            if mask < 3746 then
              ⟨{0, 5, 7, 9, 10, 11}, certificate_3745⟩
            else
              ⟨{1, 5, 7, 9, 10, 11}, certificate_3746⟩
          else
            if mask < 3752 then
              ⟨{2, 5, 7, 9, 10, 11}, certificate_3748⟩
            else
              ⟨{3, 5, 7, 9, 10, 11}, certificate_3752⟩
      else
        if mask < 3780 then
          if mask < 3777 then
            ⟨{4, 5, 7, 9, 10, 11}, certificate_3760⟩
          else
            if mask < 3778 then
              ⟨{0, 6, 7, 9, 10, 11}, certificate_3777⟩
            else
              ⟨{1, 6, 7, 9, 10, 11}, certificate_3778⟩
        else
          if mask < 3792 then
            if mask < 3784 then
              ⟨{2, 6, 7, 9, 10, 11}, certificate_3780⟩
            else
              ⟨{3, 6, 7, 9, 10, 11}, certificate_3784⟩
          else
            if mask < 3808 then
              ⟨{4, 6, 7, 9, 10, 11}, certificate_3792⟩
            else
              ⟨{5, 6, 7, 9, 10, 11}, certificate_3808⟩
end AMEProbe.QuinaryDirect.Batch14
#print axioms AMEProbe.QuinaryDirect.Batch14.lookup
