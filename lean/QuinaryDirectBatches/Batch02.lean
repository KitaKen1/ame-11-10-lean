import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch02
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_543 : Certificate {0, 1, 2, 3, 4, 9} := by
  refine ⟨!![1, 0, 1, 3, 2, 4;
      4, 1, 3, 2, 3, 3;
      1, 1, 1, 1, 1, 3;
      1, 4, 1, 4, 4, 1;
      2, 1, 3, 0, 3, 4;
      2, 2, 4, 1, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 4, 9} =
      !![0, 4, 0, 2, 0, 4;
      4, 2, 0, 3, 3, 2;
      4, 1, 4, 2, 4, 4;
      4, 4, 1, 4, 1, 4;
      4, 4, 0, 3, 3, 3;
      3, 0, 2, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_559 : Certificate {0, 1, 2, 3, 5, 9} := by
  refine ⟨!![3, 4, 3, 0, 2, 0;
      1, 3, 4, 1, 0, 1;
      2, 1, 1, 4, 3, 3;
      4, 2, 0, 0, 2, 3;
      1, 4, 2, 4, 3, 1;
      3, 3, 2, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 5, 9} =
      !![0, 2, 1, 2, 0, 3;
      4, 2, 0, 3, 3, 2;
      4, 1, 4, 2, 4, 4;
      4, 4, 1, 4, 4, 4;
      4, 4, 0, 3, 3, 3;
      3, 0, 2, 2, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_567 : Certificate {0, 1, 2, 4, 5, 9} := by
  refine ⟨!![2, 4, 1, 3, 2, 2;
      0, 0, 4, 1, 2, 4;
      4, 3, 2, 0, 0, 0;
      1, 2, 4, 4, 2, 4;
      3, 2, 4, 1, 1, 1;
      0, 4, 2, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 5, 9} =
      !![0, 3, 2, 2, 2, 4;
      4, 2, 0, 3, 3, 2;
      4, 1, 4, 4, 4, 4;
      4, 4, 1, 1, 4, 4;
      4, 4, 0, 3, 3, 3;
      3, 0, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_571 : Certificate {0, 1, 3, 4, 5, 9} := by
  refine ⟨!![4, 4, 3, 0, 1, 3;
      2, 2, 3, 2, 4, 2;
      3, 3, 1, 4, 3, 2;
      4, 4, 4, 1, 1, 0;
      4, 0, 3, 3, 0, 2;
      1, 0, 4, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 5, 9} =
      !![0, 0, 2, 1, 0, 1;
      4, 2, 3, 3, 3, 2;
      4, 1, 2, 4, 4, 4;
      4, 4, 4, 1, 4, 4;
      4, 4, 3, 3, 3, 3;
      3, 0, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_573 : Certificate {0, 2, 3, 4, 5, 9} := by
  refine ⟨!![3, 0, 4, 2, 1, 1;
      1, 0, 4, 2, 1, 4;
      0, 0, 4, 1, 2, 4;
      4, 0, 4, 0, 2, 2;
      2, 1, 0, 3, 4, 1;
      0, 4, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 5, 9} =
      !![0, 0, 3, 2, 4, 4;
      4, 0, 3, 3, 3, 2;
      4, 4, 2, 4, 4, 4;
      4, 1, 4, 1, 4, 4;
      4, 0, 3, 3, 3, 3;
      3, 2, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_574 : Certificate {1, 2, 3, 4, 5, 9} := by
  refine ⟨!![3, 2, 0, 0, 3, 0;
      3, 2, 1, 3, 2, 2;
      2, 3, 4, 1, 4, 4;
      3, 2, 2, 4, 2, 4;
      2, 4, 4, 0, 2, 2;
      4, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 5, 9} =
      !![0, 0, 0, 0, 0, 4;
      2, 0, 3, 3, 3, 2;
      1, 4, 2, 4, 4, 4;
      4, 1, 4, 1, 4, 4;
      4, 0, 3, 3, 3, 3;
      0, 2, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_591 : Certificate {0, 1, 2, 3, 6, 9} := by
  refine ⟨!![2, 0, 1, 1, 4, 4;
      0, 2, 0, 2, 0, 4;
      3, 0, 3, 3, 1, 4;
      4, 1, 4, 0, 1, 0;
      3, 1, 0, 2, 3, 0;
      2, 2, 3, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 6, 9} =
      !![0, 2, 1, 2, 3, 3;
      0, 4, 0, 2, 3, 4;
      4, 1, 4, 2, 3, 4;
      4, 4, 1, 4, 0, 4;
      4, 4, 0, 3, 3, 3;
      3, 0, 2, 2, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_599 : Certificate {0, 1, 2, 4, 6, 9} := by
  refine ⟨!![4, 2, 4, 0, 4, 3;
      3, 2, 0, 0, 1, 2;
      4, 3, 0, 2, 2, 3;
      3, 0, 0, 3, 1, 3;
      1, 4, 2, 3, 3, 1;
      0, 4, 1, 4, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 6, 9} =
      !![0, 3, 2, 2, 3, 4;
      0, 4, 0, 0, 3, 4;
      4, 1, 4, 4, 3, 4;
      4, 4, 1, 1, 0, 4;
      4, 4, 0, 3, 3, 3;
      3, 0, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_603 : Certificate {0, 1, 3, 4, 6, 9} := by
  refine ⟨!![1, 1, 3, 0, 2, 2;
      1, 3, 4, 3, 2, 3;
      1, 2, 4, 2, 0, 2;
      1, 1, 4, 1, 2, 4;
      4, 0, 3, 3, 0, 2;
      3, 0, 3, 0, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 6, 9} =
      !![0, 0, 2, 1, 0, 1;
      0, 4, 2, 0, 3, 4;
      4, 1, 2, 4, 3, 4;
      4, 4, 4, 1, 0, 4;
      4, 4, 3, 3, 3, 3;
      3, 0, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_605 : Certificate {0, 2, 3, 4, 6, 9} := by
  refine ⟨!![2, 2, 3, 4, 3, 2;
      3, 1, 1, 3, 2, 2;
      4, 2, 3, 3, 4, 0;
      0, 3, 0, 3, 0, 1;
      3, 4, 3, 4, 4, 2;
      2, 0, 0, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 6, 9} =
      !![0, 0, 3, 2, 2, 4;
      0, 0, 2, 0, 3, 4;
      4, 4, 2, 4, 3, 4;
      4, 1, 4, 1, 0, 4;
      4, 0, 3, 3, 3, 3;
      3, 2, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_606 : Certificate {1, 2, 3, 4, 6, 9} := by
  refine ⟨!![2, 3, 1, 4, 3, 1;
      2, 1, 0, 1, 3, 0;
      3, 0, 1, 1, 0, 0;
      2, 1, 1, 2, 3, 2;
      0, 1, 1, 3, 2, 4;
      4, 4, 4, 2, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 6, 9} =
      !![0, 0, 0, 0, 4, 4;
      4, 0, 2, 0, 3, 4;
      1, 4, 2, 4, 3, 4;
      4, 1, 4, 1, 0, 4;
      4, 0, 3, 3, 3, 3;
      0, 2, 2, 3, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_615 : Certificate {0, 1, 2, 5, 6, 9} := by
  refine ⟨!![2, 2, 1, 3, 3, 1;
      2, 2, 2, 4, 2, 1;
      3, 3, 3, 1, 2, 2;
      2, 0, 0, 2, 4, 2;
      4, 4, 1, 1, 0, 4;
      2, 4, 0, 1, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 6, 9} =
      !![0, 3, 2, 2, 3, 4;
      0, 2, 1, 0, 3, 3;
      4, 1, 4, 4, 3, 4;
      4, 4, 1, 4, 0, 4;
      4, 4, 0, 3, 3, 3;
      3, 0, 2, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_619 : Certificate {0, 1, 3, 5, 6, 9} := by
  refine ⟨!![0, 0, 4, 4, 0, 3;
      3, 4, 1, 4, 4, 3;
      4, 2, 3, 2, 0, 0;
      0, 3, 3, 3, 1, 4;
      4, 2, 0, 0, 4, 3;
      3, 1, 4, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 6, 9} =
      !![0, 0, 2, 0, 0, 1;
      0, 2, 2, 0, 3, 3;
      4, 1, 2, 4, 3, 4;
      4, 4, 4, 4, 0, 4;
      4, 4, 3, 3, 3, 3;
      3, 0, 2, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_621 : Certificate {0, 2, 3, 5, 6, 9} := by
  refine ⟨!![2, 0, 3, 2, 3, 3;
      3, 0, 1, 2, 2, 0;
      4, 0, 3, 1, 4, 1;
      2, 3, 2, 1, 4, 4;
      3, 0, 3, 0, 4, 4;
      0, 2, 3, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 6, 9} =
      !![0, 0, 3, 4, 2, 4;
      0, 1, 2, 0, 3, 3;
      4, 4, 2, 4, 3, 4;
      4, 1, 4, 4, 0, 4;
      4, 0, 3, 3, 3, 3;
      3, 2, 2, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_622 : Certificate {1, 2, 3, 5, 6, 9} := by
  refine ⟨!![1, 2, 4, 4, 3, 4;
      0, 0, 4, 4, 0, 3;
      3, 1, 4, 4, 2, 2;
      0, 3, 4, 4, 1, 1;
      3, 1, 3, 4, 1, 4;
      1, 4, 2, 1, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 6, 9} =
      !![0, 0, 0, 0, 4, 4;
      2, 1, 2, 0, 3, 3;
      1, 4, 2, 4, 3, 4;
      4, 1, 4, 4, 0, 4;
      4, 0, 3, 3, 3, 3;
      0, 2, 2, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_627 : Certificate {0, 1, 4, 5, 6, 9} := by
  refine ⟨!![1, 2, 3, 1, 3, 1;
      4, 3, 1, 3, 1, 0;
      1, 2, 4, 2, 3, 3;
      1, 4, 4, 4, 2, 0;
      3, 1, 4, 4, 3, 2;
      0, 3, 1, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 6, 9} =
      !![0, 0, 1, 0, 0, 1;
      0, 3, 2, 2, 3, 4;
      4, 1, 4, 4, 3, 4;
      4, 4, 1, 4, 0, 4;
      4, 4, 3, 3, 3, 3;
      3, 0, 3, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_629 : Certificate {0, 2, 4, 5, 6, 9} := by
  refine ⟨!![3, 0, 0, 1, 4, 2;
      1, 0, 2, 4, 0, 2;
      4, 0, 3, 1, 4, 1;
      4, 2, 3, 3, 3, 3;
      0, 0, 2, 3, 1, 2;
      3, 3, 2, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 6, 9} =
      !![0, 0, 2, 4, 2, 4;
      0, 2, 2, 2, 3, 4;
      4, 4, 4, 4, 3, 4;
      4, 1, 1, 4, 0, 4;
      4, 0, 3, 3, 3, 3;
      3, 2, 3, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_630 : Certificate {1, 2, 4, 5, 6, 9} := by
  refine ⟨!![3, 4, 2, 1, 2, 4;
      1, 3, 1, 4, 1, 1;
      1, 3, 2, 0, 1, 3;
      1, 0, 2, 2, 0, 0;
      1, 3, 1, 0, 0, 0;
      3, 2, 4, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 6, 9} =
      !![0, 0, 0, 0, 4, 4;
      3, 2, 2, 2, 3, 4;
      1, 4, 4, 4, 3, 4;
      4, 1, 1, 4, 0, 4;
      4, 0, 3, 3, 3, 3;
      0, 2, 3, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_633 : Certificate {0, 3, 4, 5, 6, 9} := by
  refine ⟨!![1, 0, 1, 3, 4, 3;
      3, 0, 1, 2, 0, 1;
      1, 0, 2, 4, 4, 0;
      4, 4, 4, 1, 4, 3;
      1, 0, 4, 2, 1, 4;
      3, 1, 1, 2, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 6, 9} =
      !![0, 3, 2, 4, 2, 4;
      0, 2, 1, 0, 0, 1;
      4, 2, 4, 4, 3, 4;
      4, 4, 1, 4, 0, 4;
      4, 3, 3, 3, 3, 3;
      3, 2, 3, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_634 : Certificate {1, 3, 4, 5, 6, 9} := by
  refine ⟨!![2, 2, 2, 4, 2, 0;
      1, 1, 4, 0, 4, 2;
      0, 0, 1, 1, 0, 2;
      4, 3, 4, 2, 2, 1;
      1, 1, 4, 1, 3, 1;
      3, 4, 1, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 6, 9} =
      !![0, 0, 0, 0, 4, 4;
      0, 2, 1, 0, 0, 1;
      1, 2, 4, 4, 3, 4;
      4, 4, 1, 4, 0, 4;
      4, 3, 3, 3, 3, 3;
      0, 2, 3, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_636 : Certificate {2, 3, 4, 5, 6, 9} := by
  refine ⟨!![0, 2, 2, 1, 3, 1;
      0, 2, 0, 4, 1, 3;
      0, 2, 3, 2, 3, 3;
      1, 1, 2, 4, 3, 4;
      0, 4, 2, 1, 3, 3;
      4, 1, 3, 4, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 6, 9} =
      !![0, 0, 0, 0, 4, 4;
      0, 3, 2, 4, 2, 4;
      4, 2, 4, 4, 3, 4;
      1, 4, 1, 4, 0, 4;
      0, 3, 3, 3, 3, 3;
      2, 2, 3, 1, 1, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_655 : Certificate {0, 1, 2, 3, 7, 9} := by
  refine ⟨!![1, 4, 3, 2, 2, 1;
      4, 0, 0, 3, 4, 4;
      4, 0, 4, 2, 4, 0;
      0, 2, 2, 4, 3, 3;
      1, 2, 0, 4, 1, 0;
      0, 1, 4, 1, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 7, 9} =
      !![0, 2, 1, 2, 4, 3;
      0, 4, 0, 2, 4, 4;
      4, 2, 0, 3, 3, 2;
      4, 4, 1, 4, 1, 4;
      4, 4, 0, 3, 0, 3;
      3, 0, 2, 2, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_663 : Certificate {0, 1, 2, 4, 7, 9} := by
  refine ⟨!![3, 1, 2, 4, 3, 0;
      2, 0, 3, 0, 1, 3;
      2, 4, 1, 2, 2, 0;
      0, 4, 4, 3, 1, 1;
      3, 1, 1, 0, 0, 2;
      0, 3, 1, 0, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 7, 9} =
      !![0, 3, 2, 2, 2, 4;
      0, 4, 0, 0, 4, 4;
      4, 2, 0, 3, 3, 2;
      4, 4, 1, 1, 1, 4;
      4, 4, 0, 3, 0, 3;
      3, 0, 2, 3, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_667 : Certificate {0, 1, 3, 4, 7, 9} := by
  refine ⟨!![4, 2, 1, 2, 3, 4;
      4, 3, 0, 4, 2, 2;
      2, 1, 4, 3, 4, 2;
      1, 2, 1, 2, 3, 2;
      2, 1, 1, 0, 1, 4;
      3, 2, 2, 2, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 7, 9} =
      !![0, 0, 2, 1, 4, 1;
      0, 4, 2, 0, 4, 4;
      4, 2, 3, 3, 3, 2;
      4, 4, 4, 1, 1, 4;
      4, 4, 3, 3, 0, 3;
      3, 0, 2, 3, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_669 : Certificate {0, 2, 3, 4, 7, 9} := by
  refine ⟨!![3, 3, 2, 1, 2, 2;
      1, 3, 2, 1, 2, 0;
      2, 3, 3, 3, 2, 1;
      1, 3, 3, 2, 2, 4;
      1, 0, 3, 4, 2, 3;
      3, 0, 3, 2, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 7, 9} =
      !![0, 0, 3, 2, 1, 4;
      0, 0, 2, 0, 4, 4;
      4, 0, 3, 3, 3, 2;
      4, 1, 4, 1, 1, 4;
      4, 0, 3, 3, 0, 3;
      3, 2, 2, 3, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_670 : Certificate {1, 2, 3, 4, 7, 9} := by
  refine ⟨!![2, 2, 0, 1, 1, 2;
      1, 3, 3, 2, 1, 2;
      3, 4, 0, 3, 3, 1;
      4, 1, 4, 2, 0, 4;
      2, 1, 4, 3, 4, 1;
      2, 4, 1, 2, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 7, 9} =
      !![0, 0, 0, 0, 4, 4;
      4, 0, 2, 0, 4, 4;
      2, 0, 3, 3, 3, 2;
      4, 1, 4, 1, 1, 4;
      4, 0, 3, 3, 0, 3;
      0, 2, 2, 3, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_679 : Certificate {0, 1, 2, 5, 7, 9} := by
  refine ⟨!![3, 0, 1, 2, 4, 1;
      4, 1, 1, 2, 3, 2;
      1, 2, 3, 3, 0, 2;
      2, 1, 3, 2, 2, 4;
      0, 1, 3, 0, 3, 2;
      2, 1, 1, 1, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 7, 9} =
      !![0, 3, 2, 2, 2, 4;
      0, 2, 1, 0, 4, 3;
      4, 2, 0, 3, 3, 2;
      4, 4, 1, 4, 1, 4;
      4, 4, 0, 3, 0, 3;
      3, 0, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_683 : Certificate {0, 1, 3, 5, 7, 9} := by
  refine ⟨!![3, 1, 1, 3, 1, 2;
      0, 3, 4, 0, 3, 4;
      4, 1, 2, 0, 1, 1;
      0, 2, 2, 1, 2, 0;
      4, 2, 0, 0, 4, 3;
      2, 0, 1, 0, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 7, 9} =
      !![0, 0, 2, 0, 4, 1;
      0, 2, 2, 0, 4, 3;
      4, 2, 3, 3, 3, 2;
      4, 4, 4, 4, 1, 4;
      4, 4, 3, 3, 0, 3;
      3, 0, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_685 : Certificate {0, 2, 3, 5, 7, 9} := by
  refine ⟨!![2, 3, 4, 0, 3, 1;
      0, 3, 4, 0, 3, 4;
      1, 0, 0, 1, 0, 2;
      0, 3, 0, 1, 3, 3;
      1, 1, 3, 1, 3, 4;
      3, 3, 3, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 7, 9} =
      !![0, 0, 3, 4, 1, 4;
      0, 1, 2, 0, 4, 3;
      4, 0, 3, 3, 3, 2;
      4, 1, 4, 4, 1, 4;
      4, 0, 3, 3, 0, 3;
      3, 2, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_686 : Certificate {1, 2, 3, 5, 7, 9} := by
  refine ⟨!![1, 3, 3, 4, 2, 4;
      4, 0, 1, 1, 1, 0;
      4, 3, 0, 2, 4, 0;
      3, 2, 4, 3, 4, 0;
      4, 4, 3, 2, 2, 2;
      0, 1, 2, 3, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 7, 9} =
      !![0, 0, 0, 0, 4, 4;
      2, 1, 2, 0, 4, 3;
      2, 0, 3, 3, 3, 2;
      4, 1, 4, 4, 1, 4;
      4, 0, 3, 3, 0, 3;
      0, 2, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_691 : Certificate {0, 1, 4, 5, 7, 9} := by
  refine ⟨!![1, 1, 3, 1, 3, 1;
      3, 0, 3, 0, 0, 1;
      4, 2, 3, 1, 1, 0;
      3, 3, 0, 0, 4, 3;
      4, 4, 2, 2, 4, 1;
      1, 2, 4, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 7, 9} =
      !![0, 0, 1, 0, 4, 1;
      0, 3, 2, 2, 2, 4;
      4, 2, 3, 3, 3, 2;
      4, 4, 1, 4, 1, 4;
      4, 4, 3, 3, 0, 3;
      3, 0, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_693 : Certificate {0, 2, 4, 5, 7, 9} := by
  refine ⟨!![1, 3, 1, 3, 4, 3;
      4, 3, 1, 3, 4, 1;
      4, 0, 0, 4, 0, 3;
      0, 3, 2, 0, 4, 2;
      1, 1, 2, 4, 0, 2;
      3, 3, 0, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 7, 9} =
      !![0, 0, 2, 4, 1, 4;
      0, 2, 2, 2, 2, 4;
      4, 0, 3, 3, 3, 2;
      4, 1, 1, 4, 1, 4;
      4, 0, 3, 3, 0, 3;
      3, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_694 : Certificate {1, 2, 4, 5, 7, 9} := by
  refine ⟨!![2, 4, 1, 3, 0, 2;
      4, 4, 4, 2, 3, 3;
      0, 3, 1, 2, 4, 1;
      2, 2, 3, 3, 4, 4;
      2, 2, 2, 4, 1, 1;
      2, 3, 3, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 7, 9} =
      !![0, 0, 0, 0, 4, 4;
      3, 2, 2, 2, 2, 4;
      2, 0, 3, 3, 3, 2;
      4, 1, 1, 4, 1, 4;
      4, 0, 3, 3, 0, 3;
      0, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_697 : Certificate {0, 3, 4, 5, 7, 9} := by
  refine ⟨!![2, 0, 0, 0, 0, 2;
      0, 4, 4, 0, 0, 3;
      4, 4, 4, 4, 0, 1;
      1, 1, 2, 2, 0, 3;
      3, 2, 2, 3, 2, 4;
      4, 1, 0, 4, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 7, 9} =
      !![0, 3, 2, 4, 1, 4;
      0, 2, 1, 0, 4, 1;
      4, 3, 3, 3, 3, 2;
      4, 4, 1, 4, 1, 4;
      4, 3, 3, 3, 0, 3;
      3, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_698 : Certificate {1, 3, 4, 5, 7, 9} := by
  refine ⟨!![2, 1, 4, 4, 3, 3;
      4, 1, 2, 3, 1, 4;
      2, 0, 3, 3, 3, 0;
      1, 4, 4, 4, 4, 1;
      2, 3, 1, 2, 0, 4;
      2, 2, 4, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 7, 9} =
      !![0, 0, 0, 0, 4, 4;
      0, 2, 1, 0, 4, 1;
      2, 3, 3, 3, 3, 2;
      4, 4, 1, 4, 1, 4;
      4, 3, 3, 3, 0, 3;
      0, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_700 : Certificate {2, 3, 4, 5, 7, 9} := by
  refine ⟨!![0, 3, 0, 0, 0, 3;
      2, 2, 3, 4, 3, 3;
      2, 1, 3, 3, 3, 1;
      3, 2, 3, 3, 2, 1;
      1, 0, 4, 0, 1, 0;
      3, 0, 1, 0, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 7, 9} =
      !![0, 0, 0, 0, 4, 4;
      0, 3, 2, 4, 1, 4;
      0, 3, 3, 3, 3, 2;
      1, 4, 1, 4, 1, 4;
      0, 3, 3, 3, 0, 3;
      2, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_711 : Certificate {0, 1, 2, 6, 7, 9} := by
  refine ⟨!![0, 1, 1, 1, 0, 4;
      2, 0, 2, 4, 4, 1;
      2, 0, 3, 0, 3, 1;
      1, 3, 1, 3, 0, 1;
      3, 0, 0, 3, 1, 3;
      3, 4, 0, 2, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 6, 7, 9} =
      !![0, 3, 2, 3, 2, 4;
      0, 2, 1, 3, 4, 3;
      0, 4, 0, 3, 4, 4;
      4, 4, 1, 0, 1, 4;
      4, 4, 0, 3, 0, 3;
      3, 0, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_715 : Certificate {0, 1, 3, 6, 7, 9} := by
  refine ⟨!![1, 2, 1, 2, 1, 3;
      2, 2, 4, 1, 3, 3;
      4, 4, 0, 4, 4, 1;
      1, 4, 2, 4, 2, 2;
      3, 3, 3, 1, 2, 1;
      1, 0, 3, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 6, 7, 9} =
      !![0, 0, 2, 0, 4, 1;
      0, 2, 2, 3, 4, 3;
      0, 4, 2, 3, 4, 4;
      4, 4, 4, 0, 1, 4;
      4, 4, 3, 3, 0, 3;
      3, 0, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_717 : Certificate {0, 2, 3, 6, 7, 9} := by
  refine ⟨!![4, 3, 1, 4, 2, 4;
      2, 1, 1, 0, 0, 0;
      1, 3, 0, 2, 3, 0;
      0, 3, 0, 1, 3, 3;
      0, 0, 2, 2, 0, 4;
      2, 0, 2, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 6, 7, 9} =
      !![0, 0, 3, 2, 1, 4;
      0, 1, 2, 3, 4, 3;
      0, 0, 2, 3, 4, 4;
      4, 1, 4, 0, 1, 4;
      4, 0, 3, 3, 0, 3;
      3, 2, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_718 : Certificate {1, 2, 3, 6, 7, 9} := by
  refine ⟨!![4, 1, 4, 4, 3, 0;
      4, 3, 2, 2, 2, 3;
      0, 1, 1, 1, 0, 4;
      2, 1, 2, 3, 2, 3;
      1, 4, 3, 3, 2, 4;
      1, 0, 0, 4, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 6, 7, 9} =
      !![0, 0, 0, 4, 4, 4;
      2, 1, 2, 3, 4, 3;
      4, 0, 2, 3, 4, 4;
      4, 1, 4, 0, 1, 4;
      4, 0, 3, 3, 0, 3;
      0, 2, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_723 : Certificate {0, 1, 4, 6, 7, 9} := by
  refine ⟨!![4, 3, 3, 0, 1, 4;
      0, 1, 3, 4, 0, 3;
      0, 2, 3, 0, 3, 1;
      2, 2, 0, 0, 1, 2;
      0, 1, 2, 3, 3, 2;
      1, 4, 4, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 6, 7, 9} =
      !![0, 0, 1, 0, 4, 1;
      0, 3, 2, 3, 2, 4;
      0, 4, 0, 3, 4, 4;
      4, 4, 1, 0, 1, 4;
      4, 4, 3, 3, 0, 3;
      3, 0, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_725 : Certificate {0, 2, 4, 6, 7, 9} := by
  refine ⟨!![3, 2, 3, 1, 3, 0;
      0, 3, 4, 2, 0, 4;
      0, 4, 4, 3, 3, 2;
      4, 1, 1, 1, 2, 1;
      0, 4, 1, 0, 3, 1;
      2, 4, 1, 3, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 6, 7, 9} =
      !![0, 0, 2, 2, 1, 4;
      0, 2, 2, 3, 2, 4;
      0, 0, 0, 3, 4, 4;
      4, 1, 1, 0, 1, 4;
      4, 0, 3, 3, 0, 3;
      3, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_726 : Certificate {1, 2, 4, 6, 7, 9} := by
  refine ⟨!![4, 0, 3, 3, 3, 1;
      3, 3, 0, 3, 1, 1;
      2, 4, 3, 2, 2, 0;
      2, 0, 1, 2, 2, 4;
      3, 4, 2, 1, 4, 3;
      4, 1, 2, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 6, 7, 9} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 2, 4;
      4, 0, 0, 3, 4, 4;
      4, 1, 1, 0, 1, 4;
      4, 0, 3, 3, 0, 3;
      0, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_729 : Certificate {0, 3, 4, 6, 7, 9} := by
  refine ⟨!![2, 3, 1, 3, 4, 1;
      3, 1, 3, 0, 2, 4;
      2, 4, 4, 2, 1, 1;
      0, 2, 4, 2, 1, 1;
      2, 4, 1, 4, 1, 0;
      4, 4, 1, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 6, 7, 9} =
      !![0, 3, 2, 2, 1, 4;
      0, 2, 1, 0, 4, 1;
      0, 2, 0, 3, 4, 4;
      4, 4, 1, 0, 1, 4;
      4, 3, 3, 3, 0, 3;
      3, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_730 : Certificate {1, 3, 4, 6, 7, 9} := by
  refine ⟨!![3, 3, 4, 2, 3, 2;
      4, 3, 1, 4, 0, 1;
      2, 3, 4, 2, 4, 3;
      1, 3, 2, 1, 2, 0;
      4, 0, 2, 2, 1, 0;
      4, 2, 1, 2, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 6, 7, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 1, 0, 4, 1;
      4, 2, 0, 3, 4, 4;
      4, 4, 1, 0, 1, 4;
      4, 3, 3, 3, 0, 3;
      0, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_732 : Certificate {2, 3, 4, 6, 7, 9} := by
  refine ⟨!![3, 3, 3, 4, 4, 1;
      1, 0, 2, 2, 2, 4;
      3, 4, 4, 2, 3, 4;
      3, 0, 3, 4, 4, 3;
      3, 4, 1, 4, 3, 3;
      3, 1, 1, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 6, 7, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 2, 2, 1, 4;
      0, 2, 0, 3, 4, 4;
      1, 4, 1, 0, 1, 4;
      0, 3, 3, 3, 0, 3;
      2, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_739 : Certificate {0, 1, 5, 6, 7, 9} := by
  refine ⟨!![0, 1, 1, 1, 4, 2;
      3, 4, 3, 2, 0, 4;
      1, 0, 1, 1, 1, 4;
      3, 2, 1, 1, 2, 1;
      1, 3, 1, 4, 2, 2;
      2, 3, 1, 4, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 6, 7, 9} =
      !![0, 0, 0, 0, 4, 1;
      0, 3, 2, 3, 2, 4;
      0, 2, 0, 3, 4, 3;
      4, 4, 4, 0, 1, 4;
      4, 4, 3, 3, 0, 3;
      3, 0, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_741 : Certificate {0, 2, 5, 6, 7, 9} := by
  refine ⟨!![1, 4, 4, 1, 1, 1;
      3, 4, 4, 0, 1, 2;
      1, 0, 3, 2, 3, 0;
      4, 0, 0, 4, 0, 3;
      1, 3, 3, 0, 4, 3;
      2, 3, 0, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 6, 7, 9} =
      !![0, 0, 4, 2, 1, 4;
      0, 2, 2, 3, 2, 4;
      0, 1, 0, 3, 4, 3;
      4, 1, 4, 0, 1, 4;
      4, 0, 3, 3, 0, 3;
      3, 2, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_742 : Certificate {1, 2, 5, 6, 7, 9} := by
  refine ⟨!![2, 1, 0, 1, 1, 1;
      0, 2, 2, 2, 3, 4;
      4, 3, 4, 3, 4, 1;
      2, 0, 4, 1, 2, 0;
      4, 1, 4, 1, 0, 4;
      3, 4, 2, 3, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 6, 7, 9} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 2, 4;
      2, 1, 0, 3, 4, 3;
      4, 1, 4, 0, 1, 4;
      4, 0, 3, 3, 0, 3;
      0, 2, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_745 : Certificate {0, 3, 5, 6, 7, 9} := by
  refine ⟨!![0, 3, 4, 3, 4, 1;
      3, 2, 1, 3, 1, 3;
      3, 3, 2, 4, 2, 2;
      2, 2, 1, 2, 1, 1;
      3, 2, 1, 3, 3, 2;
      2, 4, 4, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 6, 7, 9} =
      !![0, 3, 4, 2, 1, 4;
      0, 2, 0, 0, 4, 1;
      0, 2, 0, 3, 4, 3;
      4, 4, 4, 0, 1, 4;
      4, 3, 3, 3, 0, 3;
      3, 2, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_746 : Certificate {1, 3, 5, 6, 7, 9} := by
  refine ⟨!![0, 3, 4, 3, 4, 1;
      1, 1, 0, 1, 4, 4;
      1, 2, 1, 2, 0, 3;
      4, 2, 4, 3, 0, 3;
      1, 2, 3, 2, 4, 0;
      4, 1, 3, 0, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 6, 7, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 0, 0, 4, 1;
      2, 2, 0, 3, 4, 3;
      4, 4, 4, 0, 1, 4;
      4, 3, 3, 3, 0, 3;
      0, 2, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_748 : Certificate {2, 3, 5, 6, 7, 9} := by
  refine ⟨!![3, 1, 1, 2, 3, 4;
      3, 4, 1, 3, 3, 3;
      2, 2, 2, 4, 0, 2;
      3, 3, 1, 2, 3, 1;
      4, 1, 3, 2, 1, 0;
      2, 1, 1, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 6, 7, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 4, 2, 1, 4;
      1, 2, 0, 3, 4, 3;
      1, 4, 4, 0, 1, 4;
      0, 3, 3, 3, 0, 3;
      2, 2, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_753 : Certificate {0, 4, 5, 6, 7, 9} := by
  refine ⟨!![4, 2, 4, 4, 2, 4;
      1, 2, 4, 3, 2, 0;
      3, 1, 4, 1, 2, 1;
      3, 3, 1, 1, 3, 3;
      2, 4, 3, 1, 1, 4;
      1, 3, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 6, 7, 9} =
      !![0, 2, 4, 2, 1, 4;
      0, 1, 0, 0, 4, 1;
      0, 2, 2, 3, 2, 4;
      4, 1, 4, 0, 1, 4;
      4, 3, 3, 3, 0, 3;
      3, 3, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_754 : Certificate {1, 4, 5, 6, 7, 9} := by
  refine ⟨!![3, 1, 1, 2, 0, 0;
      1, 1, 0, 1, 4, 4;
      4, 0, 4, 4, 3, 3;
      4, 2, 1, 4, 4, 0;
      3, 4, 2, 1, 0, 2;
      2, 4, 2, 0, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 6, 7, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 1, 0, 0, 4, 1;
      3, 2, 2, 3, 2, 4;
      4, 1, 4, 0, 1, 4;
      4, 3, 3, 3, 0, 3;
      0, 3, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_756 : Certificate {2, 4, 5, 6, 7, 9} := by
  refine ⟨!![2, 2, 1, 0, 1, 2;
      3, 0, 4, 4, 4, 4;
      3, 4, 1, 4, 0, 2;
      2, 4, 1, 0, 1, 4;
      0, 4, 0, 3, 2, 1;
      2, 2, 4, 2, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 6, 7, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 4, 2, 1, 4;
      2, 2, 2, 3, 2, 4;
      1, 1, 4, 0, 1, 4;
      0, 3, 3, 3, 0, 3;
      2, 3, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_760 : Certificate {3, 4, 5, 6, 7, 9} := by
  refine ⟨!![3, 4, 3, 1, 2, 4;
      3, 1, 3, 0, 2, 0;
      4, 1, 3, 0, 1, 4;
      0, 2, 0, 0, 0, 2;
      4, 1, 4, 1, 3, 3;
      0, 2, 1, 4, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 6, 7, 9} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 4, 2, 1, 4;
      2, 1, 0, 0, 4, 1;
      4, 1, 4, 0, 1, 4;
      3, 3, 3, 3, 0, 3;
      2, 3, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 685 then
    if mask < 622 then
      if mask < 599 then
        if mask < 571 then
          if mask < 559 then
            ⟨{0, 1, 2, 3, 4, 9}, certificate_543⟩
          else
            if mask < 567 then
              ⟨{0, 1, 2, 3, 5, 9}, certificate_559⟩
            else
              ⟨{0, 1, 2, 4, 5, 9}, certificate_567⟩
        else
          if mask < 574 then
            if mask < 573 then
              ⟨{0, 1, 3, 4, 5, 9}, certificate_571⟩
            else
              ⟨{0, 2, 3, 4, 5, 9}, certificate_573⟩
          else
            if mask < 591 then
              ⟨{1, 2, 3, 4, 5, 9}, certificate_574⟩
            else
              ⟨{0, 1, 2, 3, 6, 9}, certificate_591⟩
      else
        if mask < 606 then
          if mask < 603 then
            ⟨{0, 1, 2, 4, 6, 9}, certificate_599⟩
          else
            if mask < 605 then
              ⟨{0, 1, 3, 4, 6, 9}, certificate_603⟩
            else
              ⟨{0, 2, 3, 4, 6, 9}, certificate_605⟩
        else
          if mask < 619 then
            if mask < 615 then
              ⟨{1, 2, 3, 4, 6, 9}, certificate_606⟩
            else
              ⟨{0, 1, 2, 5, 6, 9}, certificate_615⟩
          else
            if mask < 621 then
              ⟨{0, 1, 3, 5, 6, 9}, certificate_619⟩
            else
              ⟨{0, 2, 3, 5, 6, 9}, certificate_621⟩
    else
      if mask < 655 then
        if mask < 630 then
          if mask < 627 then
            ⟨{1, 2, 3, 5, 6, 9}, certificate_622⟩
          else
            if mask < 629 then
              ⟨{0, 1, 4, 5, 6, 9}, certificate_627⟩
            else
              ⟨{0, 2, 4, 5, 6, 9}, certificate_629⟩
        else
          if mask < 634 then
            if mask < 633 then
              ⟨{1, 2, 4, 5, 6, 9}, certificate_630⟩
            else
              ⟨{0, 3, 4, 5, 6, 9}, certificate_633⟩
          else
            if mask < 636 then
              ⟨{1, 3, 4, 5, 6, 9}, certificate_634⟩
            else
              ⟨{2, 3, 4, 5, 6, 9}, certificate_636⟩
      else
        if mask < 669 then
          if mask < 663 then
            ⟨{0, 1, 2, 3, 7, 9}, certificate_655⟩
          else
            if mask < 667 then
              ⟨{0, 1, 2, 4, 7, 9}, certificate_663⟩
            else
              ⟨{0, 1, 3, 4, 7, 9}, certificate_667⟩
        else
          if mask < 679 then
            if mask < 670 then
              ⟨{0, 2, 3, 4, 7, 9}, certificate_669⟩
            else
              ⟨{1, 2, 3, 4, 7, 9}, certificate_670⟩
          else
            if mask < 683 then
              ⟨{0, 1, 2, 5, 7, 9}, certificate_679⟩
            else
              ⟨{0, 1, 3, 5, 7, 9}, certificate_683⟩
  else
    if mask < 726 then
      if mask < 700 then
        if mask < 693 then
          if mask < 686 then
            ⟨{0, 2, 3, 5, 7, 9}, certificate_685⟩
          else
            if mask < 691 then
              ⟨{1, 2, 3, 5, 7, 9}, certificate_686⟩
            else
              ⟨{0, 1, 4, 5, 7, 9}, certificate_691⟩
        else
          if mask < 697 then
            if mask < 694 then
              ⟨{0, 2, 4, 5, 7, 9}, certificate_693⟩
            else
              ⟨{1, 2, 4, 5, 7, 9}, certificate_694⟩
          else
            if mask < 698 then
              ⟨{0, 3, 4, 5, 7, 9}, certificate_697⟩
            else
              ⟨{1, 3, 4, 5, 7, 9}, certificate_698⟩
      else
        if mask < 717 then
          if mask < 711 then
            ⟨{2, 3, 4, 5, 7, 9}, certificate_700⟩
          else
            if mask < 715 then
              ⟨{0, 1, 2, 6, 7, 9}, certificate_711⟩
            else
              ⟨{0, 1, 3, 6, 7, 9}, certificate_715⟩
        else
          if mask < 723 then
            if mask < 718 then
              ⟨{0, 2, 3, 6, 7, 9}, certificate_717⟩
            else
              ⟨{1, 2, 3, 6, 7, 9}, certificate_718⟩
          else
            if mask < 725 then
              ⟨{0, 1, 4, 6, 7, 9}, certificate_723⟩
            else
              ⟨{0, 2, 4, 6, 7, 9}, certificate_725⟩
    else
      if mask < 745 then
        if mask < 732 then
          if mask < 729 then
            ⟨{1, 2, 4, 6, 7, 9}, certificate_726⟩
          else
            if mask < 730 then
              ⟨{0, 3, 4, 6, 7, 9}, certificate_729⟩
            else
              ⟨{1, 3, 4, 6, 7, 9}, certificate_730⟩
        else
          if mask < 741 then
            if mask < 739 then
              ⟨{2, 3, 4, 6, 7, 9}, certificate_732⟩
            else
              ⟨{0, 1, 5, 6, 7, 9}, certificate_739⟩
          else
            if mask < 742 then
              ⟨{0, 2, 5, 6, 7, 9}, certificate_741⟩
            else
              ⟨{1, 2, 5, 6, 7, 9}, certificate_742⟩
      else
        if mask < 753 then
          if mask < 746 then
            ⟨{0, 3, 5, 6, 7, 9}, certificate_745⟩
          else
            if mask < 748 then
              ⟨{1, 3, 5, 6, 7, 9}, certificate_746⟩
            else
              ⟨{2, 3, 5, 6, 7, 9}, certificate_748⟩
        else
          if mask < 756 then
            if mask < 754 then
              ⟨{0, 4, 5, 6, 7, 9}, certificate_753⟩
            else
              ⟨{1, 4, 5, 6, 7, 9}, certificate_754⟩
          else
            if mask < 760 then
              ⟨{2, 4, 5, 6, 7, 9}, certificate_756⟩
            else
              ⟨{3, 4, 5, 6, 7, 9}, certificate_760⟩
end AMEProbe.QuinaryDirect.Batch02
#print axioms AMEProbe.QuinaryDirect.Batch02.lookup
