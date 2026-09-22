import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch06
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_1551 : Certificate {0, 1, 2, 3, 9, 10} := by
  refine ⟨!![0, 3, 1, 4, 3, 3;
      3, 1, 4, 2, 4, 0;
      3, 1, 3, 2, 3, 1;
      3, 4, 0, 4, 1, 0;
      1, 0, 0, 3, 0, 1;
      1, 3, 3, 4, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 9, 10} =
      !![0, 2, 1, 2, 3, 3;
      0, 4, 0, 2, 4, 3;
      4, 2, 0, 3, 2, 3;
      4, 1, 4, 2, 4, 0;
      4, 4, 1, 4, 4, 4;
      3, 0, 2, 2, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1559 : Certificate {0, 1, 2, 4, 9, 10} := by
  refine ⟨!![2, 2, 2, 3, 1, 4;
      4, 0, 1, 1, 4, 2;
      2, 1, 4, 2, 0, 2;
      3, 1, 4, 1, 2, 4;
      2, 1, 1, 4, 1, 2;
      2, 4, 4, 0, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 9, 10} =
      !![0, 3, 2, 2, 4, 3;
      0, 4, 0, 0, 4, 3;
      4, 2, 0, 3, 2, 3;
      4, 1, 4, 4, 4, 0;
      4, 4, 1, 1, 4, 4;
      3, 0, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1563 : Certificate {0, 1, 3, 4, 9, 10} := by
  refine ⟨!![1, 4, 3, 1, 3, 1;
      1, 1, 3, 2, 1, 2;
      4, 2, 0, 0, 3, 1;
      4, 4, 3, 3, 0, 2;
      4, 2, 2, 2, 4, 1;
      4, 0, 0, 3, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 9, 10} =
      !![0, 0, 2, 1, 1, 0;
      0, 4, 2, 0, 4, 3;
      4, 2, 3, 3, 2, 3;
      4, 1, 2, 4, 4, 0;
      4, 4, 4, 1, 4, 4;
      3, 0, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1565 : Certificate {0, 2, 3, 4, 9, 10} := by
  refine ⟨!![2, 3, 4, 0, 2, 4;
      3, 0, 1, 4, 0, 0;
      1, 3, 0, 0, 4, 3;
      3, 0, 2, 4, 1, 4;
      4, 3, 3, 1, 0, 3;
      4, 1, 1, 2, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 9, 10} =
      !![0, 0, 3, 2, 4, 4;
      0, 0, 2, 0, 4, 3;
      4, 0, 3, 3, 2, 3;
      4, 4, 2, 4, 4, 0;
      4, 1, 4, 1, 4, 4;
      3, 2, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1566 : Certificate {1, 2, 3, 4, 9, 10} := by
  refine ⟨!![1, 2, 3, 3, 1, 1;
      1, 0, 3, 2, 3, 0;
      1, 1, 1, 3, 4, 2;
      0, 3, 1, 4, 3, 3;
      2, 1, 1, 2, 3, 2;
      2, 4, 4, 3, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 9, 10} =
      !![0, 0, 0, 0, 4, 4;
      4, 0, 2, 0, 4, 3;
      2, 0, 3, 3, 2, 3;
      1, 4, 2, 4, 4, 0;
      4, 1, 4, 1, 4, 4;
      0, 2, 2, 3, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1575 : Certificate {0, 1, 2, 5, 9, 10} := by
  refine ⟨!![2, 1, 2, 1, 3, 4;
      3, 4, 3, 1, 3, 4;
      0, 1, 3, 1, 4, 1;
      2, 2, 1, 0, 2, 1;
      4, 0, 2, 3, 4, 3;
      4, 4, 0, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 9, 10} =
      !![0, 3, 2, 2, 4, 3;
      0, 2, 1, 0, 3, 3;
      4, 2, 0, 3, 2, 3;
      4, 1, 4, 4, 4, 0;
      4, 4, 1, 4, 4, 4;
      3, 0, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1579 : Certificate {0, 1, 3, 5, 9, 10} := by
  refine ⟨!![3, 2, 4, 3, 0, 1;
      2, 4, 4, 0, 0, 3;
      0, 1, 3, 1, 4, 1;
      3, 1, 2, 0, 1, 1;
      1, 3, 4, 3, 2, 3;
      1, 4, 3, 3, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 9, 10} =
      !![0, 0, 2, 0, 1, 0;
      0, 2, 2, 0, 3, 3;
      4, 2, 3, 3, 2, 3;
      4, 1, 2, 4, 4, 0;
      4, 4, 4, 4, 4, 4;
      3, 0, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1581 : Certificate {0, 2, 3, 5, 9, 10} := by
  refine ⟨!![1, 1, 3, 1, 3, 1;
      4, 0, 0, 2, 2, 3;
      1, 1, 3, 4, 2, 3;
      4, 0, 1, 2, 3, 2;
      3, 1, 2, 2, 1, 0;
      0, 2, 1, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 9, 10} =
      !![0, 0, 3, 4, 4, 4;
      0, 1, 2, 0, 3, 3;
      4, 0, 3, 3, 2, 3;
      4, 4, 2, 4, 4, 0;
      4, 1, 4, 4, 4, 4;
      3, 2, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1582 : Certificate {1, 2, 3, 5, 9, 10} := by
  refine ⟨!![1, 0, 4, 2, 4, 4;
      4, 1, 4, 1, 1, 0;
      1, 0, 4, 0, 3, 1;
      3, 1, 1, 4, 3, 0;
      1, 3, 2, 1, 1, 1;
      3, 2, 3, 4, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 9, 10} =
      !![0, 0, 0, 0, 4, 4;
      2, 1, 2, 0, 3, 3;
      2, 0, 3, 3, 2, 3;
      1, 4, 2, 4, 4, 0;
      4, 1, 4, 4, 4, 4;
      0, 2, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1587 : Certificate {0, 1, 4, 5, 9, 10} := by
  refine ⟨!![3, 0, 3, 1, 2, 4;
      3, 1, 0, 3, 0, 1;
      3, 3, 4, 1, 3, 1;
      4, 1, 2, 1, 3, 2;
      3, 2, 1, 4, 2, 4;
      0, 4, 3, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 9, 10} =
      !![0, 0, 1, 0, 1, 0;
      0, 3, 2, 2, 4, 3;
      4, 2, 3, 3, 2, 3;
      4, 1, 4, 4, 4, 0;
      4, 4, 1, 4, 4, 4;
      3, 0, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1589 : Certificate {0, 2, 4, 5, 9, 10} := by
  refine ⟨!![1, 3, 1, 2, 1, 0;
      3, 2, 4, 2, 2, 1;
      3, 4, 3, 0, 0, 1;
      0, 3, 2, 2, 3, 4;
      3, 3, 0, 3, 4, 4;
      2, 2, 4, 0, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 9, 10} =
      !![0, 0, 2, 4, 4, 4;
      0, 2, 2, 2, 4, 3;
      4, 0, 3, 3, 2, 3;
      4, 4, 4, 4, 4, 0;
      4, 1, 1, 4, 4, 4;
      3, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1590 : Certificate {1, 2, 4, 5, 9, 10} := by
  refine ⟨!![4, 0, 1, 2, 3, 2;
      3, 3, 3, 0, 0, 0;
      2, 0, 3, 0, 1, 2;
      2, 3, 0, 3, 2, 0;
      2, 4, 0, 3, 0, 0;
      2, 1, 0, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 9, 10} =
      !![0, 0, 0, 0, 4, 4;
      3, 2, 2, 2, 4, 3;
      2, 0, 3, 3, 2, 3;
      1, 4, 4, 4, 4, 0;
      4, 1, 1, 4, 4, 4;
      0, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1593 : Certificate {0, 3, 4, 5, 9, 10} := by
  refine ⟨!![3, 2, 2, 2, 4, 3;
      4, 2, 2, 3, 1, 2;
      2, 0, 0, 1, 1, 4;
      3, 0, 1, 4, 0, 0;
      0, 2, 1, 3, 2, 2;
      2, 4, 4, 4, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 9, 10} =
      !![0, 3, 2, 4, 4, 4;
      0, 2, 1, 0, 1, 0;
      4, 3, 3, 3, 2, 3;
      4, 2, 4, 4, 4, 0;
      4, 4, 1, 4, 4, 4;
      3, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1594 : Certificate {1, 3, 4, 5, 9, 10} := by
  refine ⟨!![4, 2, 3, 1, 1, 3;
      0, 1, 1, 2, 4, 3;
      2, 3, 1, 1, 3, 1;
      4, 0, 2, 3, 2, 0;
      3, 1, 2, 0, 4, 3;
      1, 4, 3, 0, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 9, 10} =
      !![0, 0, 0, 0, 4, 4;
      0, 2, 1, 0, 1, 0;
      2, 3, 3, 3, 2, 3;
      1, 2, 4, 4, 4, 0;
      4, 4, 1, 4, 4, 4;
      0, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1596 : Certificate {2, 3, 4, 5, 9, 10} := by
  refine ⟨!![3, 4, 2, 3, 4, 0;
      3, 0, 2, 4, 1, 4;
      1, 0, 4, 2, 4, 4;
      2, 4, 4, 1, 1, 0;
      0, 2, 4, 1, 3, 4;
      4, 3, 1, 4, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 9, 10} =
      !![0, 0, 0, 0, 4, 4;
      0, 3, 2, 4, 4, 4;
      0, 3, 3, 3, 2, 3;
      4, 2, 4, 4, 4, 0;
      1, 4, 1, 4, 4, 4;
      2, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1607 : Certificate {0, 1, 2, 6, 9, 10} := by
  refine ⟨!![3, 2, 0, 1, 4, 2;
      2, 4, 3, 4, 4, 1;
      4, 2, 1, 2, 2, 3;
      0, 1, 3, 3, 2, 0;
      0, 3, 1, 4, 4, 1;
      4, 3, 2, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 6, 9, 10} =
      !![0, 3, 2, 3, 4, 3;
      0, 2, 1, 3, 3, 3;
      0, 4, 0, 3, 4, 3;
      4, 1, 4, 3, 4, 0;
      4, 4, 1, 0, 4, 4;
      3, 0, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1611 : Certificate {0, 1, 3, 6, 9, 10} := by
  refine ⟨!![4, 1, 4, 1, 4, 2;
      4, 1, 1, 2, 2, 3;
      2, 4, 3, 2, 2, 3;
      1, 3, 2, 4, 3, 4;
      2, 2, 4, 1, 1, 4;
      3, 2, 3, 4, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 6, 9, 10} =
      !![0, 0, 2, 0, 1, 0;
      0, 2, 2, 3, 3, 3;
      0, 4, 2, 3, 4, 3;
      4, 1, 2, 3, 4, 0;
      4, 4, 4, 0, 4, 4;
      3, 0, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1613 : Certificate {0, 2, 3, 6, 9, 10} := by
  refine ⟨!![3, 4, 1, 4, 1, 2;
      2, 1, 2, 0, 1, 2;
      2, 2, 2, 1, 2, 1;
      1, 2, 4, 1, 3, 3;
      2, 0, 3, 0, 1, 2;
      0, 0, 1, 0, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 6, 9, 10} =
      !![0, 0, 3, 2, 4, 4;
      0, 1, 2, 3, 3, 3;
      0, 0, 2, 3, 4, 3;
      4, 4, 2, 3, 4, 0;
      4, 1, 4, 0, 4, 4;
      3, 2, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1614 : Certificate {1, 2, 3, 6, 9, 10} := by
  refine ⟨!![3, 4, 1, 1, 2, 0;
      3, 4, 4, 0, 4, 4;
      2, 2, 2, 4, 1, 3;
      1, 2, 4, 0, 0, 4;
      2, 0, 3, 3, 0, 4;
      1, 3, 3, 2, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 6, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      2, 1, 2, 3, 3, 3;
      4, 0, 2, 3, 4, 3;
      1, 4, 2, 3, 4, 0;
      4, 1, 4, 0, 4, 4;
      0, 2, 2, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1619 : Certificate {0, 1, 4, 6, 9, 10} := by
  refine ⟨!![2, 1, 0, 2, 0, 1;
      2, 1, 2, 3, 3, 2;
      1, 1, 3, 4, 4, 1;
      2, 0, 1, 0, 4, 3;
      0, 4, 2, 1, 1, 4;
      2, 0, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 6, 9, 10} =
      !![0, 0, 1, 0, 1, 0;
      0, 3, 2, 3, 4, 3;
      0, 4, 0, 3, 4, 3;
      4, 1, 4, 3, 4, 0;
      4, 4, 1, 0, 4, 4;
      3, 0, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1621 : Certificate {0, 2, 4, 6, 9, 10} := by
  refine ⟨!![1, 4, 0, 1, 2, 3;
      4, 1, 3, 3, 0, 1;
      1, 2, 4, 2, 0, 4;
      4, 0, 2, 0, 1, 2;
      1, 3, 4, 3, 1, 3;
      3, 1, 3, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 6, 9, 10} =
      !![0, 0, 2, 2, 4, 4;
      0, 2, 2, 3, 4, 3;
      0, 0, 0, 3, 4, 3;
      4, 4, 4, 3, 4, 0;
      4, 1, 1, 0, 4, 4;
      3, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1622 : Certificate {1, 2, 4, 6, 9, 10} := by
  refine ⟨!![1, 2, 4, 1, 2, 0;
      1, 2, 2, 0, 4, 4;
      2, 2, 2, 3, 2, 1;
      2, 3, 0, 3, 2, 0;
      4, 2, 0, 1, 2, 0;
      3, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 6, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 4, 3;
      4, 0, 0, 3, 4, 3;
      1, 4, 4, 3, 4, 0;
      4, 1, 1, 0, 4, 4;
      0, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1625 : Certificate {0, 3, 4, 6, 9, 10} := by
  refine ⟨!![0, 0, 3, 4, 2, 4;
      4, 3, 1, 0, 2, 4;
      4, 2, 2, 1, 3, 3;
      3, 3, 3, 0, 3, 1;
      3, 3, 1, 4, 3, 4;
      2, 1, 2, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 6, 9, 10} =
      !![0, 3, 2, 2, 4, 4;
      0, 2, 1, 0, 1, 0;
      0, 2, 0, 3, 4, 3;
      4, 2, 4, 3, 4, 0;
      4, 4, 1, 0, 4, 4;
      3, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1626 : Certificate {1, 3, 4, 6, 9, 10} := by
  refine ⟨!![0, 0, 2, 1, 3, 1;
      2, 2, 4, 2, 3, 4;
      2, 1, 2, 4, 2, 4;
      4, 1, 4, 4, 0, 1;
      4, 1, 0, 2, 2, 3;
      1, 3, 1, 4, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 6, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 1, 0, 1, 0;
      4, 2, 0, 3, 4, 3;
      1, 2, 4, 3, 4, 0;
      4, 4, 1, 0, 4, 4;
      0, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1628 : Certificate {2, 3, 4, 6, 9, 10} := by
  refine ⟨!![0, 0, 3, 4, 2, 4;
      1, 2, 4, 3, 1, 1;
      4, 1, 0, 1, 3, 4;
      1, 1, 1, 3, 2, 3;
      1, 1, 3, 4, 3, 3;
      2, 3, 1, 3, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 6, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 2, 2, 4, 4;
      0, 2, 0, 3, 4, 3;
      4, 2, 4, 3, 4, 0;
      1, 4, 1, 0, 4, 4;
      2, 2, 3, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1635 : Certificate {0, 1, 5, 6, 9, 10} := by
  refine ⟨!![3, 0, 4, 0, 3, 3;
      1, 4, 2, 1, 1, 4;
      4, 1, 1, 2, 2, 3;
      4, 4, 1, 4, 3, 4;
      1, 0, 0, 0, 0, 0;
      1, 0, 3, 2, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 6, 9, 10} =
      !![0, 0, 0, 0, 1, 0;
      0, 3, 2, 3, 4, 3;
      0, 2, 0, 3, 3, 3;
      4, 1, 4, 3, 4, 0;
      4, 4, 4, 0, 4, 4;
      3, 0, 1, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1637 : Certificate {0, 2, 5, 6, 9, 10} := by
  refine ⟨!![3, 1, 1, 1, 3, 0;
      3, 3, 3, 4, 3, 4;
      4, 4, 2, 0, 2, 4;
      3, 1, 1, 4, 2, 2;
      4, 0, 2, 1, 3, 3;
      2, 3, 3, 2, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 6, 9, 10} =
      !![0, 0, 4, 2, 4, 4;
      0, 2, 2, 3, 4, 3;
      0, 1, 0, 3, 3, 3;
      4, 4, 4, 3, 4, 0;
      4, 1, 4, 0, 4, 4;
      3, 2, 1, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1638 : Certificate {1, 2, 5, 6, 9, 10} := by
  refine ⟨!![2, 2, 1, 3, 0, 4;
      4, 1, 4, 4, 0, 2;
      0, 1, 4, 2, 3, 4;
      2, 2, 1, 1, 4, 1;
      4, 1, 1, 4, 4, 1;
      3, 2, 3, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 6, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 4, 3;
      2, 1, 0, 3, 3, 3;
      1, 4, 4, 3, 4, 0;
      4, 1, 4, 0, 4, 4;
      0, 2, 1, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1641 : Certificate {0, 3, 5, 6, 9, 10} := by
  refine ⟨!![3, 1, 3, 2, 4, 4;
      1, 1, 3, 4, 2, 2;
      2, 2, 4, 1, 2, 1;
      2, 0, 0, 1, 1, 4;
      3, 4, 4, 2, 1, 1;
      1, 2, 1, 1, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 6, 9, 10} =
      !![0, 3, 4, 2, 4, 4;
      0, 2, 0, 0, 1, 0;
      0, 2, 0, 3, 3, 3;
      4, 2, 4, 3, 4, 0;
      4, 4, 4, 0, 4, 4;
      3, 2, 1, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1642 : Certificate {1, 3, 5, 6, 9, 10} := by
  refine ⟨!![4, 1, 1, 0, 1, 1;
      0, 4, 2, 0, 4, 4;
      1, 2, 1, 3, 0, 4;
      4, 2, 4, 3, 1, 4;
      0, 3, 1, 0, 2, 2;
      0, 0, 0, 2, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 6, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 0, 0, 1, 0;
      2, 2, 0, 3, 3, 3;
      1, 2, 4, 3, 4, 0;
      4, 4, 4, 0, 4, 4;
      0, 2, 1, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1644 : Certificate {2, 3, 5, 6, 9, 10} := by
  refine ⟨!![4, 2, 3, 3, 2, 2;
      2, 4, 4, 1, 4, 4;
      1, 4, 0, 4, 2, 1;
      3, 1, 1, 2, 0, 3;
      3, 0, 3, 0, 4, 4;
      3, 4, 1, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 6, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 4, 2, 4, 4;
      1, 2, 0, 3, 3, 3;
      4, 2, 4, 3, 4, 0;
      1, 4, 4, 0, 4, 4;
      2, 2, 1, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1649 : Certificate {0, 4, 5, 6, 9, 10} := by
  refine ⟨!![4, 4, 3, 3, 3, 4;
      2, 4, 3, 0, 1, 2;
      1, 3, 3, 4, 2, 2;
      0, 1, 2, 1, 0, 2;
      3, 2, 2, 0, 4, 3;
      4, 0, 0, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 6, 9, 10} =
      !![0, 2, 4, 2, 4, 4;
      0, 1, 0, 0, 1, 0;
      0, 2, 2, 3, 4, 3;
      4, 4, 4, 3, 4, 0;
      4, 1, 4, 0, 4, 4;
      3, 3, 1, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1650 : Certificate {1, 4, 5, 6, 9, 10} := by
  refine ⟨!![4, 4, 0, 0, 4, 4;
      1, 3, 4, 1, 3, 1;
      0, 2, 1, 2, 0, 1;
      2, 3, 2, 1, 2, 4;
      4, 3, 1, 4, 2, 4;
      3, 4, 2, 0, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 6, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 1, 0, 0, 1, 0;
      3, 2, 2, 3, 4, 3;
      1, 4, 4, 3, 4, 0;
      4, 1, 4, 0, 4, 4;
      0, 3, 1, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1652 : Certificate {2, 4, 5, 6, 9, 10} := by
  refine ⟨!![3, 2, 4, 4, 2, 0;
      4, 4, 2, 4, 4, 3;
      0, 3, 2, 3, 1, 4;
      2, 2, 1, 0, 1, 1;
      4, 2, 0, 3, 1, 1;
      3, 1, 4, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 6, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 4, 2, 4, 4;
      2, 2, 2, 3, 4, 3;
      4, 4, 4, 3, 4, 0;
      1, 1, 4, 0, 4, 4;
      2, 3, 1, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1656 : Certificate {3, 4, 5, 6, 9, 10} := by
  refine ⟨!![2, 0, 2, 0, 2, 2;
      3, 3, 3, 2, 1, 1;
      4, 2, 3, 1, 3, 2;
      2, 4, 2, 4, 0, 3;
      3, 2, 4, 3, 0, 0;
      4, 4, 4, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 6, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 4, 2, 4, 4;
      2, 1, 0, 0, 1, 0;
      2, 4, 4, 3, 4, 0;
      4, 1, 4, 0, 4, 4;
      2, 3, 1, 1, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1671 : Certificate {0, 1, 2, 7, 9, 10} := by
  refine ⟨!![3, 0, 4, 0, 0, 2;
      0, 4, 4, 4, 1, 0;
      0, 4, 4, 3, 0, 1;
      2, 2, 0, 1, 2, 1;
      0, 0, 2, 0, 3, 1;
      4, 2, 4, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 7, 9, 10} =
      !![0, 3, 2, 2, 4, 3;
      0, 2, 1, 4, 3, 3;
      0, 4, 0, 4, 4, 3;
      4, 2, 0, 3, 2, 3;
      4, 4, 1, 1, 4, 4;
      3, 0, 2, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1675 : Certificate {0, 1, 3, 7, 9, 10} := by
  refine ⟨!![1, 1, 1, 4, 4, 3;
      0, 0, 0, 1, 1, 4;
      0, 2, 2, 4, 0, 3;
      4, 3, 0, 1, 3, 3;
      0, 4, 1, 3, 3, 2;
      3, 1, 1, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 7, 9, 10} =
      !![0, 0, 2, 4, 1, 0;
      0, 2, 2, 4, 3, 3;
      0, 4, 2, 4, 4, 3;
      4, 2, 3, 3, 2, 3;
      4, 4, 4, 1, 4, 4;
      3, 0, 2, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1677 : Certificate {0, 2, 3, 7, 9, 10} := by
  refine ⟨!![1, 2, 2, 1, 1, 1;
      0, 0, 0, 4, 4, 1;
      0, 2, 2, 2, 3, 0;
      4, 2, 4, 2, 4, 2;
      0, 4, 1, 4, 4, 1;
      3, 4, 4, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 7, 9, 10} =
      !![0, 0, 3, 1, 4, 4;
      0, 1, 2, 4, 3, 3;
      0, 0, 2, 4, 4, 3;
      4, 0, 3, 3, 2, 3;
      4, 1, 4, 1, 4, 4;
      3, 2, 2, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1678 : Certificate {1, 2, 3, 7, 9, 10} := by
  refine ⟨!![2, 2, 0, 1, 0, 4;
      2, 2, 0, 0, 4, 0;
      4, 1, 2, 4, 3, 3;
      4, 3, 1, 0, 0, 1;
      3, 2, 1, 3, 4, 2;
      2, 0, 3, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 7, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      2, 1, 2, 4, 3, 3;
      4, 0, 2, 4, 4, 3;
      2, 0, 3, 3, 2, 3;
      4, 1, 4, 1, 4, 4;
      0, 2, 2, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1683 : Certificate {0, 1, 4, 7, 9, 10} := by
  refine ⟨!![3, 4, 2, 1, 2, 3;
      4, 3, 4, 4, 2, 2;
      1, 2, 1, 2, 4, 2;
      4, 0, 2, 0, 3, 1;
      4, 3, 1, 3, 4, 4;
      4, 2, 1, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 7, 9, 10} =
      !![0, 0, 1, 4, 1, 0;
      0, 3, 2, 2, 4, 3;
      0, 4, 0, 4, 4, 3;
      4, 2, 3, 3, 2, 3;
      4, 4, 1, 1, 4, 4;
      3, 0, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1685 : Certificate {0, 2, 4, 7, 9, 10} := by
  refine ⟨!![1, 0, 0, 4, 3, 1;
      2, 4, 2, 2, 0, 4;
      2, 4, 2, 3, 1, 3;
      4, 0, 2, 0, 1, 2;
      3, 1, 0, 2, 2, 3;
      4, 2, 1, 4, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 7, 9, 10} =
      !![0, 0, 2, 1, 4, 4;
      0, 2, 2, 2, 4, 3;
      0, 0, 0, 4, 4, 3;
      4, 0, 3, 3, 2, 3;
      4, 1, 1, 1, 4, 4;
      3, 2, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1686 : Certificate {1, 2, 4, 7, 9, 10} := by
  refine ⟨!![4, 2, 2, 3, 4, 1;
      4, 1, 4, 2, 3, 3;
      0, 4, 2, 0, 0, 1;
      2, 1, 3, 3, 1, 1;
      0, 1, 0, 0, 3, 0;
      2, 3, 2, 2, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 7, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 2, 4, 3;
      4, 0, 0, 4, 4, 3;
      2, 0, 3, 3, 2, 3;
      4, 1, 1, 1, 4, 4;
      0, 2, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1689 : Certificate {0, 3, 4, 7, 9, 10} := by
  refine ⟨!![4, 2, 0, 4, 4, 3;
      3, 2, 0, 0, 1, 2;
      0, 0, 0, 1, 1, 4;
      2, 2, 2, 0, 2, 4;
      1, 4, 2, 4, 4, 1;
      4, 4, 0, 3, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 7, 9, 10} =
      !![0, 3, 2, 1, 4, 4;
      0, 2, 1, 4, 1, 0;
      0, 2, 0, 4, 4, 3;
      4, 3, 3, 3, 2, 3;
      4, 4, 1, 1, 4, 4;
      3, 2, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1690 : Certificate {1, 3, 4, 7, 9, 10} := by
  refine ⟨!![4, 1, 1, 0, 3, 2;
      1, 2, 4, 2, 0, 4;
      1, 4, 4, 1, 3, 2;
      4, 2, 3, 3, 3, 2;
      1, 0, 1, 3, 0, 2;
      4, 3, 1, 4, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 7, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 1, 4, 1, 0;
      4, 2, 0, 4, 4, 3;
      2, 3, 3, 3, 2, 3;
      4, 4, 1, 1, 4, 4;
      0, 2, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1692 : Certificate {2, 3, 4, 7, 9, 10} := by
  refine ⟨!![2, 4, 3, 4, 3, 4;
      0, 4, 0, 1, 2, 4;
      2, 4, 3, 0, 4, 3;
      0, 3, 2, 1, 3, 1;
      3, 4, 4, 2, 3, 1;
      1, 3, 4, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 7, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 2, 1, 4, 4;
      0, 2, 0, 4, 4, 3;
      0, 3, 3, 3, 2, 3;
      1, 4, 1, 1, 4, 4;
      2, 2, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1699 : Certificate {0, 1, 5, 7, 9, 10} := by
  refine ⟨!![4, 1, 2, 2, 1, 3;
      3, 1, 2, 1, 3, 3;
      2, 4, 3, 0, 3, 1;
      3, 3, 4, 1, 4, 0;
      4, 3, 4, 1, 4, 0;
      0, 4, 3, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 7, 9, 10} =
      !![0, 0, 0, 4, 1, 0;
      0, 3, 2, 2, 4, 3;
      0, 2, 0, 4, 3, 3;
      4, 2, 3, 3, 2, 3;
      4, 4, 4, 1, 4, 4;
      3, 0, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1701 : Certificate {0, 2, 5, 7, 9, 10} := by
  refine ⟨!![4, 1, 2, 3, 0, 3;
      3, 1, 2, 3, 1, 3;
      3, 1, 2, 4, 2, 2;
      2, 1, 0, 2, 0, 4;
      0, 0, 3, 3, 0, 1;
      3, 0, 0, 0, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 7, 9, 10} =
      !![0, 0, 4, 1, 4, 4;
      0, 2, 2, 2, 4, 3;
      0, 1, 0, 4, 3, 3;
      4, 0, 3, 3, 2, 3;
      4, 1, 4, 1, 4, 4;
      3, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1702 : Certificate {1, 2, 5, 7, 9, 10} := by
  refine ⟨!![1, 1, 3, 0, 3, 1;
      4, 3, 0, 2, 3, 1;
      3, 2, 2, 3, 1, 4;
      2, 0, 0, 3, 1, 2;
      3, 3, 2, 3, 4, 4;
      4, 2, 3, 4, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 7, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 2, 4, 3;
      2, 1, 0, 4, 3, 3;
      2, 0, 3, 3, 2, 3;
      4, 1, 4, 1, 4, 4;
      0, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1705 : Certificate {0, 3, 5, 7, 9, 10} := by
  refine ⟨!![4, 2, 0, 2, 2, 0;
      3, 2, 0, 2, 3, 0;
      0, 0, 0, 1, 1, 4;
      0, 4, 3, 3, 0, 1;
      4, 1, 3, 4, 4, 1;
      4, 4, 0, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 7, 9, 10} =
      !![0, 3, 4, 1, 4, 4;
      0, 2, 0, 4, 1, 0;
      0, 2, 0, 4, 3, 3;
      4, 3, 3, 3, 2, 3;
      4, 4, 4, 1, 4, 4;
      3, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1706 : Certificate {1, 3, 5, 7, 9, 10} := by
  refine ⟨!![3, 0, 3, 1, 2, 4;
      4, 3, 4, 1, 0, 2;
      2, 0, 2, 0, 4, 0;
      4, 4, 2, 1, 1, 3;
      1, 4, 4, 4, 1, 4;
      4, 2, 4, 0, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 7, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 0, 4, 1, 0;
      2, 2, 0, 4, 3, 3;
      2, 3, 3, 3, 2, 3;
      4, 4, 4, 1, 4, 4;
      0, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1708 : Certificate {2, 3, 5, 7, 9, 10} := by
  refine ⟨!![1, 0, 1, 2, 4, 3;
      4, 4, 4, 3, 2, 2;
      1, 0, 1, 3, 0, 2;
      4, 2, 2, 2, 2, 3;
      2, 2, 0, 2, 1, 2;
      3, 1, 3, 1, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 7, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 4, 1, 4, 4;
      1, 2, 0, 4, 3, 3;
      0, 3, 3, 3, 2, 3;
      1, 4, 4, 1, 4, 4;
      2, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1713 : Certificate {0, 4, 5, 7, 9, 10} := by
  refine ⟨!![2, 4, 0, 4, 0, 0;
      4, 1, 0, 1, 4, 0;
      1, 4, 0, 0, 2, 4;
      1, 1, 1, 3, 4, 4;
      2, 1, 1, 2, 0, 4;
      0, 3, 0, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 7, 9, 10} =
      !![0, 2, 4, 1, 4, 4;
      0, 1, 0, 4, 1, 0;
      0, 2, 2, 2, 4, 3;
      4, 3, 3, 3, 2, 3;
      4, 1, 4, 1, 4, 4;
      3, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1714 : Certificate {1, 4, 5, 7, 9, 10} := by
  refine ⟨!![1, 4, 2, 2, 4, 4;
      3, 0, 1, 4, 1, 2;
      1, 1, 2, 0, 1, 3;
      4, 0, 4, 4, 0, 0;
      1, 1, 3, 0, 4, 3;
      4, 4, 3, 1, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 7, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 1, 0, 4, 1, 0;
      3, 2, 2, 2, 4, 3;
      2, 3, 3, 3, 2, 3;
      4, 1, 4, 1, 4, 4;
      0, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1716 : Certificate {2, 4, 5, 7, 9, 10} := by
  refine ⟨!![1, 3, 2, 3, 4, 4;
      1, 4, 2, 3, 3, 4;
      0, 4, 0, 1, 2, 4;
      1, 1, 3, 0, 3, 3;
      0, 4, 1, 1, 0, 4;
      3, 0, 1, 4, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 7, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 4, 1, 4, 4;
      2, 2, 2, 2, 4, 3;
      0, 3, 3, 3, 2, 3;
      1, 1, 4, 1, 4, 4;
      2, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1720 : Certificate {3, 4, 5, 7, 9, 10} := by
  refine ⟨!![0, 2, 4, 4, 0, 0;
      0, 3, 4, 4, 4, 0;
      0, 2, 1, 2, 2, 4;
      2, 3, 3, 1, 2, 2;
      2, 1, 2, 4, 3, 2;
      0, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 7, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 4, 1, 4, 4;
      2, 1, 0, 4, 1, 0;
      3, 3, 3, 3, 2, 3;
      4, 1, 4, 1, 4, 4;
      2, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1731 : Certificate {0, 1, 6, 7, 9, 10} := by
  refine ⟨!![2, 2, 3, 4, 3, 3;
      1, 2, 1, 2, 0, 0;
      1, 2, 4, 0, 4, 3;
      2, 1, 2, 2, 0, 0;
      3, 1, 2, 2, 0, 0;
      1, 1, 1, 4, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 6, 7, 9, 10} =
      !![0, 0, 0, 4, 1, 0;
      0, 3, 3, 2, 4, 3;
      0, 2, 3, 4, 3, 3;
      0, 4, 3, 4, 4, 3;
      4, 4, 0, 1, 4, 4;
      3, 0, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1733 : Certificate {0, 2, 6, 7, 9, 10} := by
  refine ⟨!![2, 2, 2, 3, 4, 0;
      3, 1, 4, 2, 4, 3;
      1, 2, 1, 2, 2, 4;
      3, 3, 4, 0, 4, 3;
      3, 1, 3, 3, 4, 3;
      1, 1, 3, 1, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 6, 7, 9, 10} =
      !![0, 0, 2, 1, 4, 4;
      0, 2, 3, 2, 4, 3;
      0, 1, 3, 4, 3, 3;
      0, 0, 3, 4, 4, 3;
      4, 1, 0, 1, 4, 4;
      3, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1734 : Certificate {1, 2, 6, 7, 9, 10} := by
  refine ⟨!![1, 4, 3, 4, 3, 3;
      2, 1, 2, 3, 4, 4;
      0, 1, 0, 3, 0, 4;
      4, 1, 3, 4, 0, 0;
      0, 3, 0, 1, 3, 3;
      0, 0, 2, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 6, 7, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 2, 3, 2, 4, 3;
      2, 1, 3, 4, 3, 3;
      4, 0, 3, 4, 4, 3;
      4, 1, 0, 1, 4, 4;
      0, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1737 : Certificate {0, 3, 6, 7, 9, 10} := by
  refine ⟨!![4, 2, 0, 0, 0, 2;
      2, 3, 4, 4, 1, 2;
      2, 3, 2, 2, 0, 0;
      4, 0, 2, 4, 2, 4;
      0, 0, 4, 1, 0, 0;
      3, 0, 4, 4, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 6, 7, 9, 10} =
      !![0, 3, 2, 1, 4, 4;
      0, 2, 0, 4, 1, 0;
      0, 2, 3, 4, 3, 3;
      0, 2, 3, 4, 4, 3;
      4, 4, 0, 1, 4, 4;
      3, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1738 : Certificate {1, 3, 6, 7, 9, 10} := by
  refine ⟨!![1, 1, 2, 1, 2, 2;
      2, 4, 3, 1, 0, 0;
      3, 0, 3, 0, 1, 0;
      2, 0, 1, 1, 1, 1;
      3, 3, 0, 4, 1, 1;
      1, 2, 1, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 6, 7, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 0, 4, 1, 0;
      2, 2, 3, 4, 3, 3;
      4, 2, 3, 4, 4, 3;
      4, 4, 0, 1, 4, 4;
      0, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1740 : Certificate {2, 3, 6, 7, 9, 10} := by
  refine ⟨!![1, 3, 2, 1, 2, 1;
      2, 2, 3, 1, 0, 1;
      4, 3, 0, 1, 3, 1;
      3, 3, 3, 2, 3, 2;
      1, 3, 1, 2, 2, 1;
      1, 1, 1, 0, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 6, 7, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 3, 2, 1, 4, 4;
      1, 2, 3, 4, 3, 3;
      0, 2, 3, 4, 4, 3;
      1, 4, 0, 1, 4, 4;
      2, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1745 : Certificate {0, 4, 6, 7, 9, 10} := by
  refine ⟨!![1, 1, 2, 1, 1, 4;
      3, 1, 3, 4, 4, 3;
      1, 4, 0, 0, 2, 4;
      3, 1, 0, 2, 4, 3;
      0, 1, 2, 3, 0, 0;
      0, 0, 4, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 6, 7, 9, 10} =
      !![0, 2, 2, 1, 4, 4;
      0, 1, 0, 4, 1, 0;
      0, 2, 3, 2, 4, 3;
      0, 0, 3, 4, 4, 3;
      4, 1, 0, 1, 4, 4;
      3, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1746 : Certificate {1, 4, 6, 7, 9, 10} := by
  refine ⟨!![2, 4, 1, 1, 1, 1;
      2, 2, 3, 2, 2, 2;
      2, 2, 4, 0, 2, 1;
      1, 0, 2, 2, 4, 4;
      4, 4, 4, 0, 2, 2;
      2, 4, 0, 3, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 6, 7, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 1, 0, 4, 1, 0;
      3, 2, 3, 2, 4, 3;
      4, 0, 3, 4, 4, 3;
      4, 1, 0, 1, 4, 4;
      0, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1748 : Certificate {2, 4, 6, 7, 9, 10} := by
  refine ⟨!![4, 2, 1, 4, 4, 0;
      3, 1, 3, 1, 1, 4;
      3, 1, 4, 4, 1, 3;
      2, 3, 1, 3, 0, 4;
      1, 2, 4, 3, 0, 1;
      3, 4, 1, 0, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 6, 7, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 2, 1, 4, 4;
      2, 2, 3, 2, 4, 3;
      0, 0, 3, 4, 4, 3;
      1, 1, 0, 1, 4, 4;
      2, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1752 : Certificate {3, 4, 6, 7, 9, 10} := by
  refine ⟨!![3, 3, 4, 2, 2, 1;
      0, 4, 2, 0, 0, 2;
      4, 0, 1, 1, 3, 2;
      4, 2, 3, 3, 0, 1;
      3, 2, 4, 4, 1, 2;
      3, 1, 2, 2, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 6, 7, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 2, 2, 1, 4, 4;
      2, 1, 0, 4, 1, 0;
      2, 0, 3, 4, 4, 3;
      4, 1, 0, 1, 4, 4;
      2, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1761 : Certificate {0, 5, 6, 7, 9, 10} := by
  refine ⟨!![3, 4, 2, 4, 2, 1;
      2, 1, 1, 2, 1, 2;
      4, 3, 4, 3, 1, 2;
      4, 3, 1, 0, 2, 4;
      4, 4, 1, 0, 2, 4;
      0, 4, 2, 4, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 6, 7, 9, 10} =
      !![0, 4, 2, 1, 4, 4;
      0, 0, 0, 4, 1, 0;
      0, 2, 3, 2, 4, 3;
      0, 0, 3, 4, 3, 3;
      4, 4, 0, 1, 4, 4;
      3, 1, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1762 : Certificate {1, 5, 6, 7, 9, 10} := by
  refine ⟨!![4, 2, 0, 4, 2, 2;
      3, 4, 3, 4, 2, 2;
      1, 4, 3, 2, 3, 2;
      0, 1, 0, 3, 1, 1;
      0, 2, 0, 3, 1, 1;
      3, 3, 2, 2, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 6, 7, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 0, 0, 4, 1, 0;
      3, 2, 3, 2, 4, 3;
      2, 0, 3, 4, 3, 3;
      4, 4, 0, 1, 4, 4;
      0, 1, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1764 : Certificate {2, 5, 6, 7, 9, 10} := by
  refine ⟨!![1, 4, 1, 3, 4, 1;
      4, 1, 2, 3, 4, 2;
      3, 0, 3, 4, 4, 3;
      2, 1, 4, 3, 1, 4;
      0, 1, 4, 1, 0, 3;
      4, 3, 4, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 6, 7, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 4, 2, 1, 4, 4;
      2, 2, 3, 2, 4, 3;
      1, 0, 3, 4, 3, 3;
      1, 4, 0, 1, 4, 4;
      2, 1, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1768 : Certificate {3, 5, 6, 7, 9, 10} := by
  refine ⟨!![1, 0, 3, 1, 3, 3;
      0, 3, 4, 0, 0, 4;
      3, 3, 4, 3, 1, 4;
      1, 0, 4, 4, 4, 4;
      4, 0, 4, 2, 3, 3;
      1, 2, 3, 1, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 6, 7, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 4, 2, 1, 4, 4;
      2, 0, 0, 4, 1, 0;
      2, 0, 3, 4, 3, 3;
      4, 4, 0, 1, 4, 4;
      2, 1, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1776 : Certificate {4, 5, 6, 7, 9, 10} := by
  refine ⟨!![4, 2, 3, 3, 0, 1;
      2, 4, 3, 4, 0, 2;
      3, 2, 1, 1, 2, 2;
      2, 0, 2, 0, 2, 2;
      3, 3, 0, 2, 2, 1;
      1, 0, 2, 2, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 6, 7, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      2, 4, 2, 1, 4, 4;
      1, 0, 0, 4, 1, 0;
      2, 2, 3, 2, 4, 3;
      1, 4, 0, 1, 4, 4;
      3, 1, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 1671 then
    if mask < 1613 then
      if mask < 1582 then
        if mask < 1566 then
          if mask < 1563 then
            if mask < 1559 then
              ⟨{0, 1, 2, 3, 9, 10}, certificate_1551⟩
            else
              ⟨{0, 1, 2, 4, 9, 10}, certificate_1559⟩
          else
            if mask < 1565 then
              ⟨{0, 1, 3, 4, 9, 10}, certificate_1563⟩
            else
              ⟨{0, 2, 3, 4, 9, 10}, certificate_1565⟩
        else
          if mask < 1579 then
            if mask < 1575 then
              ⟨{1, 2, 3, 4, 9, 10}, certificate_1566⟩
            else
              ⟨{0, 1, 2, 5, 9, 10}, certificate_1575⟩
          else
            if mask < 1581 then
              ⟨{0, 1, 3, 5, 9, 10}, certificate_1579⟩
            else
              ⟨{0, 2, 3, 5, 9, 10}, certificate_1581⟩
      else
        if mask < 1593 then
          if mask < 1589 then
            if mask < 1587 then
              ⟨{1, 2, 3, 5, 9, 10}, certificate_1582⟩
            else
              ⟨{0, 1, 4, 5, 9, 10}, certificate_1587⟩
          else
            if mask < 1590 then
              ⟨{0, 2, 4, 5, 9, 10}, certificate_1589⟩
            else
              ⟨{1, 2, 4, 5, 9, 10}, certificate_1590⟩
        else
          if mask < 1596 then
            if mask < 1594 then
              ⟨{0, 3, 4, 5, 9, 10}, certificate_1593⟩
            else
              ⟨{1, 3, 4, 5, 9, 10}, certificate_1594⟩
          else
            if mask < 1607 then
              ⟨{2, 3, 4, 5, 9, 10}, certificate_1596⟩
            else
              if mask < 1611 then
                ⟨{0, 1, 2, 6, 9, 10}, certificate_1607⟩
              else
                ⟨{0, 1, 3, 6, 9, 10}, certificate_1611⟩
    else
      if mask < 1637 then
        if mask < 1622 then
          if mask < 1619 then
            if mask < 1614 then
              ⟨{0, 2, 3, 6, 9, 10}, certificate_1613⟩
            else
              ⟨{1, 2, 3, 6, 9, 10}, certificate_1614⟩
          else
            if mask < 1621 then
              ⟨{0, 1, 4, 6, 9, 10}, certificate_1619⟩
            else
              ⟨{0, 2, 4, 6, 9, 10}, certificate_1621⟩
        else
          if mask < 1626 then
            if mask < 1625 then
              ⟨{1, 2, 4, 6, 9, 10}, certificate_1622⟩
            else
              ⟨{0, 3, 4, 6, 9, 10}, certificate_1625⟩
          else
            if mask < 1628 then
              ⟨{1, 3, 4, 6, 9, 10}, certificate_1626⟩
            else
              if mask < 1635 then
                ⟨{2, 3, 4, 6, 9, 10}, certificate_1628⟩
              else
                ⟨{0, 1, 5, 6, 9, 10}, certificate_1635⟩
      else
        if mask < 1644 then
          if mask < 1641 then
            if mask < 1638 then
              ⟨{0, 2, 5, 6, 9, 10}, certificate_1637⟩
            else
              ⟨{1, 2, 5, 6, 9, 10}, certificate_1638⟩
          else
            if mask < 1642 then
              ⟨{0, 3, 5, 6, 9, 10}, certificate_1641⟩
            else
              ⟨{1, 3, 5, 6, 9, 10}, certificate_1642⟩
        else
          if mask < 1650 then
            if mask < 1649 then
              ⟨{2, 3, 5, 6, 9, 10}, certificate_1644⟩
            else
              ⟨{0, 4, 5, 6, 9, 10}, certificate_1649⟩
          else
            if mask < 1652 then
              ⟨{1, 4, 5, 6, 9, 10}, certificate_1650⟩
            else
              if mask < 1656 then
                ⟨{2, 4, 5, 6, 9, 10}, certificate_1652⟩
              else
                ⟨{3, 4, 5, 6, 9, 10}, certificate_1656⟩
  else
    if mask < 1714 then
      if mask < 1690 then
        if mask < 1683 then
          if mask < 1677 then
            if mask < 1675 then
              ⟨{0, 1, 2, 7, 9, 10}, certificate_1671⟩
            else
              ⟨{0, 1, 3, 7, 9, 10}, certificate_1675⟩
          else
            if mask < 1678 then
              ⟨{0, 2, 3, 7, 9, 10}, certificate_1677⟩
            else
              ⟨{1, 2, 3, 7, 9, 10}, certificate_1678⟩
        else
          if mask < 1686 then
            if mask < 1685 then
              ⟨{0, 1, 4, 7, 9, 10}, certificate_1683⟩
            else
              ⟨{0, 2, 4, 7, 9, 10}, certificate_1685⟩
          else
            if mask < 1689 then
              ⟨{1, 2, 4, 7, 9, 10}, certificate_1686⟩
            else
              ⟨{0, 3, 4, 7, 9, 10}, certificate_1689⟩
      else
        if mask < 1702 then
          if mask < 1699 then
            if mask < 1692 then
              ⟨{1, 3, 4, 7, 9, 10}, certificate_1690⟩
            else
              ⟨{2, 3, 4, 7, 9, 10}, certificate_1692⟩
          else
            if mask < 1701 then
              ⟨{0, 1, 5, 7, 9, 10}, certificate_1699⟩
            else
              ⟨{0, 2, 5, 7, 9, 10}, certificate_1701⟩
        else
          if mask < 1706 then
            if mask < 1705 then
              ⟨{1, 2, 5, 7, 9, 10}, certificate_1702⟩
            else
              ⟨{0, 3, 5, 7, 9, 10}, certificate_1705⟩
          else
            if mask < 1708 then
              ⟨{1, 3, 5, 7, 9, 10}, certificate_1706⟩
            else
              if mask < 1713 then
                ⟨{2, 3, 5, 7, 9, 10}, certificate_1708⟩
              else
                ⟨{0, 4, 5, 7, 9, 10}, certificate_1713⟩
    else
      if mask < 1745 then
        if mask < 1733 then
          if mask < 1720 then
            if mask < 1716 then
              ⟨{1, 4, 5, 7, 9, 10}, certificate_1714⟩
            else
              ⟨{2, 4, 5, 7, 9, 10}, certificate_1716⟩
          else
            if mask < 1731 then
              ⟨{3, 4, 5, 7, 9, 10}, certificate_1720⟩
            else
              ⟨{0, 1, 6, 7, 9, 10}, certificate_1731⟩
        else
          if mask < 1737 then
            if mask < 1734 then
              ⟨{0, 2, 6, 7, 9, 10}, certificate_1733⟩
            else
              ⟨{1, 2, 6, 7, 9, 10}, certificate_1734⟩
          else
            if mask < 1738 then
              ⟨{0, 3, 6, 7, 9, 10}, certificate_1737⟩
            else
              if mask < 1740 then
                ⟨{1, 3, 6, 7, 9, 10}, certificate_1738⟩
              else
                ⟨{2, 3, 6, 7, 9, 10}, certificate_1740⟩
      else
        if mask < 1761 then
          if mask < 1748 then
            if mask < 1746 then
              ⟨{0, 4, 6, 7, 9, 10}, certificate_1745⟩
            else
              ⟨{1, 4, 6, 7, 9, 10}, certificate_1746⟩
          else
            if mask < 1752 then
              ⟨{2, 4, 6, 7, 9, 10}, certificate_1748⟩
            else
              ⟨{3, 4, 6, 7, 9, 10}, certificate_1752⟩
        else
          if mask < 1764 then
            if mask < 1762 then
              ⟨{0, 5, 6, 7, 9, 10}, certificate_1761⟩
            else
              ⟨{1, 5, 6, 7, 9, 10}, certificate_1762⟩
          else
            if mask < 1768 then
              ⟨{2, 5, 6, 7, 9, 10}, certificate_1764⟩
            else
              if mask < 1776 then
                ⟨{3, 5, 6, 7, 9, 10}, certificate_1768⟩
              else
                ⟨{4, 5, 6, 7, 9, 10}, certificate_1776⟩
end AMEProbe.QuinaryDirect.Batch06
#print axioms AMEProbe.QuinaryDirect.Batch06.lookup
