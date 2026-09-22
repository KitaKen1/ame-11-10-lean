import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch07
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_1799 : Certificate {0, 1, 2, 8, 9, 10} := by
  refine ⟨!![4, 3, 0, 3, 1, 0;
      2, 2, 2, 0, 3, 1;
      4, 1, 3, 0, 4, 3;
      4, 2, 4, 2, 4, 2;
      3, 0, 3, 4, 1, 0;
      3, 3, 0, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 8, 9, 10} =
      !![0, 3, 2, 4, 4, 3;
      0, 2, 1, 1, 3, 3;
      0, 4, 0, 4, 4, 3;
      4, 2, 0, 0, 2, 3;
      4, 1, 4, 1, 4, 0;
      3, 0, 2, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1803 : Certificate {0, 1, 3, 8, 9, 10} := by
  refine ⟨!![0, 2, 2, 3, 2, 2;
      0, 4, 3, 0, 1, 2;
      2, 2, 4, 3, 4, 4;
      4, 0, 4, 3, 3, 2;
      3, 1, 3, 1, 4, 0;
      1, 2, 1, 1, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 8, 9, 10} =
      !![0, 0, 2, 1, 1, 0;
      0, 2, 2, 1, 3, 3;
      0, 4, 2, 4, 4, 3;
      4, 2, 3, 0, 2, 3;
      4, 1, 2, 1, 4, 0;
      3, 0, 2, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1805 : Certificate {0, 2, 3, 8, 9, 10} := by
  refine ⟨!![0, 4, 1, 3, 0, 3;
      0, 2, 4, 0, 3, 1;
      4, 0, 3, 2, 4, 2;
      3, 3, 1, 1, 1, 4;
      1, 2, 2, 2, 0, 4;
      2, 0, 1, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 8, 9, 10} =
      !![0, 0, 3, 4, 4, 4;
      0, 1, 2, 1, 3, 3;
      0, 0, 2, 4, 4, 3;
      4, 0, 3, 0, 2, 3;
      4, 4, 2, 1, 4, 0;
      3, 2, 2, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1806 : Certificate {1, 2, 3, 8, 9, 10} := by
  refine ⟨!![0, 3, 2, 1, 0, 1;
      0, 3, 3, 2, 3, 3;
      1, 0, 2, 3, 1, 3;
      2, 4, 3, 0, 0, 3;
      4, 4, 1, 0, 3, 2;
      3, 2, 1, 0, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 8, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      2, 1, 2, 1, 3, 3;
      4, 0, 2, 4, 4, 3;
      2, 0, 3, 0, 2, 3;
      1, 4, 2, 1, 4, 0;
      0, 2, 2, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1811 : Certificate {0, 1, 4, 8, 9, 10} := by
  refine ⟨!![2, 4, 4, 1, 0, 4;
      3, 2, 3, 2, 4, 2;
      4, 4, 1, 1, 2, 1;
      0, 1, 3, 2, 1, 1;
      2, 0, 1, 2, 2, 3;
      0, 1, 1, 2, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 8, 9, 10} =
      !![0, 0, 1, 1, 1, 0;
      0, 3, 2, 4, 4, 3;
      0, 4, 0, 4, 4, 3;
      4, 2, 3, 0, 2, 3;
      4, 1, 4, 1, 4, 0;
      3, 0, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1813 : Certificate {0, 2, 4, 8, 9, 10} := by
  refine ⟨!![0, 1, 2, 3, 4, 1;
      1, 3, 4, 3, 1, 3;
      4, 0, 3, 2, 4, 2;
      2, 2, 1, 3, 3, 2;
      2, 3, 2, 0, 3, 1;
      3, 0, 3, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 8, 9, 10} =
      !![0, 0, 2, 4, 4, 4;
      0, 2, 2, 4, 4, 3;
      0, 0, 0, 4, 4, 3;
      4, 0, 3, 0, 2, 3;
      4, 4, 4, 1, 4, 0;
      3, 2, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1814 : Certificate {1, 2, 4, 8, 9, 10} := by
  refine ⟨!![0, 1, 2, 3, 4, 1;
      2, 1, 2, 0, 4, 4;
      3, 0, 1, 4, 3, 4;
      4, 3, 2, 2, 4, 4;
      4, 3, 1, 1, 0, 2;
      1, 4, 2, 2, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 8, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 4, 4, 3;
      4, 0, 0, 4, 4, 3;
      2, 0, 3, 0, 2, 3;
      1, 4, 4, 1, 4, 0;
      0, 2, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1817 : Certificate {0, 3, 4, 8, 9, 10} := by
  refine ⟨!![4, 3, 1, 2, 2, 0;
      2, 1, 4, 0, 0, 0;
      2, 4, 4, 2, 4, 2;
      3, 0, 0, 1, 4, 0;
      1, 0, 3, 2, 2, 3;
      0, 1, 2, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 8, 9, 10} =
      !![0, 3, 2, 4, 4, 4;
      0, 2, 1, 1, 1, 0;
      0, 2, 0, 4, 4, 3;
      4, 3, 3, 0, 2, 3;
      4, 2, 4, 1, 4, 0;
      3, 2, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1818 : Certificate {1, 3, 4, 8, 9, 10} := by
  refine ⟨!![1, 3, 4, 2, 1, 4;
      4, 4, 2, 2, 3, 1;
      1, 3, 0, 3, 4, 1;
      4, 1, 4, 0, 4, 1;
      2, 4, 2, 3, 1, 1;
      3, 0, 4, 2, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 8, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 1, 1, 1, 0;
      4, 2, 0, 4, 4, 3;
      2, 3, 3, 0, 2, 3;
      1, 2, 4, 1, 4, 0;
      0, 2, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1820 : Certificate {2, 3, 4, 8, 9, 10} := by
  refine ⟨!![4, 4, 2, 0, 1, 1;
      4, 3, 4, 1, 2, 1;
      1, 1, 4, 1, 2, 1;
      1, 4, 3, 1, 3, 4;
      4, 0, 0, 2, 3, 4;
      4, 1, 2, 2, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 8, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 2, 4, 4, 4;
      0, 2, 0, 4, 4, 3;
      0, 3, 3, 0, 2, 3;
      4, 2, 4, 1, 4, 0;
      2, 2, 3, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1827 : Certificate {0, 1, 5, 8, 9, 10} := by
  refine ⟨!![1, 3, 0, 2, 2, 0;
      4, 2, 1, 1, 1, 4;
      4, 1, 3, 1, 4, 0;
      1, 1, 1, 1, 3, 3;
      0, 4, 4, 4, 2, 2;
      2, 1, 2, 0, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 8, 9, 10} =
      !![0, 0, 0, 1, 1, 0;
      0, 3, 2, 4, 4, 3;
      0, 2, 0, 1, 3, 3;
      4, 2, 3, 0, 2, 3;
      4, 1, 4, 1, 4, 0;
      3, 0, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1829 : Certificate {0, 2, 5, 8, 9, 10} := by
  refine ⟨!![3, 3, 2, 2, 0, 1;
      2, 2, 4, 1, 3, 3;
      2, 1, 1, 1, 1, 4;
      4, 2, 0, 4, 0, 3;
      2, 1, 3, 0, 0, 0;
      1, 1, 1, 0, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 2, 4, 4, 3;
      0, 1, 0, 1, 3, 3;
      4, 0, 3, 0, 2, 3;
      4, 4, 4, 1, 4, 0;
      3, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1830 : Certificate {1, 2, 5, 8, 9, 10} := by
  refine ⟨!![4, 3, 4, 4, 1, 3;
      1, 2, 2, 4, 2, 1;
      0, 4, 3, 3, 1, 0;
      3, 4, 2, 1, 2, 1;
      1, 1, 1, 3, 4, 3;
      0, 0, 2, 1, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 8, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 4, 4, 3;
      2, 1, 0, 1, 3, 3;
      2, 0, 3, 0, 2, 3;
      1, 4, 4, 1, 4, 0;
      0, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1833 : Certificate {0, 3, 5, 8, 9, 10} := by
  refine ⟨!![0, 0, 1, 3, 3, 4;
      2, 1, 3, 0, 2, 4;
      3, 1, 2, 3, 4, 4;
      0, 4, 3, 3, 0, 1;
      1, 0, 1, 2, 1, 1;
      1, 3, 3, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 8, 9, 10} =
      !![0, 3, 4, 4, 4, 4;
      0, 2, 0, 1, 1, 0;
      0, 2, 0, 1, 3, 3;
      4, 3, 3, 0, 2, 3;
      4, 2, 4, 1, 4, 0;
      3, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1834 : Certificate {1, 3, 5, 8, 9, 10} := by
  refine ⟨!![0, 0, 1, 3, 3, 4;
      4, 4, 3, 4, 1, 4;
      1, 3, 0, 3, 4, 1;
      0, 4, 1, 2, 4, 3;
      2, 4, 3, 0, 4, 4;
      2, 2, 1, 3, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 8, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 0, 1, 1, 0;
      2, 2, 0, 1, 3, 3;
      2, 3, 3, 0, 2, 3;
      1, 2, 4, 1, 4, 0;
      0, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1836 : Certificate {2, 3, 5, 8, 9, 10} := by
  refine ⟨!![0, 0, 1, 3, 3, 4;
      2, 1, 1, 1, 3, 1;
      2, 2, 3, 3, 4, 3;
      3, 1, 1, 0, 2, 3;
      0, 1, 4, 1, 0, 3;
      1, 3, 0, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 8, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 4, 4, 4, 4;
      1, 2, 0, 1, 3, 3;
      0, 3, 3, 0, 2, 3;
      4, 2, 4, 1, 4, 0;
      2, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1841 : Certificate {0, 4, 5, 8, 9, 10} := by
  refine ⟨!![2, 0, 2, 4, 1, 2;
      3, 1, 1, 3, 1, 3;
      3, 3, 1, 1, 2, 1;
      0, 2, 4, 0, 2, 4;
      2, 3, 0, 2, 2, 3;
      0, 4, 2, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 8, 9, 10} =
      !![0, 2, 4, 4, 4, 4;
      0, 1, 0, 1, 1, 0;
      0, 2, 2, 4, 4, 3;
      4, 3, 3, 0, 2, 3;
      4, 4, 4, 1, 4, 0;
      3, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1842 : Certificate {1, 4, 5, 8, 9, 10} := by
  refine ⟨!![2, 3, 3, 2, 3, 1;
      0, 1, 3, 2, 2, 0;
      1, 2, 2, 1, 2, 1;
      2, 0, 2, 2, 0, 0;
      3, 0, 0, 1, 3, 0;
      4, 0, 3, 2, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 8, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 1, 0, 1, 1, 0;
      3, 2, 2, 4, 4, 3;
      2, 3, 3, 0, 2, 3;
      1, 4, 4, 1, 4, 0;
      0, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1844 : Certificate {2, 4, 5, 8, 9, 10} := by
  refine ⟨!![0, 1, 1, 2, 3, 1;
      1, 1, 3, 0, 4, 4;
      3, 1, 1, 0, 3, 3;
      2, 1, 3, 4, 3, 1;
      3, 3, 3, 2, 2, 3;
      4, 1, 4, 4, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 8, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 4, 4, 4, 4;
      2, 2, 2, 4, 4, 3;
      0, 3, 3, 0, 2, 3;
      4, 4, 4, 1, 4, 0;
      2, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1848 : Certificate {3, 4, 5, 8, 9, 10} := by
  refine ⟨!![3, 3, 2, 4, 1, 2;
      2, 4, 4, 2, 2, 0;
      4, 1, 4, 1, 2, 1;
      1, 2, 1, 0, 2, 4;
      1, 3, 2, 0, 4, 2;
      2, 0, 2, 0, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 8, 9, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 4, 4, 4, 4;
      2, 1, 0, 1, 1, 0;
      3, 3, 3, 0, 2, 3;
      2, 4, 4, 1, 4, 0;
      2, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1859 : Certificate {0, 1, 6, 8, 9, 10} := by
  refine ⟨!![3, 4, 1, 1, 2, 1;
      0, 4, 0, 1, 0, 0;
      0, 1, 4, 2, 1, 2;
      2, 1, 2, 2, 0, 0;
      4, 4, 3, 3, 0, 0;
      2, 2, 1, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 6, 8, 9, 10} =
      !![0, 0, 0, 1, 1, 0;
      0, 3, 3, 4, 4, 3;
      0, 2, 3, 1, 3, 3;
      0, 4, 3, 4, 4, 3;
      4, 1, 3, 1, 4, 0;
      3, 0, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1861 : Certificate {0, 2, 6, 8, 9, 10} := by
  refine ⟨!![4, 4, 3, 3, 0, 2;
      0, 3, 0, 2, 0, 0;
      0, 4, 4, 4, 1, 2;
      1, 2, 0, 4, 2, 4;
      2, 2, 4, 1, 4, 3;
      1, 4, 4, 3, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 6, 8, 9, 10} =
      !![0, 0, 2, 4, 4, 4;
      0, 2, 3, 4, 4, 3;
      0, 1, 3, 1, 3, 3;
      0, 0, 3, 4, 4, 3;
      4, 4, 3, 1, 4, 0;
      3, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1862 : Certificate {1, 2, 6, 8, 9, 10} := by
  refine ⟨!![1, 3, 4, 4, 3, 4;
      3, 2, 2, 4, 4, 2;
      3, 3, 1, 1, 0, 4;
      1, 4, 2, 1, 0, 0;
      3, 4, 2, 4, 3, 4;
      2, 4, 0, 4, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 6, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 2, 3, 4, 4, 3;
      2, 1, 3, 1, 3, 3;
      4, 0, 3, 4, 4, 3;
      1, 4, 3, 1, 4, 0;
      0, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1865 : Certificate {0, 3, 6, 8, 9, 10} := by
  refine ⟨!![2, 4, 2, 1, 1, 4;
      2, 1, 1, 1, 4, 3;
      0, 0, 4, 3, 1, 2;
      2, 3, 3, 4, 4, 3;
      4, 1, 0, 4, 3, 1;
      4, 4, 3, 1, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 6, 8, 9, 10} =
      !![0, 3, 2, 4, 4, 4;
      0, 2, 0, 1, 1, 0;
      0, 2, 3, 1, 3, 3;
      0, 2, 3, 4, 4, 3;
      4, 2, 3, 1, 4, 0;
      3, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1866 : Certificate {1, 3, 6, 8, 9, 10} := by
  refine ⟨!![2, 1, 0, 4, 0, 0;
      3, 1, 4, 1, 3, 4;
      3, 4, 4, 4, 1, 2;
      1, 2, 1, 0, 3, 4;
      3, 2, 1, 3, 1, 3;
      2, 2, 4, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 6, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 0, 1, 1, 0;
      2, 2, 3, 1, 3, 3;
      4, 2, 3, 4, 4, 3;
      1, 2, 3, 1, 4, 0;
      0, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1868 : Certificate {2, 3, 6, 8, 9, 10} := by
  refine ⟨!![3, 3, 3, 0, 4, 1;
      4, 3, 2, 2, 2, 0;
      4, 4, 3, 3, 3, 0;
      4, 2, 3, 2, 4, 3;
      1, 2, 3, 0, 2, 2;
      0, 2, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 6, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 3, 2, 4, 4, 4;
      1, 2, 3, 1, 3, 3;
      0, 2, 3, 4, 4, 3;
      4, 2, 3, 1, 4, 0;
      2, 2, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1873 : Certificate {0, 4, 6, 8, 9, 10} := by
  refine ⟨!![3, 2, 3, 1, 3, 3;
      0, 0, 3, 2, 0, 0;
      2, 1, 0, 4, 0, 0;
      1, 0, 4, 2, 2, 4;
      4, 1, 3, 1, 3, 1;
      3, 1, 4, 4, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 6, 8, 9, 10} =
      !![0, 2, 2, 4, 4, 4;
      0, 1, 0, 1, 1, 0;
      0, 2, 3, 4, 4, 3;
      0, 0, 3, 4, 4, 3;
      4, 4, 3, 1, 4, 0;
      3, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1874 : Certificate {1, 4, 6, 8, 9, 10} := by
  refine ⟨!![3, 4, 3, 3, 0, 0;
      4, 2, 2, 1, 0, 0;
      4, 0, 2, 4, 3, 3;
      0, 1, 3, 0, 1, 3;
      1, 3, 0, 4, 4, 2;
      4, 1, 0, 2, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 6, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 1, 0, 1, 1, 0;
      3, 2, 3, 4, 4, 3;
      4, 0, 3, 4, 4, 3;
      1, 4, 3, 1, 4, 0;
      0, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1876 : Certificate {2, 4, 6, 8, 9, 10} := by
  refine ⟨!![1, 3, 4, 2, 3, 3;
      4, 2, 4, 0, 2, 2;
      2, 4, 4, 0, 2, 2;
      1, 4, 3, 4, 0, 2;
      2, 1, 2, 2, 0, 3;
      4, 1, 1, 4, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 6, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 2, 4, 4, 4;
      2, 2, 3, 4, 4, 3;
      0, 0, 3, 4, 4, 3;
      4, 4, 3, 1, 4, 0;
      2, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1880 : Certificate {3, 4, 6, 8, 9, 10} := by
  refine ⟨!![4, 1, 1, 1, 1, 1;
      2, 0, 1, 4, 0, 0;
      1, 1, 0, 3, 4, 4;
      3, 4, 1, 1, 0, 2;
      2, 4, 2, 3, 3, 1;
      3, 1, 2, 3, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 6, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 2, 2, 4, 4, 4;
      2, 1, 0, 1, 1, 0;
      2, 0, 3, 4, 4, 3;
      2, 4, 3, 1, 4, 0;
      2, 3, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1889 : Certificate {0, 5, 6, 8, 9, 10} := by
  refine ⟨!![3, 2, 4, 0, 3, 3;
      3, 4, 4, 4, 1, 2;
      4, 2, 0, 1, 4, 3;
      2, 3, 4, 3, 4, 3;
      3, 3, 1, 2, 1, 2;
      4, 4, 1, 3, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 6, 8, 9, 10} =
      !![0, 4, 2, 4, 4, 4;
      0, 0, 0, 1, 1, 0;
      0, 2, 3, 4, 4, 3;
      0, 0, 3, 1, 3, 3;
      4, 4, 3, 1, 4, 0;
      3, 1, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1890 : Certificate {1, 5, 6, 8, 9, 10} := by
  refine ⟨!![3, 0, 1, 2, 4, 2;
      2, 2, 4, 2, 4, 2;
      2, 1, 2, 4, 1, 2;
      4, 0, 1, 4, 4, 2;
      1, 1, 4, 1, 1, 3;
      2, 3, 3, 1, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 6, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 0, 0, 1, 1, 0;
      3, 2, 3, 4, 4, 3;
      2, 0, 3, 1, 3, 3;
      1, 4, 3, 1, 4, 0;
      0, 1, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1892 : Certificate {2, 5, 6, 8, 9, 10} := by
  refine ⟨!![2, 0, 4, 3, 1, 3;
      4, 2, 4, 0, 2, 2;
      1, 1, 3, 0, 4, 4;
      2, 0, 2, 1, 3, 4;
      4, 1, 3, 3, 1, 1;
      2, 3, 2, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 6, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 4, 2, 4, 4, 4;
      2, 2, 3, 4, 4, 3;
      1, 0, 3, 1, 3, 3;
      4, 4, 3, 1, 4, 0;
      2, 1, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1896 : Certificate {3, 5, 6, 8, 9, 10} := by
  refine ⟨!![3, 3, 2, 2, 2, 0;
      2, 2, 0, 2, 1, 4;
      4, 3, 3, 2, 0, 3;
      4, 3, 2, 4, 2, 0;
      0, 1, 0, 2, 4, 0;
      1, 3, 0, 2, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 6, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 4, 2, 4, 4, 4;
      2, 0, 0, 1, 1, 0;
      2, 0, 3, 1, 3, 3;
      2, 4, 3, 1, 4, 0;
      2, 1, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1904 : Certificate {4, 5, 6, 8, 9, 10} := by
  refine ⟨!![0, 4, 1, 2, 4, 4;
      4, 3, 4, 2, 3, 3;
      1, 2, 4, 1, 0, 0;
      3, 1, 4, 2, 2, 4;
      2, 0, 1, 1, 4, 2;
      3, 2, 1, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 6, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      2, 4, 2, 4, 4, 4;
      1, 0, 0, 1, 1, 0;
      2, 2, 3, 4, 4, 3;
      4, 4, 3, 1, 4, 0;
      3, 1, 1, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1923 : Certificate {0, 1, 7, 8, 9, 10} := by
  refine ⟨!![0, 3, 4, 3, 3, 3;
      1, 2, 3, 4, 4, 3;
      2, 1, 1, 1, 3, 1;
      0, 0, 1, 1, 2, 4;
      3, 1, 0, 0, 1, 2;
      2, 3, 0, 4, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 7, 8, 9, 10} =
      !![0, 0, 4, 1, 1, 0;
      0, 3, 2, 4, 4, 3;
      0, 2, 4, 1, 3, 3;
      0, 4, 4, 4, 4, 3;
      4, 2, 3, 0, 2, 3;
      3, 0, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1925 : Certificate {0, 2, 7, 8, 9, 10} := by
  refine ⟨!![2, 2, 1, 2, 4, 0;
      3, 1, 3, 1, 4, 3;
      3, 3, 3, 4, 4, 3;
      3, 1, 4, 2, 1, 2;
      4, 3, 0, 1, 1, 2;
      0, 4, 4, 1, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 7, 8, 9, 10} =
      !![0, 0, 1, 4, 4, 4;
      0, 2, 2, 4, 4, 3;
      0, 1, 4, 1, 3, 3;
      0, 0, 4, 4, 4, 3;
      4, 0, 3, 0, 2, 3;
      3, 2, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1926 : Certificate {1, 2, 7, 8, 9, 10} := by
  refine ⟨!![2, 2, 2, 1, 1, 2;
      0, 3, 4, 3, 3, 3;
      4, 4, 3, 3, 0, 2;
      0, 3, 0, 4, 0, 2;
      1, 0, 4, 0, 1, 3;
      4, 3, 3, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 7, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 2, 2, 4, 4, 3;
      2, 1, 4, 1, 3, 3;
      4, 0, 4, 4, 4, 3;
      2, 0, 3, 0, 2, 3;
      0, 2, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1929 : Certificate {0, 3, 7, 8, 9, 10} := by
  refine ⟨!![2, 4, 3, 3, 0, 2;
      1, 4, 3, 3, 4, 3;
      3, 1, 1, 3, 3, 1;
      2, 3, 2, 2, 0, 0;
      4, 1, 3, 0, 0, 0;
      4, 4, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 7, 8, 9, 10} =
      !![0, 3, 1, 4, 4, 4;
      0, 2, 4, 1, 1, 0;
      0, 2, 4, 1, 3, 3;
      0, 2, 4, 4, 4, 3;
      4, 3, 3, 0, 2, 3;
      3, 2, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1930 : Certificate {1, 3, 7, 8, 9, 10} := by
  refine ⟨!![1, 3, 4, 3, 3, 3;
      3, 1, 1, 3, 3, 1;
      2, 1, 2, 2, 4, 4;
      1, 2, 3, 2, 3, 1;
      0, 3, 2, 4, 0, 1;
      1, 4, 3, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 7, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 4, 1, 1, 0;
      2, 2, 4, 1, 3, 3;
      4, 2, 4, 4, 4, 3;
      2, 3, 3, 0, 2, 3;
      0, 2, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1932 : Certificate {2, 3, 7, 8, 9, 10} := by
  refine ⟨!![1, 1, 3, 2, 3, 4;
      3, 2, 4, 1, 3, 3;
      0, 0, 4, 1, 3, 3;
      2, 0, 2, 0, 1, 4;
      0, 1, 1, 3, 0, 2;
      2, 4, 3, 1, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 7, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 3, 1, 4, 4, 4;
      1, 2, 4, 1, 3, 3;
      0, 2, 4, 4, 4, 3;
      0, 3, 3, 0, 2, 3;
      2, 2, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1937 : Certificate {0, 4, 7, 8, 9, 10} := by
  refine ⟨!![4, 4, 4, 2, 1, 4;
      1, 3, 3, 4, 0, 0;
      1, 3, 0, 2, 0, 0;
      4, 0, 3, 4, 4, 3;
      1, 1, 4, 4, 1, 2;
      2, 3, 4, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 7, 8, 9, 10} =
      !![0, 2, 1, 4, 4, 4;
      0, 1, 4, 1, 1, 0;
      0, 2, 2, 4, 4, 3;
      0, 0, 4, 4, 4, 3;
      4, 3, 3, 0, 2, 3;
      3, 3, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1938 : Certificate {1, 4, 7, 8, 9, 10} := by
  refine ⟨!![3, 2, 4, 4, 4, 1;
      4, 3, 4, 3, 3, 2;
      0, 2, 4, 4, 1, 4;
      2, 4, 0, 3, 4, 3;
      4, 1, 0, 3, 4, 4;
      3, 3, 1, 0, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 7, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 1, 4, 1, 1, 0;
      3, 2, 2, 4, 4, 3;
      4, 0, 4, 4, 4, 3;
      2, 3, 3, 0, 2, 3;
      0, 3, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1940 : Certificate {2, 4, 7, 8, 9, 10} := by
  refine ⟨!![4, 4, 1, 4, 3, 2;
      4, 2, 1, 4, 1, 4;
      3, 1, 4, 1, 4, 1;
      2, 1, 1, 1, 3, 4;
      3, 3, 0, 4, 3, 0;
      1, 0, 0, 4, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 7, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 1, 4, 4, 4;
      2, 2, 2, 4, 4, 3;
      0, 0, 4, 4, 4, 3;
      0, 3, 3, 0, 2, 3;
      2, 3, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1944 : Certificate {3, 4, 7, 8, 9, 10} := by
  refine ⟨!![3, 1, 3, 2, 3, 2;
      4, 1, 4, 1, 2, 3;
      1, 3, 4, 1, 1, 4;
      1, 3, 3, 4, 3, 4;
      0, 2, 2, 2, 0, 3;
      2, 2, 1, 3, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 7, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 2, 1, 4, 4, 4;
      2, 1, 4, 1, 1, 0;
      2, 0, 4, 4, 4, 3;
      3, 3, 3, 0, 2, 3;
      2, 3, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1953 : Certificate {0, 5, 7, 8, 9, 10} := by
  refine ⟨!![0, 3, 4, 3, 0, 2;
      1, 2, 1, 2, 1, 2;
      4, 1, 2, 2, 1, 2;
      1, 3, 3, 1, 2, 4;
      3, 4, 4, 1, 4, 3;
      3, 2, 4, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 7, 8, 9, 10} =
      !![0, 4, 1, 4, 4, 4;
      0, 0, 4, 1, 1, 0;
      0, 2, 2, 4, 4, 3;
      0, 0, 4, 1, 3, 3;
      4, 3, 3, 0, 2, 3;
      3, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1954 : Certificate {1, 5, 7, 8, 9, 10} := by
  refine ⟨!![0, 1, 3, 1, 0, 4;
      4, 3, 1, 1, 0, 4;
      1, 4, 4, 2, 2, 1;
      4, 3, 0, 4, 1, 2;
      2, 2, 4, 3, 1, 4;
      2, 1, 2, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 7, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 0, 4, 1, 1, 0;
      3, 2, 2, 4, 4, 3;
      2, 0, 4, 1, 3, 3;
      2, 3, 3, 0, 2, 3;
      0, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1956 : Certificate {2, 5, 7, 8, 9, 10} := by
  refine ⟨!![3, 3, 4, 1, 3, 1;
      1, 2, 3, 2, 2, 1;
      0, 4, 4, 1, 1, 3;
      0, 1, 4, 3, 2, 2;
      0, 3, 2, 2, 4, 2;
      4, 2, 0, 4, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 7, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 4, 1, 4, 4, 4;
      2, 2, 2, 4, 4, 3;
      1, 0, 4, 1, 3, 3;
      0, 3, 3, 0, 2, 3;
      2, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1960 : Certificate {3, 5, 7, 8, 9, 10} := by
  refine ⟨!![3, 3, 2, 3, 3, 4;
      3, 4, 2, 3, 4, 3;
      4, 3, 3, 2, 0, 3;
      1, 2, 1, 1, 3, 3;
      2, 0, 4, 0, 1, 2;
      2, 0, 2, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 7, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 4, 1, 4, 4, 4;
      2, 0, 4, 1, 1, 0;
      2, 0, 4, 1, 3, 3;
      3, 3, 3, 0, 2, 3;
      2, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1968 : Certificate {4, 5, 7, 8, 9, 10} := by
  refine ⟨!![4, 4, 2, 3, 4, 1;
      2, 3, 1, 4, 3, 2;
      4, 3, 1, 4, 0, 0;
      0, 1, 2, 0, 2, 0;
      0, 3, 3, 1, 4, 4;
      0, 3, 4, 0, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 7, 8, 9, 10} =
      !![0, 0, 4, 4, 4, 4;
      2, 4, 1, 4, 4, 4;
      1, 0, 4, 1, 1, 0;
      2, 2, 2, 4, 4, 3;
      3, 3, 3, 0, 2, 3;
      3, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1985 : Certificate {0, 6, 7, 8, 9, 10} := by
  refine ⟨!![4, 0, 1, 3, 1, 2;
      2, 1, 1, 0, 3, 0;
      0, 0, 2, 0, 3, 0;
      0, 2, 4, 2, 4, 0;
      0, 4, 3, 3, 4, 0;
      3, 1, 2, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 6, 7, 8, 9, 10} =
      !![0, 2, 1, 4, 4, 4;
      0, 0, 4, 1, 1, 0;
      0, 3, 2, 4, 4, 3;
      0, 3, 4, 1, 3, 3;
      0, 3, 4, 4, 4, 3;
      3, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1986 : Certificate {1, 6, 7, 8, 9, 10} := by
  refine ⟨!![1, 3, 2, 0, 0, 0;
      4, 3, 1, 1, 0, 4;
      2, 1, 1, 0, 3, 0;
      3, 1, 0, 2, 4, 0;
      4, 1, 1, 3, 4, 0;
      1, 4, 2, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 6, 7, 8, 9, 10} =
      !![0, 4, 4, 4, 4, 4;
      0, 0, 4, 1, 1, 0;
      3, 3, 2, 4, 4, 3;
      2, 3, 4, 1, 3, 3;
      4, 3, 4, 4, 4, 3;
      0, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1988 : Certificate {2, 6, 7, 8, 9, 10} := by
  refine ⟨!![0, 1, 4, 2, 4, 3;
      3, 3, 1, 2, 2, 3;
      0, 1, 1, 2, 2, 3;
      1, 1, 0, 4, 3, 3;
      2, 3, 4, 4, 1, 4;
      3, 2, 4, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 6, 7, 8, 9, 10} =
      !![0, 4, 4, 4, 4, 4;
      0, 2, 1, 4, 4, 4;
      2, 3, 2, 4, 4, 3;
      1, 3, 4, 1, 3, 3;
      0, 3, 4, 4, 4, 3;
      2, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1992 : Certificate {3, 6, 7, 8, 9, 10} := by
  refine ⟨!![2, 4, 1, 3, 1, 2;
      0, 3, 1, 2, 2, 3;
      4, 0, 2, 0, 3, 0;
      0, 4, 2, 0, 0, 2;
      0, 3, 4, 4, 1, 4;
      0, 0, 1, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 6, 7, 8, 9, 10} =
      !![0, 4, 4, 4, 4, 4;
      3, 2, 1, 4, 4, 4;
      2, 0, 4, 1, 1, 0;
      2, 3, 4, 1, 3, 3;
      2, 3, 4, 4, 4, 3;
      2, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2000 : Certificate {4, 6, 7, 8, 9, 10} := by
  refine ⟨!![3, 0, 4, 1, 0, 0;
      4, 2, 3, 4, 3, 0;
      3, 0, 4, 3, 3, 0;
      2, 4, 3, 4, 0, 2;
      3, 1, 3, 3, 3, 3;
      2, 3, 2, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 6, 7, 8, 9, 10} =
      !![0, 4, 4, 4, 4, 4;
      2, 2, 1, 4, 4, 4;
      1, 0, 4, 1, 1, 0;
      2, 3, 2, 4, 4, 3;
      0, 3, 4, 4, 4, 3;
      3, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2016 : Certificate {5, 6, 7, 8, 9, 10} := by
  refine ⟨!![4, 0, 2, 3, 0, 0;
      0, 0, 1, 3, 1, 4;
      4, 3, 2, 2, 1, 4;
      3, 4, 1, 1, 0, 2;
      1, 4, 2, 1, 1, 2;
      1, 4, 4, 3, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {5, 6, 7, 8, 9, 10} =
      !![0, 4, 4, 4, 4, 4;
      4, 2, 1, 4, 4, 4;
      0, 0, 4, 1, 1, 0;
      2, 3, 2, 4, 4, 3;
      0, 3, 4, 1, 3, 3;
      1, 1, 4, 4, 1, 2] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 1876 then
    if mask < 1834 then
      if mask < 1817 then
        if mask < 1806 then
          if mask < 1803 then
            ⟨{0, 1, 2, 8, 9, 10}, certificate_1799⟩
          else
            if mask < 1805 then
              ⟨{0, 1, 3, 8, 9, 10}, certificate_1803⟩
            else
              ⟨{0, 2, 3, 8, 9, 10}, certificate_1805⟩
        else
          if mask < 1813 then
            if mask < 1811 then
              ⟨{1, 2, 3, 8, 9, 10}, certificate_1806⟩
            else
              ⟨{0, 1, 4, 8, 9, 10}, certificate_1811⟩
          else
            if mask < 1814 then
              ⟨{0, 2, 4, 8, 9, 10}, certificate_1813⟩
            else
              ⟨{1, 2, 4, 8, 9, 10}, certificate_1814⟩
      else
        if mask < 1827 then
          if mask < 1818 then
            ⟨{0, 3, 4, 8, 9, 10}, certificate_1817⟩
          else
            if mask < 1820 then
              ⟨{1, 3, 4, 8, 9, 10}, certificate_1818⟩
            else
              ⟨{2, 3, 4, 8, 9, 10}, certificate_1820⟩
        else
          if mask < 1830 then
            if mask < 1829 then
              ⟨{0, 1, 5, 8, 9, 10}, certificate_1827⟩
            else
              ⟨{0, 2, 5, 8, 9, 10}, certificate_1829⟩
          else
            if mask < 1833 then
              ⟨{1, 2, 5, 8, 9, 10}, certificate_1830⟩
            else
              ⟨{0, 3, 5, 8, 9, 10}, certificate_1833⟩
    else
      if mask < 1861 then
        if mask < 1842 then
          if mask < 1836 then
            ⟨{1, 3, 5, 8, 9, 10}, certificate_1834⟩
          else
            if mask < 1841 then
              ⟨{2, 3, 5, 8, 9, 10}, certificate_1836⟩
            else
              ⟨{0, 4, 5, 8, 9, 10}, certificate_1841⟩
        else
          if mask < 1848 then
            if mask < 1844 then
              ⟨{1, 4, 5, 8, 9, 10}, certificate_1842⟩
            else
              ⟨{2, 4, 5, 8, 9, 10}, certificate_1844⟩
          else
            if mask < 1859 then
              ⟨{3, 4, 5, 8, 9, 10}, certificate_1848⟩
            else
              ⟨{0, 1, 6, 8, 9, 10}, certificate_1859⟩
      else
        if mask < 1866 then
          if mask < 1862 then
            ⟨{0, 2, 6, 8, 9, 10}, certificate_1861⟩
          else
            if mask < 1865 then
              ⟨{1, 2, 6, 8, 9, 10}, certificate_1862⟩
            else
              ⟨{0, 3, 6, 8, 9, 10}, certificate_1865⟩
        else
          if mask < 1873 then
            if mask < 1868 then
              ⟨{1, 3, 6, 8, 9, 10}, certificate_1866⟩
            else
              ⟨{2, 3, 6, 8, 9, 10}, certificate_1868⟩
          else
            if mask < 1874 then
              ⟨{0, 4, 6, 8, 9, 10}, certificate_1873⟩
            else
              ⟨{1, 4, 6, 8, 9, 10}, certificate_1874⟩
  else
    if mask < 1938 then
      if mask < 1923 then
        if mask < 1890 then
          if mask < 1880 then
            ⟨{2, 4, 6, 8, 9, 10}, certificate_1876⟩
          else
            if mask < 1889 then
              ⟨{3, 4, 6, 8, 9, 10}, certificate_1880⟩
            else
              ⟨{0, 5, 6, 8, 9, 10}, certificate_1889⟩
        else
          if mask < 1896 then
            if mask < 1892 then
              ⟨{1, 5, 6, 8, 9, 10}, certificate_1890⟩
            else
              ⟨{2, 5, 6, 8, 9, 10}, certificate_1892⟩
          else
            if mask < 1904 then
              ⟨{3, 5, 6, 8, 9, 10}, certificate_1896⟩
            else
              ⟨{4, 5, 6, 8, 9, 10}, certificate_1904⟩
      else
        if mask < 1929 then
          if mask < 1925 then
            ⟨{0, 1, 7, 8, 9, 10}, certificate_1923⟩
          else
            if mask < 1926 then
              ⟨{0, 2, 7, 8, 9, 10}, certificate_1925⟩
            else
              ⟨{1, 2, 7, 8, 9, 10}, certificate_1926⟩
        else
          if mask < 1932 then
            if mask < 1930 then
              ⟨{0, 3, 7, 8, 9, 10}, certificate_1929⟩
            else
              ⟨{1, 3, 7, 8, 9, 10}, certificate_1930⟩
          else
            if mask < 1937 then
              ⟨{2, 3, 7, 8, 9, 10}, certificate_1932⟩
            else
              ⟨{0, 4, 7, 8, 9, 10}, certificate_1937⟩
    else
      if mask < 1968 then
        if mask < 1953 then
          if mask < 1940 then
            ⟨{1, 4, 7, 8, 9, 10}, certificate_1938⟩
          else
            if mask < 1944 then
              ⟨{2, 4, 7, 8, 9, 10}, certificate_1940⟩
            else
              ⟨{3, 4, 7, 8, 9, 10}, certificate_1944⟩
        else
          if mask < 1956 then
            if mask < 1954 then
              ⟨{0, 5, 7, 8, 9, 10}, certificate_1953⟩
            else
              ⟨{1, 5, 7, 8, 9, 10}, certificate_1954⟩
          else
            if mask < 1960 then
              ⟨{2, 5, 7, 8, 9, 10}, certificate_1956⟩
            else
              ⟨{3, 5, 7, 8, 9, 10}, certificate_1960⟩
      else
        if mask < 1988 then
          if mask < 1985 then
            ⟨{4, 5, 7, 8, 9, 10}, certificate_1968⟩
          else
            if mask < 1986 then
              ⟨{0, 6, 7, 8, 9, 10}, certificate_1985⟩
            else
              ⟨{1, 6, 7, 8, 9, 10}, certificate_1986⟩
        else
          if mask < 2000 then
            if mask < 1992 then
              ⟨{2, 6, 7, 8, 9, 10}, certificate_1988⟩
            else
              ⟨{3, 6, 7, 8, 9, 10}, certificate_1992⟩
          else
            if mask < 2016 then
              ⟨{4, 6, 7, 8, 9, 10}, certificate_2000⟩
            else
              ⟨{5, 6, 7, 8, 9, 10}, certificate_2016⟩
end AMEProbe.QuinaryDirect.Batch07
#print axioms AMEProbe.QuinaryDirect.Batch07.lookup
