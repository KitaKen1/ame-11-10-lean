import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch15
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_3843 : Certificate {0, 1, 8, 9, 10, 11} := by
  refine ⟨!![4, 0, 1, 0, 4, 0;
      4, 0, 3, 1, 1, 4;
      1, 2, 0, 2, 1, 4;
      2, 1, 4, 3, 2, 3;
      1, 4, 3, 4, 1, 4;
      4, 1, 3, 0, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 8, 9, 10, 11} =
      !![0, 0, 1, 1, 0, 2;
      0, 3, 4, 4, 3, 2;
      0, 2, 1, 3, 3, 3;
      0, 4, 4, 4, 3, 1;
      4, 2, 0, 2, 3, 1;
      4, 1, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3845 : Certificate {0, 2, 8, 9, 10, 11} := by
  refine ⟨!![3, 1, 0, 3, 2, 2;
      1, 2, 4, 3, 3, 2;
      1, 4, 2, 1, 0, 0;
      4, 4, 1, 2, 1, 4;
      4, 2, 2, 2, 4, 1;
      3, 2, 2, 3, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 0;
      0, 2, 4, 4, 3, 2;
      0, 1, 1, 3, 3, 3;
      0, 0, 4, 4, 3, 1;
      4, 0, 0, 2, 3, 1;
      4, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3846 : Certificate {1, 2, 8, 9, 10, 11} := by
  refine ⟨!![3, 2, 2, 3, 4, 1;
      4, 1, 0, 1, 1, 1;
      1, 1, 1, 1, 4, 3;
      0, 1, 1, 3, 0, 3;
      3, 1, 4, 1, 2, 1;
      0, 1, 2, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 4, 4, 3, 2;
      2, 1, 1, 3, 3, 3;
      4, 0, 4, 4, 3, 1;
      2, 0, 0, 2, 3, 1;
      1, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3849 : Certificate {0, 3, 8, 9, 10, 11} := by
  refine ⟨!![0, 0, 3, 4, 3, 1;
      0, 2, 4, 3, 3, 2;
      4, 2, 3, 3, 2, 3;
      2, 2, 2, 4, 3, 2;
      3, 2, 2, 2, 4, 1;
      2, 4, 1, 1, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 8, 9, 10, 11} =
      !![0, 3, 4, 4, 4, 0;
      0, 2, 1, 1, 0, 2;
      0, 2, 1, 3, 3, 3;
      0, 2, 4, 4, 3, 1;
      4, 3, 0, 2, 3, 1;
      4, 2, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3850 : Certificate {1, 3, 8, 9, 10, 11} := by
  refine ⟨!![0, 0, 2, 1, 2, 4;
      0, 2, 3, 0, 2, 0;
      2, 0, 1, 0, 3, 2;
      1, 1, 0, 2, 0, 2;
      4, 3, 1, 0, 4, 0;
      1, 3, 4, 4, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 1, 1, 0, 2;
      2, 2, 1, 3, 3, 3;
      4, 2, 4, 4, 3, 1;
      2, 3, 0, 2, 3, 1;
      1, 2, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3852 : Certificate {2, 3, 8, 9, 10, 11} := by
  refine ⟨!![0, 0, 4, 2, 4, 3;
      2, 1, 3, 3, 0, 3;
      2, 0, 0, 2, 2, 0;
      2, 3, 4, 3, 3, 4;
      2, 4, 0, 4, 0, 0;
      4, 4, 3, 3, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 3, 4, 4, 4, 0;
      1, 2, 1, 3, 3, 3;
      0, 2, 4, 4, 3, 1;
      0, 3, 0, 2, 3, 1;
      4, 2, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3857 : Certificate {0, 4, 8, 9, 10, 11} := by
  refine ⟨!![0, 1, 0, 3, 2, 2;
      4, 2, 3, 0, 0, 0;
      4, 3, 0, 2, 1, 4;
      3, 4, 2, 0, 4, 1;
      0, 2, 4, 3, 0, 0;
      2, 1, 0, 4, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 8, 9, 10, 11} =
      !![0, 2, 4, 4, 4, 0;
      0, 1, 1, 1, 0, 2;
      0, 2, 4, 4, 3, 2;
      0, 0, 4, 4, 3, 1;
      4, 3, 0, 2, 3, 1;
      4, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3858 : Certificate {1, 4, 8, 9, 10, 11} := by
  refine ⟨!![0, 2, 0, 1, 4, 4;
      1, 0, 4, 4, 4, 4;
      1, 1, 1, 1, 0, 3;
      2, 1, 4, 1, 4, 1;
      0, 4, 4, 4, 4, 4;
      3, 2, 3, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 1, 1, 1, 0, 2;
      3, 2, 4, 4, 3, 2;
      4, 0, 4, 4, 3, 1;
      2, 3, 0, 2, 3, 1;
      1, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3860 : Certificate {2, 4, 8, 9, 10, 11} := by
  refine ⟨!![4, 4, 4, 0, 2, 2;
      0, 4, 3, 4, 1, 1;
      2, 1, 2, 3, 1, 4;
      1, 4, 3, 3, 4, 1;
      2, 2, 1, 2, 2, 2;
      2, 4, 2, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 4, 4, 4, 0;
      2, 2, 4, 4, 3, 2;
      0, 0, 4, 4, 3, 1;
      0, 3, 0, 2, 3, 1;
      4, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3864 : Certificate {3, 4, 8, 9, 10, 11} := by
  refine ⟨!![0, 0, 2, 1, 4, 4;
      2, 1, 3, 3, 3, 3;
      0, 4, 2, 4, 4, 2;
      3, 1, 4, 0, 3, 0;
      1, 1, 1, 0, 1, 1;
      0, 2, 4, 3, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 4, 4, 4, 0;
      2, 1, 1, 1, 0, 2;
      2, 0, 4, 4, 3, 1;
      3, 3, 0, 2, 3, 1;
      2, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3873 : Certificate {0, 5, 8, 9, 10, 11} := by
  refine ⟨!![1, 2, 2, 1, 4, 0;
      2, 1, 4, 0, 0, 0;
      0, 3, 2, 4, 4, 1;
      4, 2, 4, 0, 4, 1;
      3, 4, 0, 1, 2, 3;
      3, 3, 2, 3, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 0;
      0, 0, 1, 1, 0, 2;
      0, 2, 4, 4, 3, 2;
      0, 0, 1, 3, 3, 3;
      4, 3, 0, 2, 3, 1;
      4, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3874 : Certificate {1, 5, 8, 9, 10, 11} := by
  refine ⟨!![1, 4, 4, 3, 0, 3;
      0, 2, 0, 3, 2, 0;
      2, 1, 0, 0, 4, 2;
      3, 1, 3, 0, 3, 0;
      4, 4, 0, 0, 0, 0;
      0, 2, 1, 0, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 0, 1, 1, 0, 2;
      3, 2, 4, 4, 3, 2;
      2, 0, 1, 3, 3, 3;
      2, 3, 0, 2, 3, 1;
      1, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3876 : Certificate {2, 5, 8, 9, 10, 11} := by
  refine ⟨!![2, 1, 0, 2, 4, 1;
      4, 1, 3, 1, 1, 2;
      1, 4, 4, 1, 0, 4;
      1, 1, 2, 0, 2, 4;
      4, 3, 1, 3, 2, 0;
      4, 1, 4, 3, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 4, 4, 4, 4, 0;
      2, 2, 4, 4, 3, 2;
      1, 0, 1, 3, 3, 3;
      0, 3, 0, 2, 3, 1;
      4, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3880 : Certificate {3, 5, 8, 9, 10, 11} := by
  refine ⟨!![2, 1, 0, 2, 4, 1;
      3, 4, 2, 1, 3, 4;
      1, 2, 1, 4, 2, 4;
      4, 4, 3, 2, 4, 3;
      3, 2, 4, 4, 3, 2;
      3, 1, 1, 0, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 4, 4, 4, 4, 0;
      2, 0, 1, 1, 0, 2;
      2, 0, 1, 3, 3, 3;
      3, 3, 0, 2, 3, 1;
      2, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3888 : Certificate {4, 5, 8, 9, 10, 11} := by
  refine ⟨!![4, 3, 2, 2, 2, 2;
      3, 3, 0, 3, 4, 4;
      3, 2, 4, 3, 2, 0;
      4, 2, 4, 1, 1, 3;
      3, 3, 1, 2, 2, 2;
      2, 4, 3, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 8, 9, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      2, 4, 4, 4, 4, 0;
      1, 0, 1, 1, 0, 2;
      2, 2, 4, 4, 3, 2;
      3, 3, 0, 2, 3, 1;
      4, 4, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3905 : Certificate {0, 6, 8, 9, 10, 11} := by
  refine ⟨!![1, 1, 2, 4, 1, 4;
      2, 1, 4, 0, 0, 0;
      0, 2, 2, 2, 1, 0;
      0, 4, 1, 3, 1, 0;
      3, 1, 0, 0, 3, 0;
      0, 0, 1, 0, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 6, 8, 9, 10, 11} =
      !![0, 2, 4, 4, 4, 0;
      0, 0, 1, 1, 0, 2;
      0, 3, 4, 4, 3, 2;
      0, 3, 1, 3, 3, 3;
      0, 3, 4, 4, 3, 1;
      4, 3, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3906 : Certificate {1, 6, 8, 9, 10, 11} := by
  refine ⟨!![4, 2, 1, 0, 2, 0;
      3, 3, 2, 2, 2, 2;
      4, 4, 3, 2, 3, 0;
      3, 3, 3, 3, 0, 0;
      1, 1, 3, 3, 3, 3;
      4, 2, 2, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 6, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      0, 0, 1, 1, 0, 2;
      3, 3, 4, 4, 3, 2;
      2, 3, 1, 3, 3, 3;
      4, 3, 4, 4, 3, 1;
      1, 3, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3908 : Certificate {2, 6, 8, 9, 10, 11} := by
  refine ⟨!![1, 2, 3, 3, 0, 3;
      1, 3, 0, 4, 4, 4;
      2, 2, 4, 0, 4, 3;
      1, 3, 1, 0, 2, 2;
      4, 0, 0, 3, 2, 3;
      3, 1, 0, 4, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 6, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      0, 2, 4, 4, 4, 0;
      2, 3, 4, 4, 3, 2;
      1, 3, 1, 3, 3, 3;
      0, 3, 4, 4, 3, 1;
      4, 3, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3912 : Certificate {3, 6, 8, 9, 10, 11} := by
  refine ⟨!![1, 3, 1, 2, 1, 2;
      3, 4, 2, 3, 1, 3;
      3, 3, 4, 4, 3, 2;
      3, 1, 4, 2, 1, 4;
      3, 2, 4, 1, 1, 1;
      1, 0, 3, 0, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 6, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      3, 2, 4, 4, 4, 0;
      2, 0, 1, 1, 0, 2;
      2, 3, 1, 3, 3, 3;
      2, 3, 4, 4, 3, 1;
      2, 3, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3920 : Certificate {4, 6, 8, 9, 10, 11} := by
  refine ⟨!![1, 0, 3, 4, 3, 0;
      2, 2, 2, 2, 1, 0;
      3, 2, 3, 3, 2, 3;
      0, 3, 2, 2, 4, 2;
      3, 3, 0, 2, 2, 0;
      3, 0, 4, 3, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 6, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      2, 2, 4, 4, 4, 0;
      1, 0, 1, 1, 0, 2;
      2, 3, 4, 4, 3, 2;
      0, 3, 4, 4, 3, 1;
      4, 3, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3936 : Certificate {5, 6, 8, 9, 10, 11} := by
  refine ⟨!![1, 2, 0, 3, 3, 3;
      4, 0, 1, 1, 2, 2;
      0, 4, 1, 0, 3, 1;
      2, 3, 3, 0, 0, 2;
      0, 0, 3, 4, 3, 3;
      4, 4, 1, 0, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {5, 6, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      4, 2, 4, 4, 4, 0;
      0, 0, 1, 1, 0, 2;
      2, 3, 4, 4, 3, 2;
      0, 3, 1, 3, 3, 3;
      4, 3, 1, 4, 0, 4] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3969 : Certificate {0, 7, 8, 9, 10, 11} := by
  refine ⟨!![4, 1, 3, 1, 0, 4;
      3, 4, 1, 0, 0, 0;
      3, 1, 3, 2, 1, 0;
      3, 3, 2, 3, 1, 0;
      1, 0, 1, 0, 3, 0;
      1, 3, 3, 0, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 7, 8, 9, 10, 11} =
      !![0, 1, 4, 4, 4, 0;
      0, 4, 1, 1, 0, 2;
      0, 2, 4, 4, 3, 2;
      0, 4, 1, 3, 3, 3;
      0, 4, 4, 4, 3, 1;
      4, 3, 0, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3970 : Certificate {1, 7, 8, 9, 10, 11} := by
  refine ⟨!![4, 4, 1, 3, 2, 2;
      0, 2, 0, 3, 0, 2;
      4, 3, 3, 3, 3, 4;
      3, 4, 3, 2, 0, 1;
      4, 0, 0, 4, 0, 1;
      4, 3, 2, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 7, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      0, 4, 1, 1, 0, 2;
      3, 2, 4, 4, 3, 2;
      2, 4, 1, 3, 3, 3;
      4, 4, 4, 4, 3, 1;
      2, 3, 0, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3972 : Certificate {2, 7, 8, 9, 10, 11} := by
  refine ⟨!![2, 2, 2, 2, 1, 3;
      2, 4, 1, 3, 1, 2;
      3, 2, 3, 4, 0, 3;
      3, 4, 1, 3, 0, 0;
      1, 2, 2, 1, 1, 4;
      0, 4, 4, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 7, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      0, 1, 4, 4, 4, 0;
      2, 2, 4, 4, 3, 2;
      1, 4, 1, 3, 3, 3;
      0, 4, 4, 4, 3, 1;
      0, 3, 0, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3976 : Certificate {3, 7, 8, 9, 10, 11} := by
  refine ⟨!![3, 4, 4, 2, 4, 3;
      2, 1, 3, 1, 1, 4;
      3, 3, 4, 3, 0, 4;
      2, 3, 0, 2, 2, 1;
      1, 1, 1, 2, 1, 3;
      3, 1, 1, 1, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 7, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      3, 1, 4, 4, 4, 0;
      2, 4, 1, 1, 0, 2;
      2, 4, 1, 3, 3, 3;
      2, 4, 4, 4, 3, 1;
      3, 3, 0, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3984 : Certificate {4, 7, 8, 9, 10, 11} := by
  refine ⟨!![4, 3, 1, 2, 2, 0;
      2, 2, 2, 2, 1, 0;
      4, 3, 0, 4, 3, 2;
      2, 0, 3, 4, 2, 3;
      4, 4, 1, 3, 0, 0;
      1, 3, 2, 1, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 7, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      2, 1, 4, 4, 4, 0;
      1, 4, 1, 1, 0, 2;
      2, 2, 4, 4, 3, 2;
      0, 4, 4, 4, 3, 1;
      3, 3, 0, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_4000 : Certificate {5, 7, 8, 9, 10, 11} := by
  refine ⟨!![0, 1, 4, 2, 4, 1;
      0, 4, 3, 3, 4, 1;
      3, 4, 3, 2, 2, 0;
      3, 1, 3, 0, 1, 2;
      4, 2, 3, 4, 2, 3;
      2, 2, 4, 3, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {5, 7, 8, 9, 10, 11} =
      !![0, 4, 4, 4, 4, 3;
      4, 1, 4, 4, 4, 0;
      0, 4, 1, 1, 0, 2;
      2, 2, 4, 4, 3, 2;
      0, 4, 1, 3, 3, 3;
      3, 3, 0, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_4032 : Certificate {6, 7, 8, 9, 10, 11} := by
  refine ⟨!![1, 2, 4, 3, 0, 3;
      1, 0, 3, 4, 0, 3;
      1, 0, 0, 1, 2, 4;
      1, 0, 2, 0, 3, 4;
      1, 3, 4, 4, 0, 1;
      2, 0, 1, 4, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {6, 7, 8, 9, 10, 11} =
      !![4, 4, 4, 4, 4, 3;
      2, 1, 4, 4, 4, 0;
      0, 4, 1, 1, 0, 2;
      3, 2, 4, 4, 3, 2;
      3, 4, 1, 3, 3, 3;
      3, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 3888 then
    if mask < 3858 then
      if mask < 3849 then
        if mask < 3845 then
          ⟨{0, 1, 8, 9, 10, 11}, certificate_3843⟩
        else
          if mask < 3846 then
            ⟨{0, 2, 8, 9, 10, 11}, certificate_3845⟩
          else
            ⟨{1, 2, 8, 9, 10, 11}, certificate_3846⟩
      else
        if mask < 3852 then
          if mask < 3850 then
            ⟨{0, 3, 8, 9, 10, 11}, certificate_3849⟩
          else
            ⟨{1, 3, 8, 9, 10, 11}, certificate_3850⟩
        else
          if mask < 3857 then
            ⟨{2, 3, 8, 9, 10, 11}, certificate_3852⟩
          else
            ⟨{0, 4, 8, 9, 10, 11}, certificate_3857⟩
    else
      if mask < 3873 then
        if mask < 3860 then
          ⟨{1, 4, 8, 9, 10, 11}, certificate_3858⟩
        else
          if mask < 3864 then
            ⟨{2, 4, 8, 9, 10, 11}, certificate_3860⟩
          else
            ⟨{3, 4, 8, 9, 10, 11}, certificate_3864⟩
      else
        if mask < 3876 then
          if mask < 3874 then
            ⟨{0, 5, 8, 9, 10, 11}, certificate_3873⟩
          else
            ⟨{1, 5, 8, 9, 10, 11}, certificate_3874⟩
        else
          if mask < 3880 then
            ⟨{2, 5, 8, 9, 10, 11}, certificate_3876⟩
          else
            ⟨{3, 5, 8, 9, 10, 11}, certificate_3880⟩
  else
    if mask < 3969 then
      if mask < 3908 then
        if mask < 3905 then
          ⟨{4, 5, 8, 9, 10, 11}, certificate_3888⟩
        else
          if mask < 3906 then
            ⟨{0, 6, 8, 9, 10, 11}, certificate_3905⟩
          else
            ⟨{1, 6, 8, 9, 10, 11}, certificate_3906⟩
      else
        if mask < 3920 then
          if mask < 3912 then
            ⟨{2, 6, 8, 9, 10, 11}, certificate_3908⟩
          else
            ⟨{3, 6, 8, 9, 10, 11}, certificate_3912⟩
        else
          if mask < 3936 then
            ⟨{4, 6, 8, 9, 10, 11}, certificate_3920⟩
          else
            ⟨{5, 6, 8, 9, 10, 11}, certificate_3936⟩
    else
      if mask < 3976 then
        if mask < 3970 then
          ⟨{0, 7, 8, 9, 10, 11}, certificate_3969⟩
        else
          if mask < 3972 then
            ⟨{1, 7, 8, 9, 10, 11}, certificate_3970⟩
          else
            ⟨{2, 7, 8, 9, 10, 11}, certificate_3972⟩
      else
        if mask < 4000 then
          if mask < 3984 then
            ⟨{3, 7, 8, 9, 10, 11}, certificate_3976⟩
          else
            ⟨{4, 7, 8, 9, 10, 11}, certificate_3984⟩
        else
          if mask < 4032 then
            ⟨{5, 7, 8, 9, 10, 11}, certificate_4000⟩
          else
            ⟨{6, 7, 8, 9, 10, 11}, certificate_4032⟩
end AMEProbe.QuinaryDirect.Batch15
#print axioms AMEProbe.QuinaryDirect.Batch15.lookup
