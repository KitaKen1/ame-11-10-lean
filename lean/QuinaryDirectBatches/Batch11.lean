import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch11
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_2823 : Certificate {0, 1, 2, 8, 9, 11} := by
  refine ⟨!![0, 2, 1, 4, 2, 3;
      1, 2, 4, 0, 4, 1;
      3, 4, 1, 2, 4, 4;
      4, 0, 0, 4, 3, 3;
      1, 2, 1, 2, 4, 4;
      1, 4, 1, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 8, 9, 11} =
      !![0, 3, 2, 4, 4, 2;
      0, 2, 1, 1, 3, 3;
      0, 4, 0, 4, 4, 1;
      4, 2, 0, 0, 2, 1;
      4, 1, 4, 1, 4, 4;
      4, 4, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2827 : Certificate {0, 1, 3, 8, 9, 11} := by
  refine ⟨!![1, 3, 2, 4, 4, 1;
      1, 0, 3, 1, 3, 1;
      4, 4, 4, 0, 3, 2;
      4, 2, 1, 3, 4, 3;
      0, 4, 4, 3, 1, 1;
      2, 3, 1, 2, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 8, 9, 11} =
      !![0, 0, 2, 1, 1, 2;
      0, 2, 2, 1, 3, 3;
      0, 4, 2, 4, 4, 1;
      4, 2, 3, 0, 2, 1;
      4, 1, 2, 1, 4, 4;
      4, 4, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2829 : Certificate {0, 2, 3, 8, 9, 11} := by
  refine ⟨!![2, 1, 3, 1, 1, 2;
      4, 1, 3, 1, 0, 4;
      3, 1, 3, 3, 1, 1;
      0, 2, 4, 4, 2, 4;
      3, 1, 0, 0, 1, 4;
      2, 1, 4, 3, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 8, 9, 11} =
      !![0, 0, 3, 4, 4, 0;
      0, 1, 2, 1, 3, 3;
      0, 0, 2, 4, 4, 1;
      4, 0, 3, 0, 2, 1;
      4, 4, 2, 1, 4, 4;
      4, 0, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2830 : Certificate {1, 2, 3, 8, 9, 11} := by
  refine ⟨!![2, 3, 3, 3, 3, 1;
      1, 3, 1, 3, 2, 3;
      0, 2, 1, 4, 2, 3;
      3, 4, 1, 1, 4, 3;
      2, 0, 1, 4, 0, 2;
      2, 3, 4, 0, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 8, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      2, 1, 2, 1, 3, 3;
      4, 0, 2, 4, 4, 1;
      2, 0, 3, 0, 2, 1;
      1, 4, 2, 1, 4, 4;
      4, 0, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2835 : Certificate {0, 1, 4, 8, 9, 11} := by
  refine ⟨!![2, 2, 2, 2, 2, 0;
      3, 1, 2, 0, 0, 0;
      2, 1, 4, 4, 2, 4;
      3, 3, 1, 0, 1, 4;
      3, 1, 4, 2, 0, 3;
      4, 0, 3, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 8, 9, 11} =
      !![0, 0, 1, 1, 1, 2;
      0, 3, 2, 4, 4, 2;
      0, 4, 0, 4, 4, 1;
      4, 2, 3, 0, 2, 1;
      4, 1, 4, 1, 4, 4;
      4, 4, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2837 : Certificate {0, 2, 4, 8, 9, 11} := by
  refine ⟨!![4, 0, 0, 3, 0, 1;
      4, 2, 1, 1, 3, 1;
      2, 3, 4, 2, 1, 2;
      3, 1, 1, 2, 2, 1;
      0, 0, 2, 2, 0, 3;
      3, 1, 4, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 8, 9, 11} =
      !![0, 0, 2, 4, 4, 0;
      0, 2, 2, 4, 4, 2;
      0, 0, 0, 4, 4, 1;
      4, 0, 3, 0, 2, 1;
      4, 4, 4, 1, 4, 4;
      4, 0, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2838 : Certificate {1, 2, 4, 8, 9, 11} := by
  refine ⟨!![1, 3, 1, 4, 1, 1;
      1, 0, 2, 2, 4, 1;
      2, 4, 1, 1, 3, 1;
      3, 0, 4, 3, 0, 2;
      1, 3, 3, 1, 1, 4;
      0, 1, 4, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 8, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 4, 4, 2;
      4, 0, 0, 4, 4, 1;
      2, 0, 3, 0, 2, 1;
      1, 4, 4, 1, 4, 4;
      4, 0, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2841 : Certificate {0, 3, 4, 8, 9, 11} := by
  refine ⟨!![3, 4, 2, 4, 3, 2;
      4, 4, 2, 1, 3, 1;
      0, 4, 2, 4, 2, 4;
      2, 1, 1, 3, 0, 2;
      4, 4, 4, 3, 3, 4;
      3, 2, 2, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 8, 9, 11} =
      !![0, 3, 2, 4, 4, 0;
      0, 2, 1, 1, 1, 2;
      0, 2, 0, 4, 4, 1;
      4, 3, 3, 0, 2, 1;
      4, 2, 4, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2842 : Certificate {1, 3, 4, 8, 9, 11} := by
  refine ⟨!![4, 2, 4, 2, 0, 4;
      1, 0, 2, 2, 4, 1;
      4, 1, 1, 1, 2, 3;
      0, 0, 3, 2, 3, 4;
      0, 2, 3, 1, 4, 3;
      2, 4, 2, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 8, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 1, 1, 1, 2;
      4, 2, 0, 4, 4, 1;
      2, 3, 3, 0, 2, 1;
      1, 2, 4, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2844 : Certificate {2, 3, 4, 8, 9, 11} := by
  refine ⟨!![1, 4, 2, 0, 4, 2;
      0, 1, 0, 2, 0, 4;
      4, 3, 3, 0, 0, 0;
      3, 2, 4, 2, 0, 0;
      0, 1, 2, 4, 0, 2;
      3, 1, 2, 2, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 8, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 2, 4, 4, 0;
      0, 2, 0, 4, 4, 1;
      0, 3, 3, 0, 2, 1;
      4, 2, 4, 1, 4, 4;
      0, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2851 : Certificate {0, 1, 5, 8, 9, 11} := by
  refine ⟨!![3, 3, 4, 1, 2, 1;
      2, 3, 0, 3, 4, 3;
      3, 1, 1, 4, 4, 2;
      2, 3, 4, 0, 4, 1;
      2, 2, 2, 1, 1, 3;
      1, 0, 2, 2, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 8, 9, 11} =
      !![0, 0, 0, 1, 1, 2;
      0, 3, 2, 4, 4, 2;
      0, 2, 0, 1, 3, 3;
      4, 2, 3, 0, 2, 1;
      4, 1, 4, 1, 4, 4;
      4, 4, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2853 : Certificate {0, 2, 5, 8, 9, 11} := by
  refine ⟨!![0, 1, 4, 4, 1, 4;
      2, 1, 4, 4, 0, 1;
      3, 3, 2, 3, 3, 4;
      2, 1, 3, 1, 0, 4;
      4, 1, 0, 1, 2, 2;
      3, 0, 3, 4, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 0;
      0, 2, 2, 4, 4, 2;
      0, 1, 0, 1, 3, 3;
      4, 0, 3, 0, 2, 1;
      4, 4, 4, 1, 4, 4;
      4, 0, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2854 : Certificate {1, 2, 5, 8, 9, 11} := by
  refine ⟨!![0, 1, 4, 4, 1, 4;
      4, 1, 3, 2, 4, 2;
      1, 2, 4, 1, 3, 4;
      4, 2, 1, 3, 0, 4;
      3, 2, 2, 1, 1, 3;
      1, 3, 1, 3, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 8, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 4, 4, 2;
      2, 1, 0, 1, 3, 3;
      2, 0, 3, 0, 2, 1;
      1, 4, 4, 1, 4, 4;
      4, 0, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2857 : Certificate {0, 3, 5, 8, 9, 11} := by
  refine ⟨!![3, 0, 0, 0, 1, 3;
      3, 4, 1, 2, 3, 0;
      3, 3, 2, 0, 4, 1;
      1, 3, 1, 1, 1, 3;
      4, 1, 0, 0, 4, 1;
      2, 2, 1, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 8, 9, 11} =
      !![0, 3, 4, 4, 4, 0;
      0, 2, 0, 1, 1, 2;
      0, 2, 0, 1, 3, 3;
      4, 3, 3, 0, 2, 1;
      4, 2, 4, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2858 : Certificate {1, 3, 5, 8, 9, 11} := by
  refine ⟨!![2, 1, 1, 2, 2, 2;
      3, 3, 0, 0, 0, 0;
      2, 4, 3, 2, 0, 0;
      3, 2, 0, 4, 2, 0;
      2, 2, 1, 2, 3, 4;
      2, 3, 2, 2, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 8, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 0, 1, 1, 2;
      2, 2, 0, 1, 3, 3;
      2, 3, 3, 0, 2, 1;
      1, 2, 4, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2860 : Certificate {2, 3, 5, 8, 9, 11} := by
  refine ⟨!![0, 2, 0, 0, 4, 2;
      2, 4, 2, 4, 2, 3;
      4, 1, 4, 4, 4, 3;
      4, 0, 3, 0, 3, 1;
      3, 0, 4, 3, 4, 0;
      1, 0, 4, 1, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 8, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 4, 4, 4, 0;
      1, 2, 0, 1, 3, 3;
      0, 3, 3, 0, 2, 1;
      4, 2, 4, 1, 4, 4;
      0, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2865 : Certificate {0, 4, 5, 8, 9, 11} := by
  refine ⟨!![3, 1, 4, 4, 3, 2;
      0, 1, 4, 4, 2, 4;
      2, 3, 2, 3, 4, 3;
      3, 1, 3, 2, 2, 1;
      4, 3, 3, 3, 3, 4;
      4, 3, 0, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 8, 9, 11} =
      !![0, 2, 4, 4, 4, 0;
      0, 1, 0, 1, 1, 2;
      0, 2, 2, 4, 4, 2;
      4, 3, 3, 0, 2, 1;
      4, 4, 4, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2866 : Certificate {1, 4, 5, 8, 9, 11} := by
  refine ⟨!![3, 0, 3, 3, 4, 3;
      1, 1, 0, 0, 0, 0;
      3, 4, 4, 0, 1, 3;
      1, 0, 0, 4, 2, 0;
      2, 0, 3, 3, 0, 0;
      3, 0, 1, 4, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 8, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 1, 0, 1, 1, 2;
      3, 2, 2, 4, 4, 2;
      2, 3, 3, 0, 2, 1;
      1, 4, 4, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2868 : Certificate {2, 4, 5, 8, 9, 11} := by
  refine ⟨!![4, 0, 4, 4, 2, 4;
      1, 2, 1, 1, 2, 3;
      0, 3, 0, 1, 0, 2;
      4, 0, 3, 2, 1, 3;
      3, 0, 4, 4, 3, 1;
      1, 0, 4, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 8, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 4, 4, 4, 0;
      2, 2, 2, 4, 4, 2;
      0, 3, 3, 0, 2, 1;
      4, 4, 4, 1, 4, 4;
      0, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2872 : Certificate {3, 4, 5, 8, 9, 11} := by
  refine ⟨!![3, 4, 3, 0, 3, 4;
      0, 2, 0, 0, 4, 2;
      1, 1, 1, 1, 1, 0;
      3, 1, 2, 4, 4, 1;
      0, 3, 1, 0, 2, 0;
      3, 3, 1, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 8, 9, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 4, 4, 4, 0;
      2, 1, 0, 1, 1, 2;
      3, 3, 3, 0, 2, 1;
      2, 4, 4, 1, 4, 4;
      3, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2883 : Certificate {0, 1, 6, 8, 9, 11} := by
  refine ⟨!![2, 4, 1, 1, 3, 1;
      4, 1, 1, 3, 2, 3;
      1, 0, 1, 1, 2, 3;
      1, 3, 3, 4, 2, 3;
      2, 3, 0, 2, 4, 1;
      4, 2, 1, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 6, 8, 9, 11} =
      !![0, 0, 0, 1, 1, 2;
      0, 3, 3, 4, 4, 2;
      0, 2, 3, 1, 3, 3;
      0, 4, 3, 4, 4, 1;
      4, 1, 3, 1, 4, 4;
      4, 4, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2885 : Certificate {0, 2, 6, 8, 9, 11} := by
  refine ⟨!![1, 3, 0, 4, 1, 3;
      3, 1, 1, 1, 2, 3;
      0, 1, 2, 4, 4, 1;
      1, 1, 1, 4, 3, 2;
      3, 1, 3, 4, 0, 0;
      4, 4, 3, 2, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 6, 8, 9, 11} =
      !![0, 0, 2, 4, 4, 0;
      0, 2, 3, 4, 4, 2;
      0, 1, 3, 1, 3, 3;
      0, 0, 3, 4, 4, 1;
      4, 4, 3, 1, 4, 4;
      4, 0, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2886 : Certificate {1, 2, 6, 8, 9, 11} := by
  refine ⟨!![2, 0, 4, 1, 4, 0;
      2, 2, 0, 0, 3, 4;
      3, 1, 3, 3, 0, 1;
      2, 3, 0, 1, 1, 4;
      3, 2, 4, 1, 3, 1;
      3, 2, 4, 0, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 6, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 3, 4, 4, 2;
      2, 1, 3, 1, 3, 3;
      4, 0, 3, 4, 4, 1;
      1, 4, 3, 1, 4, 4;
      4, 0, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2889 : Certificate {0, 3, 6, 8, 9, 11} := by
  refine ⟨!![1, 3, 2, 0, 0, 4;
      4, 3, 0, 4, 0, 0;
      4, 4, 1, 0, 2, 3;
      2, 3, 0, 2, 1, 4;
      2, 4, 2, 0, 3, 2;
      4, 4, 4, 0, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 6, 8, 9, 11} =
      !![0, 3, 2, 4, 4, 0;
      0, 2, 0, 1, 1, 2;
      0, 2, 3, 1, 3, 3;
      0, 2, 3, 4, 4, 1;
      4, 2, 3, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2890 : Certificate {1, 3, 6, 8, 9, 11} := by
  refine ⟨!![4, 4, 1, 3, 3, 1;
      1, 2, 1, 1, 2, 3;
      1, 3, 2, 2, 4, 1;
      0, 2, 1, 2, 1, 1;
      0, 3, 3, 0, 3, 4;
      4, 1, 2, 3, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 6, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 0, 1, 1, 2;
      2, 2, 3, 1, 3, 3;
      4, 2, 3, 4, 4, 1;
      1, 2, 3, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2892 : Certificate {2, 3, 6, 8, 9, 11} := by
  refine ⟨!![2, 1, 0, 4, 4, 2;
      4, 0, 3, 2, 3, 0;
      4, 3, 0, 3, 0, 0;
      1, 4, 3, 4, 3, 1;
      4, 1, 1, 3, 1, 4;
      0, 1, 3, 0, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 6, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 3, 2, 4, 4, 0;
      1, 2, 3, 1, 3, 3;
      0, 2, 3, 4, 4, 1;
      4, 2, 3, 1, 4, 4;
      0, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2897 : Certificate {0, 4, 6, 8, 9, 11} := by
  refine ⟨!![2, 2, 3, 0, 1, 3;
      4, 3, 0, 4, 0, 0;
      0, 2, 4, 3, 0, 0;
      0, 4, 0, 0, 1, 4;
      2, 1, 3, 4, 4, 1;
      2, 4, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 6, 8, 9, 11} =
      !![0, 2, 2, 4, 4, 0;
      0, 1, 0, 1, 1, 2;
      0, 2, 3, 4, 4, 2;
      0, 0, 3, 4, 4, 1;
      4, 4, 3, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2898 : Certificate {1, 4, 6, 8, 9, 11} := by
  refine ⟨!![3, 2, 0, 2, 1, 3;
      4, 0, 4, 0, 1, 3;
      3, 4, 4, 0, 1, 3;
      4, 0, 0, 1, 4, 3;
      2, 2, 0, 2, 2, 0;
      0, 2, 3, 1, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 6, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 1, 0, 1, 1, 2;
      3, 2, 3, 4, 4, 2;
      4, 0, 3, 4, 4, 1;
      1, 4, 3, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2900 : Certificate {2, 4, 6, 8, 9, 11} := by
  refine ⟨!![2, 2, 3, 3, 0, 0;
      0, 1, 3, 4, 1, 3;
      4, 2, 2, 4, 4, 2;
      2, 3, 2, 3, 4, 3;
      1, 2, 3, 3, 1, 2;
      1, 4, 4, 0, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 6, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 2, 4, 4, 0;
      2, 2, 3, 4, 4, 2;
      0, 0, 3, 4, 4, 1;
      4, 4, 3, 1, 4, 4;
      0, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2904 : Certificate {3, 4, 6, 8, 9, 11} := by
  refine ⟨!![2, 0, 3, 3, 4, 2;
      3, 4, 0, 1, 1, 3;
      1, 4, 0, 2, 4, 2;
      1, 0, 3, 4, 3, 0;
      3, 0, 1, 1, 4, 1;
      2, 3, 3, 4, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 6, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 2, 4, 4, 0;
      2, 1, 0, 1, 1, 2;
      2, 0, 3, 4, 4, 1;
      2, 4, 3, 1, 4, 4;
      3, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2913 : Certificate {0, 5, 6, 8, 9, 11} := by
  refine ⟨!![0, 4, 2, 4, 4, 0;
      1, 4, 3, 3, 1, 4;
      1, 2, 1, 2, 4, 1;
      4, 0, 2, 2, 0, 0;
      1, 0, 2, 4, 2, 3;
      0, 3, 3, 2, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 6, 8, 9, 11} =
      !![0, 4, 2, 4, 4, 0;
      0, 0, 0, 1, 1, 2;
      0, 2, 3, 4, 4, 2;
      0, 0, 3, 1, 3, 3;
      4, 4, 3, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2914 : Certificate {1, 5, 6, 8, 9, 11} := by
  refine ⟨!![0, 3, 4, 3, 3, 0;
      4, 0, 4, 0, 1, 3;
      4, 4, 0, 0, 0, 0;
      1, 3, 3, 4, 4, 1;
      4, 3, 4, 3, 4, 2;
      0, 0, 4, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 6, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 0, 0, 1, 1, 2;
      3, 2, 3, 4, 4, 2;
      2, 0, 3, 1, 3, 3;
      1, 4, 3, 1, 4, 4;
      4, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2916 : Certificate {2, 5, 6, 8, 9, 11} := by
  refine ⟨!![3, 3, 1, 2, 3, 3;
      3, 4, 2, 1, 0, 2;
      1, 2, 2, 4, 3, 2;
      2, 1, 1, 0, 2, 2;
      2, 3, 1, 2, 4, 0;
      2, 2, 3, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 6, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 4, 2, 4, 4, 0;
      2, 2, 3, 4, 4, 2;
      1, 0, 3, 1, 3, 3;
      4, 4, 3, 1, 4, 4;
      0, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2920 : Certificate {3, 5, 6, 8, 9, 11} := by
  refine ⟨!![3, 3, 3, 0, 1, 3;
      0, 1, 3, 2, 0, 4;
      0, 1, 0, 0, 2, 1;
      4, 3, 0, 3, 4, 4;
      0, 1, 1, 0, 3, 3;
      0, 0, 2, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 6, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 4, 2, 4, 4, 0;
      2, 0, 0, 1, 1, 2;
      2, 0, 3, 1, 3, 3;
      2, 4, 3, 1, 4, 4;
      3, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2928 : Certificate {4, 5, 6, 8, 9, 11} := by
  refine ⟨!![4, 4, 4, 0, 3, 4;
      0, 1, 1, 4, 3, 4;
      3, 4, 3, 0, 3, 4;
      0, 4, 3, 1, 3, 0;
      4, 0, 0, 0, 1, 2;
      1, 1, 2, 2, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 6, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      2, 4, 2, 4, 4, 0;
      1, 0, 0, 1, 1, 2;
      2, 2, 3, 4, 4, 2;
      4, 4, 3, 1, 4, 4;
      3, 3, 3, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2947 : Certificate {0, 1, 7, 8, 9, 11} := by
  refine ⟨!![2, 3, 3, 4, 1, 3;
      1, 4, 2, 1, 2, 3;
      1, 1, 4, 3, 4, 1;
      4, 2, 3, 0, 1, 4;
      2, 0, 1, 1, 3, 2;
      3, 2, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 7, 8, 9, 11} =
      !![0, 0, 4, 1, 1, 2;
      0, 3, 2, 4, 4, 2;
      0, 2, 4, 1, 3, 3;
      0, 4, 4, 4, 4, 1;
      4, 2, 3, 0, 2, 1;
      4, 4, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2949 : Certificate {0, 2, 7, 8, 9, 11} := by
  refine ⟨!![3, 3, 4, 1, 2, 2;
      3, 3, 0, 4, 0, 0;
      2, 4, 2, 3, 2, 3;
      4, 0, 0, 3, 3, 2;
      2, 4, 2, 0, 4, 1;
      3, 3, 4, 2, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 7, 8, 9, 11} =
      !![0, 0, 1, 4, 4, 0;
      0, 2, 2, 4, 4, 2;
      0, 1, 4, 1, 3, 3;
      0, 0, 4, 4, 4, 1;
      4, 0, 3, 0, 2, 1;
      4, 0, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2950 : Certificate {1, 2, 7, 8, 9, 11} := by
  refine ⟨!![2, 0, 0, 4, 2, 4;
      1, 0, 1, 0, 4, 0;
      1, 2, 1, 1, 0, 2;
      1, 1, 3, 2, 3, 3;
      3, 2, 1, 2, 4, 4;
      2, 0, 0, 0, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 7, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 2, 4, 4, 2;
      2, 1, 4, 1, 3, 3;
      4, 0, 4, 4, 4, 1;
      2, 0, 3, 0, 2, 1;
      4, 0, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2953 : Certificate {0, 3, 7, 8, 9, 11} := by
  refine ⟨!![3, 3, 0, 4, 3, 1;
      3, 3, 1, 2, 1, 4;
      3, 0, 2, 1, 2, 3;
      0, 1, 2, 2, 0, 0;
      1, 3, 3, 0, 0, 0;
      3, 3, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 7, 8, 9, 11} =
      !![0, 3, 1, 4, 4, 0;
      0, 2, 4, 1, 1, 2;
      0, 2, 4, 1, 3, 3;
      0, 2, 4, 4, 4, 1;
      4, 3, 3, 0, 2, 1;
      4, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2954 : Certificate {1, 3, 7, 8, 9, 11} := by
  refine ⟨!![3, 0, 1, 4, 1, 4;
      4, 0, 4, 0, 1, 0;
      1, 2, 4, 0, 1, 0;
      4, 1, 0, 4, 3, 2;
      3, 2, 4, 1, 0, 2;
      3, 0, 1, 0, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 7, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 4, 1, 1, 2;
      2, 2, 4, 1, 3, 3;
      4, 2, 4, 4, 4, 1;
      2, 3, 3, 0, 2, 1;
      4, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2956 : Certificate {2, 3, 7, 8, 9, 11} := by
  refine ⟨!![3, 0, 1, 4, 1, 4;
      2, 0, 0, 4, 2, 4;
      4, 3, 0, 3, 0, 0;
      4, 4, 0, 1, 2, 0;
      1, 3, 0, 4, 4, 2;
      0, 0, 0, 1, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 7, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 3, 1, 4, 4, 0;
      1, 2, 4, 1, 3, 3;
      0, 2, 4, 4, 4, 1;
      0, 3, 3, 0, 2, 1;
      0, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2961 : Certificate {0, 4, 7, 8, 9, 11} := by
  refine ⟨!![4, 3, 1, 2, 3, 1;
      4, 0, 4, 2, 0, 0;
      0, 4, 3, 1, 0, 0;
      2, 0, 3, 2, 3, 2;
      0, 4, 3, 3, 2, 3;
      2, 3, 4, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 7, 8, 9, 11} =
      !![0, 2, 1, 4, 4, 0;
      0, 1, 4, 1, 1, 2;
      0, 2, 2, 4, 4, 2;
      0, 0, 4, 4, 4, 1;
      4, 3, 3, 0, 2, 1;
      4, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2962 : Certificate {1, 4, 7, 8, 9, 11} := by
  refine ⟨!![3, 1, 4, 1, 4, 3;
      3, 3, 2, 1, 1, 2;
      1, 1, 1, 3, 3, 1;
      1, 3, 3, 3, 2, 0;
      4, 2, 0, 1, 4, 2;
      4, 2, 3, 4, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 7, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 1, 4, 1, 1, 2;
      3, 2, 2, 4, 4, 2;
      4, 0, 4, 4, 4, 1;
      2, 3, 3, 0, 2, 1;
      4, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2964 : Certificate {2, 4, 7, 8, 9, 11} := by
  refine ⟨!![2, 3, 3, 3, 2, 4;
      4, 0, 0, 3, 4, 3;
      0, 3, 0, 0, 1, 2;
      3, 4, 0, 4, 1, 3;
      0, 3, 0, 2, 3, 0;
      3, 0, 0, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 7, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 1, 4, 4, 0;
      2, 2, 2, 4, 4, 2;
      0, 0, 4, 4, 4, 1;
      0, 3, 3, 0, 2, 1;
      0, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2968 : Certificate {3, 4, 7, 8, 9, 11} := by
  refine ⟨!![2, 1, 1, 2, 3, 1;
      0, 3, 3, 4, 3, 1;
      4, 0, 2, 4, 2, 4;
      4, 2, 3, 0, 0, 1;
      1, 1, 3, 3, 2, 3;
      0, 1, 1, 4, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 7, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 1, 4, 4, 0;
      2, 1, 4, 1, 1, 2;
      2, 0, 4, 4, 4, 1;
      3, 3, 3, 0, 2, 1;
      3, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2977 : Certificate {0, 5, 7, 8, 9, 11} := by
  refine ⟨!![2, 2, 0, 3, 1, 3;
      3, 1, 2, 2, 2, 3;
      1, 0, 3, 2, 2, 3;
      3, 0, 4, 0, 3, 2;
      4, 4, 2, 0, 2, 3;
      2, 1, 1, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 7, 8, 9, 11} =
      !![0, 4, 1, 4, 4, 0;
      0, 0, 4, 1, 1, 2;
      0, 2, 2, 4, 4, 2;
      0, 0, 4, 1, 3, 3;
      4, 3, 3, 0, 2, 1;
      4, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2978 : Certificate {1, 5, 7, 8, 9, 11} := by
  refine ⟨!![2, 3, 2, 2, 1, 1;
      3, 0, 0, 3, 2, 0;
      2, 2, 0, 0, 0, 0;
      3, 4, 2, 1, 3, 4;
      1, 4, 3, 0, 3, 0;
      4, 0, 0, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 7, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 0, 4, 1, 1, 2;
      3, 2, 2, 4, 4, 2;
      2, 0, 4, 1, 3, 3;
      2, 3, 3, 0, 2, 1;
      4, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2980 : Certificate {2, 5, 7, 8, 9, 11} := by
  refine ⟨!![3, 3, 3, 0, 3, 1;
      4, 1, 1, 3, 3, 2;
      1, 2, 4, 2, 3, 0;
      1, 4, 0, 0, 4, 4;
      1, 1, 3, 4, 1, 4;
      3, 4, 4, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 7, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 4, 1, 4, 4, 0;
      2, 2, 2, 4, 4, 2;
      1, 0, 4, 1, 3, 3;
      0, 3, 3, 0, 2, 1;
      0, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2984 : Certificate {3, 5, 7, 8, 9, 11} := by
  refine ⟨!![0, 4, 4, 1, 2, 1;
      3, 2, 2, 1, 3, 3;
      2, 4, 1, 1, 2, 1;
      1, 0, 1, 4, 2, 3;
      3, 3, 0, 4, 3, 3;
      4, 4, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 7, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 4, 1, 4, 4, 0;
      2, 0, 4, 1, 1, 2;
      2, 0, 4, 1, 3, 3;
      3, 3, 3, 0, 2, 1;
      3, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2992 : Certificate {4, 5, 7, 8, 9, 11} := by
  refine ⟨!![2, 2, 0, 2, 2, 4;
      2, 2, 3, 4, 0, 0;
      3, 1, 2, 1, 1, 2;
      2, 0, 0, 1, 0, 1;
      3, 2, 4, 0, 0, 4;
      3, 1, 2, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 7, 8, 9, 11} =
      !![0, 0, 4, 4, 4, 3;
      2, 4, 1, 4, 4, 0;
      1, 0, 4, 1, 1, 2;
      2, 2, 2, 4, 4, 2;
      3, 3, 3, 0, 2, 1;
      3, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3009 : Certificate {0, 6, 7, 8, 9, 11} := by
  refine ⟨!![4, 4, 0, 2, 3, 4;
      4, 0, 4, 0, 2, 0;
      2, 4, 0, 0, 2, 0;
      2, 1, 2, 2, 3, 0;
      2, 3, 1, 3, 3, 0;
      4, 3, 1, 0, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 6, 7, 8, 9, 11} =
      !![0, 2, 1, 4, 4, 0;
      0, 0, 4, 1, 1, 2;
      0, 3, 2, 4, 4, 2;
      0, 3, 4, 1, 3, 3;
      0, 3, 4, 4, 4, 1;
      4, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3010 : Certificate {1, 6, 7, 8, 9, 11} := by
  refine ⟨!![3, 3, 2, 3, 0, 1;
      1, 2, 3, 4, 4, 3;
      4, 1, 1, 3, 3, 1;
      2, 1, 0, 3, 4, 2;
      0, 1, 1, 2, 4, 3;
      1, 0, 0, 4, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 6, 7, 8, 9, 11} =
      !![0, 4, 4, 4, 4, 3;
      0, 0, 4, 1, 1, 2;
      3, 3, 2, 4, 4, 2;
      2, 3, 4, 1, 3, 3;
      4, 3, 4, 4, 4, 1;
      4, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3012 : Certificate {2, 6, 7, 8, 9, 11} := by
  refine ⟨!![1, 4, 4, 3, 3, 1;
      2, 2, 2, 1, 3, 2;
      2, 1, 3, 4, 0, 3;
      2, 4, 0, 0, 2, 1;
      4, 0, 2, 1, 4, 1;
      2, 4, 4, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 6, 7, 8, 9, 11} =
      !![0, 4, 4, 4, 4, 3;
      0, 2, 1, 4, 4, 0;
      2, 3, 2, 4, 4, 2;
      1, 3, 4, 1, 3, 3;
      0, 3, 4, 4, 4, 1;
      0, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3016 : Certificate {3, 6, 7, 8, 9, 11} := by
  refine ⟨!![0, 2, 2, 1, 4, 2;
      4, 2, 2, 3, 3, 1;
      0, 1, 3, 2, 0, 4;
      2, 1, 2, 1, 1, 3;
      1, 4, 1, 0, 2, 4;
      1, 1, 1, 2, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 6, 7, 8, 9, 11} =
      !![0, 4, 4, 4, 4, 3;
      3, 2, 1, 4, 4, 0;
      2, 0, 4, 1, 1, 2;
      2, 3, 4, 1, 3, 3;
      2, 3, 4, 4, 4, 1;
      3, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3024 : Certificate {4, 6, 7, 8, 9, 11} := by
  refine ⟨!![2, 1, 3, 3, 2, 0;
      3, 3, 2, 1, 0, 0;
      4, 4, 0, 1, 1, 0;
      0, 3, 2, 2, 0, 1;
      4, 3, 3, 2, 0, 4;
      4, 1, 4, 2, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 6, 7, 8, 9, 11} =
      !![0, 4, 4, 4, 4, 3;
      2, 2, 1, 4, 4, 0;
      1, 0, 4, 1, 1, 2;
      2, 3, 2, 4, 4, 2;
      0, 3, 4, 4, 4, 1;
      3, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3040 : Certificate {5, 6, 7, 8, 9, 11} := by
  refine ⟨!![4, 0, 4, 1, 4, 3;
      2, 3, 1, 2, 4, 3;
      1, 1, 4, 4, 3, 1;
      4, 3, 1, 3, 4, 4;
      2, 3, 1, 4, 3, 0;
      0, 0, 4, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {5, 6, 7, 8, 9, 11} =
      !![0, 4, 4, 4, 4, 3;
      4, 2, 1, 4, 4, 0;
      0, 0, 4, 1, 1, 2;
      2, 3, 2, 4, 4, 2;
      0, 3, 4, 1, 3, 3;
      3, 3, 0, 4, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 2900 then
    if mask < 2858 then
      if mask < 2841 then
        if mask < 2830 then
          if mask < 2827 then
            ⟨{0, 1, 2, 8, 9, 11}, certificate_2823⟩
          else
            if mask < 2829 then
              ⟨{0, 1, 3, 8, 9, 11}, certificate_2827⟩
            else
              ⟨{0, 2, 3, 8, 9, 11}, certificate_2829⟩
        else
          if mask < 2837 then
            if mask < 2835 then
              ⟨{1, 2, 3, 8, 9, 11}, certificate_2830⟩
            else
              ⟨{0, 1, 4, 8, 9, 11}, certificate_2835⟩
          else
            if mask < 2838 then
              ⟨{0, 2, 4, 8, 9, 11}, certificate_2837⟩
            else
              ⟨{1, 2, 4, 8, 9, 11}, certificate_2838⟩
      else
        if mask < 2851 then
          if mask < 2842 then
            ⟨{0, 3, 4, 8, 9, 11}, certificate_2841⟩
          else
            if mask < 2844 then
              ⟨{1, 3, 4, 8, 9, 11}, certificate_2842⟩
            else
              ⟨{2, 3, 4, 8, 9, 11}, certificate_2844⟩
        else
          if mask < 2854 then
            if mask < 2853 then
              ⟨{0, 1, 5, 8, 9, 11}, certificate_2851⟩
            else
              ⟨{0, 2, 5, 8, 9, 11}, certificate_2853⟩
          else
            if mask < 2857 then
              ⟨{1, 2, 5, 8, 9, 11}, certificate_2854⟩
            else
              ⟨{0, 3, 5, 8, 9, 11}, certificate_2857⟩
    else
      if mask < 2885 then
        if mask < 2866 then
          if mask < 2860 then
            ⟨{1, 3, 5, 8, 9, 11}, certificate_2858⟩
          else
            if mask < 2865 then
              ⟨{2, 3, 5, 8, 9, 11}, certificate_2860⟩
            else
              ⟨{0, 4, 5, 8, 9, 11}, certificate_2865⟩
        else
          if mask < 2872 then
            if mask < 2868 then
              ⟨{1, 4, 5, 8, 9, 11}, certificate_2866⟩
            else
              ⟨{2, 4, 5, 8, 9, 11}, certificate_2868⟩
          else
            if mask < 2883 then
              ⟨{3, 4, 5, 8, 9, 11}, certificate_2872⟩
            else
              ⟨{0, 1, 6, 8, 9, 11}, certificate_2883⟩
      else
        if mask < 2890 then
          if mask < 2886 then
            ⟨{0, 2, 6, 8, 9, 11}, certificate_2885⟩
          else
            if mask < 2889 then
              ⟨{1, 2, 6, 8, 9, 11}, certificate_2886⟩
            else
              ⟨{0, 3, 6, 8, 9, 11}, certificate_2889⟩
        else
          if mask < 2897 then
            if mask < 2892 then
              ⟨{1, 3, 6, 8, 9, 11}, certificate_2890⟩
            else
              ⟨{2, 3, 6, 8, 9, 11}, certificate_2892⟩
          else
            if mask < 2898 then
              ⟨{0, 4, 6, 8, 9, 11}, certificate_2897⟩
            else
              ⟨{1, 4, 6, 8, 9, 11}, certificate_2898⟩
  else
    if mask < 2962 then
      if mask < 2947 then
        if mask < 2914 then
          if mask < 2904 then
            ⟨{2, 4, 6, 8, 9, 11}, certificate_2900⟩
          else
            if mask < 2913 then
              ⟨{3, 4, 6, 8, 9, 11}, certificate_2904⟩
            else
              ⟨{0, 5, 6, 8, 9, 11}, certificate_2913⟩
        else
          if mask < 2920 then
            if mask < 2916 then
              ⟨{1, 5, 6, 8, 9, 11}, certificate_2914⟩
            else
              ⟨{2, 5, 6, 8, 9, 11}, certificate_2916⟩
          else
            if mask < 2928 then
              ⟨{3, 5, 6, 8, 9, 11}, certificate_2920⟩
            else
              ⟨{4, 5, 6, 8, 9, 11}, certificate_2928⟩
      else
        if mask < 2953 then
          if mask < 2949 then
            ⟨{0, 1, 7, 8, 9, 11}, certificate_2947⟩
          else
            if mask < 2950 then
              ⟨{0, 2, 7, 8, 9, 11}, certificate_2949⟩
            else
              ⟨{1, 2, 7, 8, 9, 11}, certificate_2950⟩
        else
          if mask < 2956 then
            if mask < 2954 then
              ⟨{0, 3, 7, 8, 9, 11}, certificate_2953⟩
            else
              ⟨{1, 3, 7, 8, 9, 11}, certificate_2954⟩
          else
            if mask < 2961 then
              ⟨{2, 3, 7, 8, 9, 11}, certificate_2956⟩
            else
              ⟨{0, 4, 7, 8, 9, 11}, certificate_2961⟩
    else
      if mask < 2992 then
        if mask < 2977 then
          if mask < 2964 then
            ⟨{1, 4, 7, 8, 9, 11}, certificate_2962⟩
          else
            if mask < 2968 then
              ⟨{2, 4, 7, 8, 9, 11}, certificate_2964⟩
            else
              ⟨{3, 4, 7, 8, 9, 11}, certificate_2968⟩
        else
          if mask < 2980 then
            if mask < 2978 then
              ⟨{0, 5, 7, 8, 9, 11}, certificate_2977⟩
            else
              ⟨{1, 5, 7, 8, 9, 11}, certificate_2978⟩
          else
            if mask < 2984 then
              ⟨{2, 5, 7, 8, 9, 11}, certificate_2980⟩
            else
              ⟨{3, 5, 7, 8, 9, 11}, certificate_2984⟩
      else
        if mask < 3012 then
          if mask < 3009 then
            ⟨{4, 5, 7, 8, 9, 11}, certificate_2992⟩
          else
            if mask < 3010 then
              ⟨{0, 6, 7, 8, 9, 11}, certificate_3009⟩
            else
              ⟨{1, 6, 7, 8, 9, 11}, certificate_3010⟩
        else
          if mask < 3024 then
            if mask < 3016 then
              ⟨{2, 6, 7, 8, 9, 11}, certificate_3012⟩
            else
              ⟨{3, 6, 7, 8, 9, 11}, certificate_3016⟩
          else
            if mask < 3040 then
              ⟨{4, 6, 7, 8, 9, 11}, certificate_3024⟩
            else
              ⟨{5, 6, 7, 8, 9, 11}, certificate_3040⟩
end AMEProbe.QuinaryDirect.Batch11
#print axioms AMEProbe.QuinaryDirect.Batch11.lookup
