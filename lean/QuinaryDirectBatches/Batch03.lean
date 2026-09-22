import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch03
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_783 : Certificate {0, 1, 2, 3, 8, 9} := by
  refine ⟨!![3, 3, 3, 0, 4, 1;
      2, 1, 0, 0, 2, 4;
      1, 1, 0, 3, 4, 4;
      4, 3, 1, 2, 4, 4;
      0, 3, 4, 2, 2, 1;
      1, 1, 3, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 8, 9} =
      !![0, 2, 1, 2, 1, 3;
      0, 4, 0, 2, 4, 4;
      4, 2, 0, 3, 0, 2;
      4, 1, 4, 2, 1, 4;
      4, 4, 0, 3, 4, 3;
      3, 0, 2, 2, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_791 : Certificate {0, 1, 2, 4, 8, 9} := by
  refine ⟨!![2, 3, 1, 4, 4, 0;
      4, 4, 2, 0, 1, 1;
      3, 3, 1, 2, 0, 1;
      2, 1, 0, 3, 3, 2;
      2, 4, 4, 0, 0, 3;
      4, 1, 4, 0, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 8, 9} =
      !![0, 3, 2, 2, 4, 4;
      0, 4, 0, 0, 4, 4;
      4, 2, 0, 3, 0, 2;
      4, 1, 4, 4, 1, 4;
      4, 4, 0, 3, 4, 3;
      3, 0, 2, 3, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_795 : Certificate {0, 1, 3, 4, 8, 9} := by
  refine ⟨!![3, 2, 1, 3, 3, 1;
      3, 1, 3, 1, 0, 3;
      3, 1, 4, 2, 4, 0;
      2, 3, 2, 3, 4, 3;
      2, 1, 1, 0, 1, 4;
      1, 4, 4, 3, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 8, 9} =
      !![0, 0, 2, 1, 1, 1;
      0, 4, 2, 0, 4, 4;
      4, 2, 3, 3, 0, 2;
      4, 1, 2, 4, 1, 4;
      4, 4, 3, 3, 4, 3;
      3, 0, 2, 3, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_797 : Certificate {0, 2, 3, 4, 8, 9} := by
  refine ⟨!![1, 2, 2, 3, 1, 4;
      1, 1, 4, 1, 3, 1;
      2, 2, 4, 3, 0, 4;
      2, 1, 3, 1, 0, 3;
      2, 4, 2, 3, 2, 4;
      2, 4, 1, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 8, 9} =
      !![0, 0, 3, 2, 4, 4;
      0, 0, 2, 0, 4, 4;
      4, 0, 3, 3, 0, 2;
      4, 4, 2, 4, 1, 4;
      4, 0, 3, 3, 4, 3;
      3, 2, 2, 3, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_798 : Certificate {1, 2, 3, 4, 8, 9} := by
  refine ⟨!![2, 0, 0, 3, 2, 4;
      3, 4, 2, 0, 0, 3;
      3, 3, 0, 4, 1, 2;
      4, 2, 4, 1, 2, 3;
      4, 0, 3, 3, 4, 4;
      0, 0, 2, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 8, 9} =
      !![0, 0, 0, 0, 4, 4;
      4, 0, 2, 0, 4, 4;
      2, 0, 3, 3, 0, 2;
      1, 4, 2, 4, 1, 4;
      4, 0, 3, 3, 4, 3;
      0, 2, 2, 3, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_807 : Certificate {0, 1, 2, 5, 8, 9} := by
  refine ⟨!![0, 4, 2, 3, 0, 2;
      1, 0, 2, 3, 4, 3;
      4, 2, 4, 2, 1, 4;
      4, 4, 1, 3, 0, 3;
      0, 1, 3, 0, 3, 2;
      3, 1, 3, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 8, 9} =
      !![0, 3, 2, 2, 4, 4;
      0, 2, 1, 0, 1, 3;
      4, 2, 0, 3, 0, 2;
      4, 1, 4, 4, 1, 4;
      4, 4, 0, 3, 4, 3;
      3, 0, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_811 : Certificate {0, 1, 3, 5, 8, 9} := by
  refine ⟨!![1, 1, 4, 3, 3, 2;
      4, 0, 4, 0, 2, 2;
      1, 2, 2, 0, 3, 0;
      3, 3, 3, 1, 3, 4;
      1, 3, 0, 0, 1, 2;
      3, 3, 1, 0, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 8, 9} =
      !![0, 0, 2, 0, 1, 1;
      0, 2, 2, 0, 1, 3;
      4, 2, 3, 3, 0, 2;
      4, 1, 2, 4, 1, 4;
      4, 4, 3, 3, 4, 3;
      3, 0, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_813 : Certificate {0, 2, 3, 5, 8, 9} := by
  refine ⟨!![4, 3, 4, 2, 4, 2;
      1, 3, 4, 1, 1, 2;
      4, 4, 2, 4, 4, 0;
      3, 2, 2, 4, 2, 1;
      4, 0, 0, 4, 2, 2;
      4, 0, 4, 4, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 8, 9} =
      !![0, 0, 3, 4, 4, 4;
      0, 1, 2, 0, 1, 3;
      4, 0, 3, 3, 0, 2;
      4, 4, 2, 4, 1, 4;
      4, 0, 3, 3, 4, 3;
      3, 2, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_814 : Certificate {1, 2, 3, 5, 8, 9} := by
  refine ⟨!![3, 2, 3, 2, 1, 0;
      2, 4, 0, 1, 4, 4;
      0, 1, 3, 2, 0, 3;
      2, 4, 1, 3, 3, 2;
      0, 2, 1, 2, 3, 0;
      4, 3, 4, 3, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 8, 9} =
      !![0, 0, 0, 0, 4, 4;
      2, 1, 2, 0, 1, 3;
      2, 0, 3, 3, 0, 2;
      1, 4, 2, 4, 1, 4;
      4, 0, 3, 3, 4, 3;
      0, 2, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_819 : Certificate {0, 1, 4, 5, 8, 9} := by
  refine ⟨!![4, 1, 1, 1, 1, 3;
      3, 4, 1, 2, 0, 1;
      2, 2, 1, 1, 4, 2;
      3, 4, 2, 3, 4, 3;
      0, 3, 1, 4, 0, 0;
      4, 0, 3, 0, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 8, 9} =
      !![0, 0, 1, 0, 1, 1;
      0, 3, 2, 2, 4, 4;
      4, 2, 3, 3, 0, 2;
      4, 1, 4, 4, 1, 4;
      4, 4, 3, 3, 4, 3;
      3, 0, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_821 : Certificate {0, 2, 4, 5, 8, 9} := by
  refine ⟨!![1, 3, 1, 3, 3, 1;
      3, 2, 4, 4, 1, 3;
      0, 1, 2, 3, 4, 3;
      1, 4, 4, 4, 1, 3;
      4, 4, 3, 1, 3, 4;
      4, 4, 2, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 8, 9} =
      !![0, 0, 2, 4, 4, 4;
      0, 2, 2, 2, 4, 4;
      4, 0, 3, 3, 0, 2;
      4, 4, 4, 4, 1, 4;
      4, 0, 3, 3, 4, 3;
      3, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_822 : Certificate {1, 2, 4, 5, 8, 9} := by
  refine ⟨!![1, 4, 2, 3, 3, 0;
      1, 2, 3, 3, 0, 0;
      4, 2, 0, 0, 1, 3;
      3, 3, 4, 0, 2, 2;
      3, 4, 0, 3, 0, 0;
      1, 1, 0, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 8, 9} =
      !![0, 0, 0, 0, 4, 4;
      3, 2, 2, 2, 4, 4;
      2, 0, 3, 3, 0, 2;
      1, 4, 4, 4, 1, 4;
      4, 0, 3, 3, 4, 3;
      0, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_825 : Certificate {0, 3, 4, 5, 8, 9} := by
  refine ⟨!![3, 3, 3, 1, 2, 4;
      1, 2, 2, 1, 2, 0;
      0, 3, 3, 0, 4, 4;
      4, 3, 4, 0, 2, 2;
      4, 2, 2, 4, 3, 3;
      4, 2, 1, 4, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 8, 9} =
      !![0, 3, 2, 4, 4, 4;
      0, 2, 1, 0, 1, 1;
      4, 3, 3, 3, 0, 2;
      4, 2, 4, 4, 1, 4;
      4, 3, 3, 3, 4, 3;
      3, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_826 : Certificate {1, 3, 4, 5, 8, 9} := by
  refine ⟨!![3, 3, 0, 1, 0, 1;
      1, 2, 1, 1, 3, 4;
      4, 2, 3, 3, 4, 2;
      2, 1, 0, 1, 1, 4;
      0, 3, 3, 1, 2, 1;
      4, 2, 2, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 8, 9} =
      !![0, 0, 0, 0, 4, 4;
      0, 2, 1, 0, 1, 1;
      2, 3, 3, 3, 0, 2;
      1, 2, 4, 4, 1, 4;
      4, 3, 3, 3, 4, 3;
      0, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_828 : Certificate {2, 3, 4, 5, 8, 9} := by
  refine ⟨!![2, 3, 3, 0, 2, 3;
      3, 1, 2, 2, 2, 1;
      3, 4, 2, 4, 0, 2;
      1, 0, 0, 4, 1, 2;
      2, 0, 3, 0, 2, 0;
      2, 0, 2, 0, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 8, 9} =
      !![0, 0, 0, 0, 4, 4;
      0, 3, 2, 4, 4, 4;
      0, 3, 3, 3, 0, 2;
      4, 2, 4, 4, 1, 4;
      0, 3, 3, 3, 4, 3;
      2, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_839 : Certificate {0, 1, 2, 6, 8, 9} := by
  refine ⟨!![4, 1, 1, 0, 3, 3;
      3, 2, 0, 2, 4, 2;
      2, 1, 2, 1, 2, 1;
      3, 0, 4, 2, 2, 3;
      0, 4, 1, 4, 1, 0;
      1, 4, 0, 0, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 6, 8, 9} =
      !![0, 3, 2, 3, 4, 4;
      0, 2, 1, 3, 1, 3;
      0, 4, 0, 3, 4, 4;
      4, 1, 4, 3, 1, 4;
      4, 4, 0, 3, 4, 3;
      3, 0, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_843 : Certificate {0, 1, 3, 6, 8, 9} := by
  refine ⟨!![2, 4, 2, 1, 2, 3;
      0, 3, 2, 3, 1, 3;
      4, 0, 0, 1, 1, 4;
      0, 1, 1, 3, 4, 4;
      1, 4, 1, 3, 0, 1;
      2, 1, 4, 0, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 6, 8, 9} =
      !![0, 0, 2, 0, 1, 1;
      0, 2, 2, 3, 1, 3;
      0, 4, 2, 3, 4, 4;
      4, 1, 2, 3, 1, 4;
      4, 4, 3, 3, 4, 3;
      3, 0, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_845 : Certificate {0, 2, 3, 6, 8, 9} := by
  refine ⟨!![3, 4, 0, 4, 0, 0;
      0, 3, 2, 3, 1, 3;
      1, 3, 3, 0, 3, 1;
      0, 3, 4, 0, 3, 1;
      4, 1, 3, 4, 3, 4;
      3, 4, 4, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 6, 8, 9} =
      !![0, 0, 3, 2, 4, 4;
      0, 1, 2, 3, 1, 3;
      0, 0, 2, 3, 4, 4;
      4, 4, 2, 3, 1, 4;
      4, 0, 3, 3, 4, 3;
      3, 2, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_846 : Certificate {1, 2, 3, 6, 8, 9} := by
  refine ⟨!![4, 3, 4, 1, 2, 4;
      1, 0, 3, 2, 4, 4;
      1, 2, 4, 1, 1, 2;
      4, 1, 3, 1, 0, 0;
      4, 2, 2, 3, 0, 3;
      1, 2, 0, 1, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 6, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      2, 1, 2, 3, 1, 3;
      4, 0, 2, 3, 4, 4;
      1, 4, 2, 3, 1, 4;
      4, 0, 3, 3, 4, 3;
      0, 2, 2, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_851 : Certificate {0, 1, 4, 6, 8, 9} := by
  refine ⟨!![3, 2, 4, 1, 3, 0;
      1, 4, 1, 4, 4, 1;
      3, 0, 0, 2, 2, 3;
      3, 3, 4, 4, 4, 1;
      2, 2, 3, 3, 1, 3;
      1, 3, 2, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 6, 8, 9} =
      !![0, 0, 1, 0, 1, 1;
      0, 3, 2, 3, 4, 4;
      0, 4, 0, 3, 4, 4;
      4, 1, 4, 3, 1, 4;
      4, 4, 3, 3, 4, 3;
      3, 0, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_853 : Certificate {0, 2, 4, 6, 8, 9} := by
  refine ⟨!![0, 0, 1, 4, 1, 2;
      4, 0, 4, 3, 3, 2;
      1, 3, 3, 2, 2, 3;
      1, 1, 2, 4, 4, 1;
      0, 4, 1, 0, 3, 1;
      3, 4, 4, 2, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 6, 8, 9} =
      !![0, 0, 2, 2, 4, 4;
      0, 2, 2, 3, 4, 4;
      0, 0, 0, 3, 4, 4;
      4, 4, 4, 3, 1, 4;
      4, 0, 3, 3, 4, 3;
      3, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_854 : Certificate {1, 2, 4, 6, 8, 9} := by
  refine ⟨!![0, 0, 3, 2, 3, 1;
      4, 1, 4, 0, 4, 2;
      1, 2, 2, 1, 0, 1;
      1, 0, 1, 3, 2, 4;
      0, 4, 2, 4, 4, 3;
      3, 1, 2, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 6, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 4, 4;
      4, 0, 0, 3, 4, 4;
      1, 4, 4, 3, 1, 4;
      4, 0, 3, 3, 4, 3;
      0, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_857 : Certificate {0, 3, 4, 6, 8, 9} := by
  refine ⟨!![3, 0, 4, 0, 2, 1;
      1, 0, 1, 2, 2, 3;
      3, 3, 3, 3, 3, 2;
      1, 1, 3, 3, 3, 2;
      3, 4, 3, 2, 0, 4;
      2, 4, 2, 1, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 6, 8, 9} =
      !![0, 3, 2, 2, 4, 4;
      0, 2, 1, 0, 1, 1;
      0, 2, 0, 3, 4, 4;
      4, 2, 4, 3, 1, 4;
      4, 3, 3, 3, 4, 3;
      3, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_858 : Certificate {1, 3, 4, 6, 8, 9} := by
  refine ⟨!![4, 1, 0, 4, 3, 3;
      1, 4, 3, 3, 0, 3;
      3, 0, 4, 1, 2, 2;
      4, 2, 0, 2, 2, 3;
      0, 4, 4, 2, 3, 3;
      0, 4, 1, 1, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 6, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 1, 0, 1, 1;
      4, 2, 0, 3, 4, 4;
      1, 2, 4, 3, 1, 4;
      4, 3, 3, 3, 4, 3;
      0, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_860 : Certificate {2, 3, 4, 6, 8, 9} := by
  refine ⟨!![0, 4, 2, 0, 1, 3;
      0, 0, 3, 2, 3, 1;
      3, 3, 3, 1, 4, 3;
      1, 0, 0, 4, 1, 2;
      4, 1, 2, 1, 0, 3;
      4, 4, 3, 0, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 6, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 2, 2, 4, 4;
      0, 2, 0, 3, 4, 4;
      4, 2, 4, 3, 1, 4;
      0, 3, 3, 3, 4, 3;
      2, 2, 3, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_867 : Certificate {0, 1, 5, 6, 8, 9} := by
  refine ⟨!![0, 3, 3, 2, 2, 0;
      3, 3, 2, 4, 1, 0;
      4, 0, 0, 1, 1, 4;
      3, 4, 3, 2, 0, 4;
      4, 4, 1, 2, 1, 1;
      2, 1, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 6, 8, 9} =
      !![0, 0, 0, 0, 1, 1;
      0, 3, 2, 3, 4, 4;
      0, 2, 0, 3, 1, 3;
      4, 1, 4, 3, 1, 4;
      4, 4, 3, 3, 4, 3;
      3, 0, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_869 : Certificate {0, 2, 5, 6, 8, 9} := by
  refine ⟨!![3, 2, 2, 2, 1, 3;
      1, 3, 3, 0, 3, 1;
      0, 1, 4, 4, 3, 4;
      2, 2, 2, 3, 0, 1;
      3, 4, 4, 0, 2, 4;
      0, 4, 1, 2, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 6, 8, 9} =
      !![0, 0, 4, 2, 4, 4;
      0, 2, 2, 3, 4, 4;
      0, 1, 0, 3, 1, 3;
      4, 4, 4, 3, 1, 4;
      4, 0, 3, 3, 4, 3;
      3, 2, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_870 : Certificate {1, 2, 5, 6, 8, 9} := by
  refine ⟨!![3, 0, 1, 0, 1, 2;
      0, 4, 4, 1, 1, 0;
      4, 1, 2, 4, 1, 0;
      3, 4, 0, 0, 2, 1;
      4, 2, 0, 3, 4, 2;
      2, 4, 0, 2, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 6, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 4, 4;
      2, 1, 0, 3, 1, 3;
      1, 4, 4, 3, 1, 4;
      4, 0, 3, 3, 4, 3;
      0, 2, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_873 : Certificate {0, 3, 5, 6, 8, 9} := by
  refine ⟨!![0, 2, 1, 3, 1, 0;
      4, 3, 4, 4, 3, 4;
      1, 1, 1, 2, 3, 0;
      1, 1, 3, 1, 4, 0;
      1, 2, 1, 1, 0, 2;
      1, 3, 1, 1, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 6, 8, 9} =
      !![0, 3, 4, 2, 4, 4;
      0, 2, 0, 0, 1, 1;
      0, 2, 0, 3, 1, 3;
      4, 2, 4, 3, 1, 4;
      4, 3, 3, 3, 4, 3;
      3, 2, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_874 : Certificate {1, 3, 5, 6, 8, 9} := by
  refine ⟨!![0, 3, 4, 2, 4, 0;
      2, 3, 3, 2, 3, 3;
      3, 1, 2, 4, 3, 1;
      3, 0, 1, 4, 1, 1;
      3, 1, 4, 4, 2, 3;
      3, 4, 0, 2, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 6, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 0, 0, 1, 1;
      2, 2, 0, 3, 1, 3;
      1, 2, 4, 3, 1, 4;
      4, 3, 3, 3, 4, 3;
      0, 2, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_876 : Certificate {2, 3, 5, 6, 8, 9} := by
  refine ⟨!![3, 4, 1, 2, 0, 1;
      2, 0, 4, 0, 4, 3;
      0, 1, 3, 3, 0, 0;
      1, 4, 2, 1, 1, 2;
      2, 2, 4, 1, 4, 1;
      1, 4, 4, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 6, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 4, 2, 4, 4;
      1, 2, 0, 3, 1, 3;
      4, 2, 4, 3, 1, 4;
      0, 3, 3, 3, 4, 3;
      2, 2, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_881 : Certificate {0, 4, 5, 6, 8, 9} := by
  refine ⟨!![4, 0, 0, 2, 4, 4;
      2, 1, 2, 3, 3, 2;
      4, 1, 4, 2, 2, 3;
      2, 2, 4, 4, 4, 1;
      1, 3, 1, 4, 2, 2;
      2, 2, 2, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 6, 8, 9} =
      !![0, 2, 4, 2, 4, 4;
      0, 1, 0, 0, 1, 1;
      0, 2, 2, 3, 4, 4;
      4, 4, 4, 3, 1, 4;
      4, 3, 3, 3, 4, 3;
      3, 3, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_882 : Certificate {1, 4, 5, 6, 8, 9} := by
  refine ⟨!![1, 2, 2, 1, 1, 4;
      3, 2, 3, 0, 4, 2;
      1, 3, 1, 1, 4, 3;
      2, 1, 3, 0, 4, 2;
      2, 2, 0, 3, 3, 4;
      0, 2, 2, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 6, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 1, 0, 0, 1, 1;
      3, 2, 2, 3, 4, 4;
      1, 4, 4, 3, 1, 4;
      4, 3, 3, 3, 4, 3;
      0, 3, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_884 : Certificate {2, 4, 5, 6, 8, 9} := by
  refine ⟨!![0, 4, 0, 2, 4, 4;
      2, 4, 1, 1, 2, 2;
      2, 3, 3, 1, 3, 0;
      4, 2, 2, 3, 3, 2;
      1, 4, 3, 4, 1, 4;
      4, 4, 0, 3, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 6, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 4, 2, 4, 4;
      2, 2, 2, 3, 4, 4;
      4, 4, 4, 3, 1, 4;
      0, 3, 3, 3, 4, 3;
      2, 3, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_888 : Certificate {3, 4, 5, 6, 8, 9} := by
  refine ⟨!![0, 4, 0, 2, 4, 4;
      4, 2, 4, 2, 2, 3;
      3, 0, 2, 3, 1, 1;
      3, 0, 3, 1, 0, 1;
      2, 2, 2, 4, 0, 1;
      4, 3, 0, 0, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 6, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 4, 2, 4, 4;
      2, 1, 0, 0, 1, 1;
      2, 4, 4, 3, 1, 4;
      3, 3, 3, 3, 4, 3;
      2, 3, 1, 1, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_903 : Certificate {0, 1, 2, 7, 8, 9} := by
  refine ⟨!![2, 2, 2, 4, 1, 2;
      3, 3, 2, 4, 0, 3;
      1, 2, 1, 4, 4, 1;
      4, 3, 3, 2, 4, 2;
      1, 3, 2, 1, 4, 0;
      2, 1, 2, 3, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 7, 8, 9} =
      !![0, 3, 2, 2, 4, 4;
      0, 2, 1, 4, 1, 3;
      0, 4, 0, 4, 4, 4;
      4, 2, 0, 3, 0, 2;
      4, 4, 0, 0, 4, 3;
      3, 0, 2, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_907 : Certificate {0, 1, 3, 7, 8, 9} := by
  refine ⟨!![4, 1, 2, 2, 4, 4;
      1, 4, 2, 1, 2, 1;
      2, 4, 1, 3, 3, 2;
      3, 1, 3, 3, 0, 1;
      4, 4, 3, 3, 1, 3;
      1, 4, 3, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 7, 8, 9} =
      !![0, 0, 2, 4, 1, 1;
      0, 2, 2, 4, 1, 3;
      0, 4, 2, 4, 4, 4;
      4, 2, 3, 3, 0, 2;
      4, 4, 3, 0, 4, 3;
      3, 0, 2, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_909 : Certificate {0, 2, 3, 7, 8, 9} := by
  refine ⟨!![0, 0, 4, 3, 1, 0;
      4, 4, 2, 1, 2, 1;
      1, 2, 0, 0, 2, 4;
      0, 4, 2, 0, 4, 3;
      1, 4, 3, 3, 1, 3;
      1, 1, 4, 2, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 7, 8, 9} =
      !![0, 0, 3, 1, 4, 4;
      0, 1, 2, 4, 1, 3;
      0, 0, 2, 4, 4, 4;
      4, 0, 3, 3, 0, 2;
      4, 0, 3, 0, 4, 3;
      3, 2, 2, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_910 : Certificate {1, 2, 3, 7, 8, 9} := by
  refine ⟨!![0, 0, 4, 3, 1, 0;
      3, 1, 0, 3, 3, 0;
      2, 0, 0, 4, 3, 0;
      0, 4, 4, 4, 2, 3;
      2, 2, 1, 3, 4, 4;
      2, 4, 0, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 7, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      2, 1, 2, 4, 1, 3;
      4, 0, 2, 4, 4, 4;
      2, 0, 3, 3, 0, 2;
      4, 0, 3, 0, 4, 3;
      0, 2, 2, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_915 : Certificate {0, 1, 4, 7, 8, 9} := by
  refine ⟨!![1, 0, 3, 0, 2, 1;
      1, 3, 0, 3, 4, 4;
      4, 1, 3, 0, 0, 0;
      1, 4, 1, 1, 3, 3;
      1, 1, 0, 0, 3, 1;
      2, 2, 3, 1, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 7, 8, 9} =
      !![0, 0, 1, 4, 1, 1;
      0, 3, 2, 2, 4, 4;
      0, 4, 0, 4, 4, 4;
      4, 2, 3, 3, 0, 2;
      4, 4, 3, 0, 4, 3;
      3, 0, 3, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_917 : Certificate {0, 2, 4, 7, 8, 9} := by
  refine ⟨!![4, 2, 2, 4, 4, 3;
      2, 0, 2, 1, 3, 3;
      3, 4, 1, 2, 1, 1;
      0, 1, 1, 3, 4, 4;
      0, 3, 0, 2, 4, 2;
      0, 1, 3, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 7, 8, 9} =
      !![0, 0, 2, 1, 4, 4;
      0, 2, 2, 2, 4, 4;
      0, 0, 0, 4, 4, 4;
      4, 0, 3, 3, 0, 2;
      4, 0, 3, 0, 4, 3;
      3, 2, 3, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_918 : Certificate {1, 2, 4, 7, 8, 9} := by
  refine ⟨!![1, 0, 4, 0, 0, 0;
      2, 4, 4, 4, 1, 4;
      2, 0, 0, 4, 3, 0;
      1, 1, 0, 3, 4, 4;
      1, 3, 4, 2, 4, 2;
      2, 1, 1, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 7, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 2, 4, 4;
      4, 0, 0, 4, 4, 4;
      2, 0, 3, 3, 0, 2;
      4, 0, 3, 0, 4, 3;
      0, 2, 3, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_921 : Certificate {0, 3, 4, 7, 8, 9} := by
  refine ⟨!![1, 1, 4, 3, 1, 0;
      4, 0, 4, 2, 1, 1;
      2, 2, 0, 0, 0, 0;
      4, 3, 0, 4, 2, 2;
      1, 4, 1, 2, 4, 2;
      3, 3, 1, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 7, 8, 9} =
      !![0, 3, 2, 1, 4, 4;
      0, 2, 1, 4, 1, 1;
      0, 2, 0, 4, 4, 4;
      4, 3, 3, 3, 0, 2;
      4, 3, 3, 0, 4, 3;
      3, 2, 3, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_922 : Certificate {1, 3, 4, 7, 8, 9} := by
  refine ⟨!![1, 2, 0, 0, 4, 2;
      0, 1, 3, 0, 2, 1;
      2, 4, 2, 4, 1, 4;
      3, 0, 4, 2, 0, 3;
      2, 2, 2, 4, 1, 1;
      4, 3, 4, 4, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 7, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 1, 4, 1, 1;
      4, 2, 0, 4, 4, 4;
      2, 3, 3, 3, 0, 2;
      4, 3, 3, 0, 4, 3;
      0, 2, 3, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_924 : Certificate {2, 3, 4, 7, 8, 9} := by
  refine ⟨!![4, 2, 3, 1, 3, 3;
      2, 0, 3, 0, 0, 0;
      0, 0, 2, 4, 3, 0;
      4, 3, 1, 1, 2, 0;
      4, 4, 3, 1, 3, 0;
      1, 3, 1, 3, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 7, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 2, 1, 4, 4;
      0, 2, 0, 4, 4, 4;
      0, 3, 3, 3, 0, 2;
      0, 3, 3, 0, 4, 3;
      2, 2, 3, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_931 : Certificate {0, 1, 5, 7, 8, 9} := by
  refine ⟨!![2, 4, 0, 0, 2, 1;
      2, 0, 1, 0, 1, 2;
      4, 3, 4, 3, 3, 2;
      2, 0, 4, 4, 1, 0;
      3, 0, 2, 4, 2, 2;
      0, 0, 2, 0, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 7, 8, 9} =
      !![0, 0, 0, 4, 1, 1;
      0, 3, 2, 2, 4, 4;
      0, 2, 0, 4, 1, 3;
      4, 2, 3, 3, 0, 2;
      4, 4, 3, 0, 4, 3;
      3, 0, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_933 : Certificate {0, 2, 5, 7, 8, 9} := by
  refine ⟨!![0, 4, 4, 0, 1, 4;
      4, 2, 1, 2, 2, 3;
      4, 0, 3, 0, 3, 1;
      4, 2, 4, 1, 2, 1;
      1, 3, 2, 2, 1, 1;
      3, 4, 4, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 7, 8, 9} =
      !![0, 0, 4, 1, 4, 4;
      0, 2, 2, 2, 4, 4;
      0, 1, 0, 4, 1, 3;
      4, 0, 3, 3, 0, 2;
      4, 0, 3, 0, 4, 3;
      3, 2, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_934 : Certificate {1, 2, 5, 7, 8, 9} := by
  refine ⟨!![0, 1, 1, 0, 4, 1;
      2, 0, 1, 1, 4, 0;
      2, 0, 0, 4, 3, 0;
      2, 1, 0, 0, 3, 4;
      3, 4, 1, 3, 0, 3;
      4, 0, 4, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 7, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 2, 4, 4;
      2, 1, 0, 4, 1, 3;
      2, 0, 3, 3, 0, 2;
      4, 0, 3, 0, 4, 3;
      0, 2, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_937 : Certificate {0, 3, 5, 7, 8, 9} := by
  refine ⟨!![2, 0, 2, 1, 2, 3;
      0, 4, 2, 0, 2, 4;
      4, 4, 0, 0, 0, 0;
      0, 4, 0, 4, 2, 2;
      0, 0, 3, 4, 3, 4;
      0, 2, 3, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 7, 8, 9} =
      !![0, 3, 4, 1, 4, 4;
      0, 2, 0, 4, 1, 1;
      0, 2, 0, 4, 1, 3;
      4, 3, 3, 3, 0, 2;
      4, 3, 3, 0, 4, 3;
      3, 2, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_938 : Certificate {1, 3, 5, 7, 8, 9} := by
  refine ⟨!![2, 2, 2, 1, 0, 2;
      1, 0, 3, 3, 2, 0;
      1, 0, 2, 1, 1, 0;
      3, 2, 3, 3, 2, 0;
      3, 3, 1, 3, 3, 2;
      3, 0, 1, 4, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 7, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 0, 4, 1, 1;
      2, 2, 0, 4, 1, 3;
      2, 3, 3, 3, 0, 2;
      4, 3, 3, 0, 4, 3;
      0, 2, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_940 : Certificate {2, 3, 5, 7, 8, 9} := by
  refine ⟨!![0, 4, 4, 2, 4, 1;
      1, 3, 1, 2, 0, 2;
      1, 2, 4, 2, 3, 3;
      1, 2, 3, 3, 4, 1;
      0, 1, 4, 2, 4, 3;
      3, 2, 3, 0, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 7, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 4, 1, 4, 4;
      1, 2, 0, 4, 1, 3;
      0, 3, 3, 3, 0, 2;
      0, 3, 3, 0, 4, 3;
      2, 2, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_945 : Certificate {0, 4, 5, 7, 8, 9} := by
  refine ⟨!![2, 1, 0, 1, 0, 4;
      2, 4, 1, 1, 3, 3;
      0, 1, 3, 3, 4, 4;
      4, 2, 2, 1, 3, 3;
      0, 4, 0, 4, 0, 3;
      2, 0, 1, 1, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 7, 8, 9} =
      !![0, 2, 4, 1, 4, 4;
      0, 1, 0, 4, 1, 1;
      0, 2, 2, 2, 4, 4;
      4, 3, 3, 3, 0, 2;
      4, 3, 3, 0, 4, 3;
      3, 3, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_946 : Certificate {1, 4, 5, 7, 8, 9} := by
  refine ⟨!![3, 4, 4, 4, 4, 3;
      0, 3, 1, 0, 3, 4;
      2, 2, 4, 4, 0, 1;
      2, 1, 3, 0, 4, 2;
      1, 2, 3, 2, 3, 4;
      1, 2, 4, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 7, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 1, 0, 4, 1, 1;
      3, 2, 2, 2, 4, 4;
      2, 3, 3, 3, 0, 2;
      4, 3, 3, 0, 4, 3;
      0, 3, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_948 : Certificate {2, 4, 5, 7, 8, 9} := by
  refine ⟨!![4, 1, 2, 0, 2, 1;
      1, 3, 4, 2, 1, 1;
      1, 2, 1, 2, 2, 4;
      4, 1, 4, 4, 0, 1;
      4, 3, 2, 0, 2, 3;
      1, 1, 4, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 7, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 4, 1, 4, 4;
      2, 2, 2, 2, 4, 4;
      0, 3, 3, 3, 0, 2;
      0, 3, 3, 0, 4, 3;
      2, 3, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_952 : Certificate {3, 4, 5, 7, 8, 9} := by
  refine ⟨!![0, 3, 4, 4, 0, 1;
      3, 2, 3, 0, 2, 1;
      4, 0, 3, 0, 1, 3;
      1, 4, 0, 4, 1, 4;
      0, 2, 0, 0, 0, 2;
      3, 4, 0, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 7, 8, 9} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 4, 1, 4, 4;
      2, 1, 0, 4, 1, 1;
      3, 3, 3, 3, 0, 2;
      3, 3, 3, 0, 4, 3;
      2, 3, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_963 : Certificate {0, 1, 6, 7, 8, 9} := by
  refine ⟨!![4, 2, 0, 4, 2, 1;
      1, 1, 1, 3, 1, 2;
      2, 3, 0, 4, 0, 0;
      2, 4, 2, 4, 2, 4;
      0, 2, 0, 3, 3, 1;
      3, 2, 2, 1, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 6, 7, 8, 9} =
      !![0, 0, 0, 4, 1, 1;
      0, 3, 3, 2, 4, 4;
      0, 2, 3, 4, 1, 3;
      0, 4, 3, 4, 4, 4;
      4, 4, 3, 0, 4, 3;
      3, 0, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_965 : Certificate {0, 2, 6, 7, 8, 9} := by
  refine ⟨!![3, 4, 0, 0, 2, 1;
      4, 3, 2, 4, 2, 4;
      2, 0, 4, 0, 4, 3;
      4, 0, 2, 2, 2, 4;
      1, 4, 3, 4, 1, 2;
      1, 1, 2, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 6, 7, 8, 9} =
      !![0, 0, 2, 1, 4, 4;
      0, 2, 3, 2, 4, 4;
      0, 1, 3, 4, 1, 3;
      0, 0, 3, 4, 4, 4;
      4, 0, 3, 0, 4, 3;
      3, 2, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_966 : Certificate {1, 2, 6, 7, 8, 9} := by
  refine ⟨!![3, 3, 3, 2, 2, 3;
      4, 0, 1, 0, 2, 0;
      3, 2, 2, 2, 3, 2;
      0, 3, 2, 2, 1, 1;
      1, 2, 4, 3, 1, 1;
      0, 3, 2, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 6, 7, 8, 9} =
      !![0, 0, 4, 4, 4, 4;
      3, 2, 3, 2, 4, 4;
      2, 1, 3, 4, 1, 3;
      4, 0, 3, 4, 4, 4;
      4, 0, 3, 0, 4, 3;
      0, 2, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_969 : Certificate {0, 3, 6, 7, 8, 9} := by
  refine ⟨!![0, 2, 3, 3, 0, 2;
      2, 1, 2, 0, 2, 4;
      3, 3, 0, 0, 0, 0;
      1, 1, 4, 2, 4, 3;
      4, 0, 2, 2, 0, 0;
      3, 0, 3, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 6, 7, 8, 9} =
      !![0, 3, 2, 1, 4, 4;
      0, 2, 0, 4, 1, 1;
      0, 2, 3, 4, 1, 3;
      0, 2, 3, 4, 4, 4;
      4, 3, 3, 0, 4, 3;
      3, 2, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_970 : Certificate {1, 3, 6, 7, 8, 9} := by
  refine ⟨!![0, 4, 1, 1, 0, 4;
      3, 0, 2, 0, 4, 0;
      2, 1, 3, 3, 3, 1;
      4, 4, 3, 1, 0, 2;
      1, 1, 4, 4, 4, 0;
      2, 4, 0, 2, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 6, 7, 8, 9} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 0, 4, 1, 1;
      2, 2, 3, 4, 1, 3;
      4, 2, 3, 4, 4, 4;
      4, 3, 3, 0, 4, 3;
      0, 2, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_972 : Certificate {2, 3, 6, 7, 8, 9} := by
  refine ⟨!![1, 1, 3, 3, 4, 4;
      1, 3, 1, 4, 1, 2;
      3, 1, 2, 2, 2, 4;
      1, 2, 3, 1, 3, 1;
      3, 2, 1, 1, 2, 2;
      2, 0, 4, 1, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 6, 7, 8, 9} =
      !![0, 0, 4, 4, 4, 4;
      0, 3, 2, 1, 4, 4;
      1, 2, 3, 4, 1, 3;
      0, 2, 3, 4, 4, 4;
      0, 3, 3, 0, 4, 3;
      2, 2, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_977 : Certificate {0, 4, 6, 7, 8, 9} := by
  refine ⟨!![4, 2, 3, 2, 2, 1;
      3, 1, 2, 1, 0, 0;
      1, 4, 2, 1, 0, 0;
      3, 1, 4, 4, 0, 0;
      2, 4, 0, 2, 3, 1;
      3, 2, 2, 1, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 6, 7, 8, 9} =
      !![0, 2, 2, 1, 4, 4;
      0, 1, 0, 4, 1, 1;
      0, 2, 3, 2, 4, 4;
      0, 0, 3, 4, 4, 4;
      4, 3, 3, 0, 4, 3;
      3, 3, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_978 : Certificate {1, 4, 6, 7, 8, 9} := by
  refine ⟨!![1, 4, 0, 1, 3, 4;
      0, 2, 1, 2, 1, 3;
      0, 1, 0, 3, 2, 1;
      2, 0, 3, 2, 2, 1;
      0, 3, 1, 1, 2, 3;
      2, 1, 1, 4, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 6, 7, 8, 9} =
      !![0, 0, 4, 4, 4, 4;
      0, 1, 0, 4, 1, 1;
      3, 2, 3, 2, 4, 4;
      4, 0, 3, 4, 4, 4;
      4, 3, 3, 0, 4, 3;
      0, 3, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_980 : Certificate {2, 4, 6, 7, 8, 9} := by
  refine ⟨!![3, 1, 2, 1, 2, 1;
      0, 1, 3, 0, 4, 2;
      1, 0, 0, 4, 0, 0;
      3, 2, 2, 4, 1, 3;
      2, 3, 2, 2, 2, 3;
      3, 0, 1, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 6, 7, 8, 9} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 2, 1, 4, 4;
      2, 2, 3, 2, 4, 4;
      0, 0, 3, 4, 4, 4;
      0, 3, 3, 0, 4, 3;
      2, 3, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_984 : Certificate {3, 4, 6, 7, 8, 9} := by
  refine ⟨!![3, 0, 2, 3, 4, 2;
      2, 2, 1, 0, 3, 4;
      2, 0, 4, 0, 3, 4;
      0, 1, 0, 3, 4, 2;
      3, 2, 1, 0, 2, 3;
      4, 2, 0, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 6, 7, 8, 9} =
      !![0, 0, 4, 4, 4, 4;
      3, 2, 2, 1, 4, 4;
      2, 1, 0, 4, 1, 1;
      2, 0, 3, 4, 4, 4;
      3, 3, 3, 0, 4, 3;
      2, 3, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_993 : Certificate {0, 5, 6, 7, 8, 9} := by
  refine ⟨!![0, 1, 4, 2, 4, 0;
      4, 2, 0, 4, 4, 3;
      0, 4, 0, 2, 2, 4;
      2, 0, 1, 1, 1, 2;
      2, 0, 1, 1, 4, 3;
      0, 1, 0, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 6, 7, 8, 9} =
      !![0, 4, 2, 1, 4, 4;
      0, 0, 0, 4, 1, 1;
      0, 2, 3, 2, 4, 4;
      0, 0, 3, 4, 1, 3;
      4, 3, 3, 0, 4, 3;
      3, 1, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_994 : Certificate {1, 5, 6, 7, 8, 9} := by
  refine ⟨!![0, 3, 2, 1, 2, 0;
      4, 0, 0, 1, 2, 0;
      0, 3, 1, 0, 3, 4;
      2, 3, 2, 0, 1, 3;
      2, 2, 3, 3, 0, 4;
      0, 2, 4, 2, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 6, 7, 8, 9} =
      !![0, 0, 4, 4, 4, 4;
      0, 0, 0, 4, 1, 1;
      3, 2, 3, 2, 4, 4;
      2, 0, 3, 4, 1, 3;
      4, 3, 3, 0, 4, 3;
      0, 1, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_996 : Certificate {2, 5, 6, 7, 8, 9} := by
  refine ⟨!![4, 1, 3, 1, 1, 2;
      0, 4, 2, 0, 1, 3;
      0, 0, 4, 4, 1, 4;
      2, 0, 0, 4, 4, 3;
      4, 3, 4, 2, 0, 0;
      3, 2, 2, 0, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 6, 7, 8, 9} =
      !![0, 0, 4, 4, 4, 4;
      0, 4, 2, 1, 4, 4;
      2, 2, 3, 2, 4, 4;
      1, 0, 3, 4, 1, 3;
      0, 3, 3, 0, 4, 3;
      2, 1, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1000 : Certificate {3, 5, 6, 7, 8, 9} := by
  refine ⟨!![4, 1, 3, 2, 3, 2;
      2, 2, 1, 0, 3, 4;
      1, 4, 1, 0, 4, 2;
      3, 4, 2, 2, 1, 1;
      4, 3, 4, 0, 1, 0;
      1, 4, 3, 3, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 6, 7, 8, 9} =
      !![0, 0, 4, 4, 4, 4;
      3, 4, 2, 1, 4, 4;
      2, 0, 0, 4, 1, 1;
      2, 0, 3, 4, 1, 3;
      3, 3, 3, 0, 4, 3;
      2, 1, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1008 : Certificate {4, 5, 6, 7, 8, 9} := by
  refine ⟨!![1, 4, 3, 4, 1, 3;
      1, 3, 3, 1, 2, 1;
      4, 1, 0, 2, 2, 1;
      3, 4, 1, 1, 2, 1;
      1, 1, 0, 3, 3, 1;
      1, 4, 4, 4, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 6, 7, 8, 9} =
      !![0, 0, 4, 4, 4, 4;
      2, 4, 2, 1, 4, 4;
      1, 0, 0, 4, 1, 1;
      2, 2, 3, 2, 4, 4;
      3, 3, 3, 0, 4, 3;
      3, 1, 1, 4, 4, 1] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 903 then
    if mask < 845 then
      if mask < 814 then
        if mask < 798 then
          if mask < 795 then
            if mask < 791 then
              ⟨{0, 1, 2, 3, 8, 9}, certificate_783⟩
            else
              ⟨{0, 1, 2, 4, 8, 9}, certificate_791⟩
          else
            if mask < 797 then
              ⟨{0, 1, 3, 4, 8, 9}, certificate_795⟩
            else
              ⟨{0, 2, 3, 4, 8, 9}, certificate_797⟩
        else
          if mask < 811 then
            if mask < 807 then
              ⟨{1, 2, 3, 4, 8, 9}, certificate_798⟩
            else
              ⟨{0, 1, 2, 5, 8, 9}, certificate_807⟩
          else
            if mask < 813 then
              ⟨{0, 1, 3, 5, 8, 9}, certificate_811⟩
            else
              ⟨{0, 2, 3, 5, 8, 9}, certificate_813⟩
      else
        if mask < 825 then
          if mask < 821 then
            if mask < 819 then
              ⟨{1, 2, 3, 5, 8, 9}, certificate_814⟩
            else
              ⟨{0, 1, 4, 5, 8, 9}, certificate_819⟩
          else
            if mask < 822 then
              ⟨{0, 2, 4, 5, 8, 9}, certificate_821⟩
            else
              ⟨{1, 2, 4, 5, 8, 9}, certificate_822⟩
        else
          if mask < 828 then
            if mask < 826 then
              ⟨{0, 3, 4, 5, 8, 9}, certificate_825⟩
            else
              ⟨{1, 3, 4, 5, 8, 9}, certificate_826⟩
          else
            if mask < 839 then
              ⟨{2, 3, 4, 5, 8, 9}, certificate_828⟩
            else
              if mask < 843 then
                ⟨{0, 1, 2, 6, 8, 9}, certificate_839⟩
              else
                ⟨{0, 1, 3, 6, 8, 9}, certificate_843⟩
    else
      if mask < 869 then
        if mask < 854 then
          if mask < 851 then
            if mask < 846 then
              ⟨{0, 2, 3, 6, 8, 9}, certificate_845⟩
            else
              ⟨{1, 2, 3, 6, 8, 9}, certificate_846⟩
          else
            if mask < 853 then
              ⟨{0, 1, 4, 6, 8, 9}, certificate_851⟩
            else
              ⟨{0, 2, 4, 6, 8, 9}, certificate_853⟩
        else
          if mask < 858 then
            if mask < 857 then
              ⟨{1, 2, 4, 6, 8, 9}, certificate_854⟩
            else
              ⟨{0, 3, 4, 6, 8, 9}, certificate_857⟩
          else
            if mask < 860 then
              ⟨{1, 3, 4, 6, 8, 9}, certificate_858⟩
            else
              if mask < 867 then
                ⟨{2, 3, 4, 6, 8, 9}, certificate_860⟩
              else
                ⟨{0, 1, 5, 6, 8, 9}, certificate_867⟩
      else
        if mask < 876 then
          if mask < 873 then
            if mask < 870 then
              ⟨{0, 2, 5, 6, 8, 9}, certificate_869⟩
            else
              ⟨{1, 2, 5, 6, 8, 9}, certificate_870⟩
          else
            if mask < 874 then
              ⟨{0, 3, 5, 6, 8, 9}, certificate_873⟩
            else
              ⟨{1, 3, 5, 6, 8, 9}, certificate_874⟩
        else
          if mask < 882 then
            if mask < 881 then
              ⟨{2, 3, 5, 6, 8, 9}, certificate_876⟩
            else
              ⟨{0, 4, 5, 6, 8, 9}, certificate_881⟩
          else
            if mask < 884 then
              ⟨{1, 4, 5, 6, 8, 9}, certificate_882⟩
            else
              if mask < 888 then
                ⟨{2, 4, 5, 6, 8, 9}, certificate_884⟩
              else
                ⟨{3, 4, 5, 6, 8, 9}, certificate_888⟩
  else
    if mask < 946 then
      if mask < 922 then
        if mask < 915 then
          if mask < 909 then
            if mask < 907 then
              ⟨{0, 1, 2, 7, 8, 9}, certificate_903⟩
            else
              ⟨{0, 1, 3, 7, 8, 9}, certificate_907⟩
          else
            if mask < 910 then
              ⟨{0, 2, 3, 7, 8, 9}, certificate_909⟩
            else
              ⟨{1, 2, 3, 7, 8, 9}, certificate_910⟩
        else
          if mask < 918 then
            if mask < 917 then
              ⟨{0, 1, 4, 7, 8, 9}, certificate_915⟩
            else
              ⟨{0, 2, 4, 7, 8, 9}, certificate_917⟩
          else
            if mask < 921 then
              ⟨{1, 2, 4, 7, 8, 9}, certificate_918⟩
            else
              ⟨{0, 3, 4, 7, 8, 9}, certificate_921⟩
      else
        if mask < 934 then
          if mask < 931 then
            if mask < 924 then
              ⟨{1, 3, 4, 7, 8, 9}, certificate_922⟩
            else
              ⟨{2, 3, 4, 7, 8, 9}, certificate_924⟩
          else
            if mask < 933 then
              ⟨{0, 1, 5, 7, 8, 9}, certificate_931⟩
            else
              ⟨{0, 2, 5, 7, 8, 9}, certificate_933⟩
        else
          if mask < 938 then
            if mask < 937 then
              ⟨{1, 2, 5, 7, 8, 9}, certificate_934⟩
            else
              ⟨{0, 3, 5, 7, 8, 9}, certificate_937⟩
          else
            if mask < 940 then
              ⟨{1, 3, 5, 7, 8, 9}, certificate_938⟩
            else
              if mask < 945 then
                ⟨{2, 3, 5, 7, 8, 9}, certificate_940⟩
              else
                ⟨{0, 4, 5, 7, 8, 9}, certificate_945⟩
    else
      if mask < 977 then
        if mask < 965 then
          if mask < 952 then
            if mask < 948 then
              ⟨{1, 4, 5, 7, 8, 9}, certificate_946⟩
            else
              ⟨{2, 4, 5, 7, 8, 9}, certificate_948⟩
          else
            if mask < 963 then
              ⟨{3, 4, 5, 7, 8, 9}, certificate_952⟩
            else
              ⟨{0, 1, 6, 7, 8, 9}, certificate_963⟩
        else
          if mask < 969 then
            if mask < 966 then
              ⟨{0, 2, 6, 7, 8, 9}, certificate_965⟩
            else
              ⟨{1, 2, 6, 7, 8, 9}, certificate_966⟩
          else
            if mask < 970 then
              ⟨{0, 3, 6, 7, 8, 9}, certificate_969⟩
            else
              if mask < 972 then
                ⟨{1, 3, 6, 7, 8, 9}, certificate_970⟩
              else
                ⟨{2, 3, 6, 7, 8, 9}, certificate_972⟩
      else
        if mask < 993 then
          if mask < 980 then
            if mask < 978 then
              ⟨{0, 4, 6, 7, 8, 9}, certificate_977⟩
            else
              ⟨{1, 4, 6, 7, 8, 9}, certificate_978⟩
          else
            if mask < 984 then
              ⟨{2, 4, 6, 7, 8, 9}, certificate_980⟩
            else
              ⟨{3, 4, 6, 7, 8, 9}, certificate_984⟩
        else
          if mask < 996 then
            if mask < 994 then
              ⟨{0, 5, 6, 7, 8, 9}, certificate_993⟩
            else
              ⟨{1, 5, 6, 7, 8, 9}, certificate_994⟩
          else
            if mask < 1000 then
              ⟨{2, 5, 6, 7, 8, 9}, certificate_996⟩
            else
              if mask < 1008 then
                ⟨{3, 5, 6, 7, 8, 9}, certificate_1000⟩
              else
                ⟨{4, 5, 6, 7, 8, 9}, certificate_1008⟩
end AMEProbe.QuinaryDirect.Batch03
#print axioms AMEProbe.QuinaryDirect.Batch03.lookup
