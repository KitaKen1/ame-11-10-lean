import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch12
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_3087 : Certificate {0, 1, 2, 3, 10, 11} := by
  refine ⟨!![1, 1, 4, 3, 1, 1;
      4, 3, 1, 4, 1, 4;
      3, 3, 0, 1, 0, 4;
      4, 1, 2, 1, 3, 4;
      1, 2, 2, 2, 3, 3;
      3, 1, 1, 1, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 10, 11} =
      !![0, 2, 1, 2, 3, 3;
      0, 4, 0, 2, 3, 1;
      4, 2, 0, 3, 3, 1;
      4, 1, 4, 2, 0, 4;
      4, 4, 1, 4, 4, 4;
      4, 4, 1, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3095 : Certificate {0, 1, 2, 4, 10, 11} := by
  refine ⟨!![4, 2, 1, 3, 4, 1;
      1, 2, 4, 4, 3, 4;
      3, 1, 1, 2, 4, 3;
      2, 0, 0, 2, 0, 3;
      3, 3, 4, 1, 1, 4;
      2, 4, 2, 1, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 10, 11} =
      !![0, 3, 2, 2, 3, 2;
      0, 4, 0, 0, 3, 1;
      4, 2, 0, 3, 3, 1;
      4, 1, 4, 4, 0, 4;
      4, 4, 1, 1, 4, 4;
      4, 4, 1, 3, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3099 : Certificate {0, 1, 3, 4, 10, 11} := by
  refine ⟨!![4, 0, 0, 2, 4, 3;
      1, 4, 0, 0, 3, 2;
      3, 2, 4, 0, 4, 2;
      1, 0, 4, 4, 2, 0;
      1, 1, 1, 4, 0, 0;
      2, 3, 4, 3, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 10, 11} =
      !![0, 0, 2, 1, 0, 2;
      0, 4, 2, 0, 3, 1;
      4, 2, 3, 3, 3, 1;
      4, 1, 2, 4, 0, 4;
      4, 4, 4, 1, 4, 4;
      4, 4, 4, 3, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3101 : Certificate {0, 2, 3, 4, 10, 11} := by
  refine ⟨!![0, 4, 0, 2, 2, 0;
      3, 0, 3, 3, 2, 2;
      2, 0, 1, 2, 3, 4;
      1, 1, 0, 0, 3, 2;
      2, 2, 3, 1, 0, 1;
      0, 0, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 10, 11} =
      !![0, 0, 3, 2, 4, 0;
      0, 0, 2, 0, 3, 1;
      4, 0, 3, 3, 3, 1;
      4, 4, 2, 4, 0, 4;
      4, 1, 4, 1, 4, 4;
      4, 1, 4, 3, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3102 : Certificate {1, 2, 3, 4, 10, 11} := by
  refine ⟨!![0, 4, 0, 2, 2, 0;
      1, 2, 4, 0, 0, 1;
      4, 0, 0, 1, 1, 0;
      2, 4, 2, 1, 1, 0;
      4, 4, 2, 1, 4, 2;
      0, 3, 4, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 10, 11} =
      !![0, 0, 0, 0, 4, 3;
      4, 0, 2, 0, 3, 1;
      2, 0, 3, 3, 3, 1;
      1, 4, 2, 4, 0, 4;
      4, 1, 4, 1, 4, 4;
      4, 1, 4, 3, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3111 : Certificate {0, 1, 2, 5, 10, 11} := by
  refine ⟨!![3, 2, 2, 0, 3, 4;
      0, 2, 0, 1, 2, 2;
      2, 1, 4, 0, 1, 0;
      3, 0, 0, 3, 0, 2;
      4, 3, 3, 4, 2, 1;
      2, 4, 4, 2, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 10, 11} =
      !![0, 3, 2, 2, 3, 2;
      0, 2, 1, 0, 3, 3;
      4, 2, 0, 3, 3, 1;
      4, 1, 4, 4, 0, 4;
      4, 4, 1, 4, 4, 4;
      4, 4, 1, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3115 : Certificate {0, 1, 3, 5, 10, 11} := by
  refine ⟨!![3, 0, 1, 3, 2, 3;
      1, 1, 0, 2, 3, 0;
      2, 3, 0, 2, 2, 1;
      1, 0, 4, 4, 2, 0;
      2, 4, 0, 1, 2, 2;
      1, 2, 0, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 10, 11} =
      !![0, 0, 2, 0, 0, 2;
      0, 2, 2, 0, 3, 3;
      4, 2, 3, 3, 3, 1;
      4, 1, 2, 4, 0, 4;
      4, 4, 4, 4, 4, 4;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3117 : Certificate {0, 2, 3, 5, 10, 11} := by
  refine ⟨!![1, 0, 0, 2, 0, 2;
      4, 2, 1, 0, 3, 1;
      0, 1, 0, 3, 1, 1;
      1, 2, 3, 2, 1, 4;
      3, 1, 2, 2, 2, 4;
      4, 3, 1, 1, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 10, 11} =
      !![0, 0, 3, 4, 4, 0;
      0, 1, 2, 0, 3, 3;
      4, 0, 3, 3, 3, 1;
      4, 4, 2, 4, 0, 4;
      4, 1, 4, 4, 4, 4;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3118 : Certificate {1, 2, 3, 5, 10, 11} := by
  refine ⟨!![4, 3, 1, 3, 2, 3;
      2, 1, 4, 1, 4, 2;
      3, 2, 2, 4, 0, 2;
      2, 1, 1, 4, 2, 1;
      2, 0, 0, 0, 3, 2;
      1, 0, 0, 0, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 10, 11} =
      !![0, 0, 0, 0, 4, 3;
      2, 1, 2, 0, 3, 3;
      2, 0, 3, 3, 3, 1;
      1, 4, 2, 4, 0, 4;
      4, 1, 4, 4, 4, 4;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3123 : Certificate {0, 1, 4, 5, 10, 11} := by
  refine ⟨!![1, 1, 3, 1, 3, 2;
      1, 3, 1, 2, 2, 0;
      3, 1, 2, 3, 1, 4;
      3, 4, 2, 1, 1, 1;
      4, 1, 2, 3, 2, 3;
      4, 2, 4, 1, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 10, 11} =
      !![0, 0, 1, 0, 0, 2;
      0, 3, 2, 2, 3, 2;
      4, 2, 3, 3, 3, 1;
      4, 1, 4, 4, 0, 4;
      4, 4, 1, 4, 4, 4;
      4, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3125 : Certificate {0, 2, 4, 5, 10, 11} := by
  refine ⟨!![0, 3, 2, 4, 1, 2;
      4, 0, 1, 4, 1, 4;
      1, 2, 3, 3, 4, 0;
      1, 0, 3, 1, 4, 2;
      0, 4, 3, 0, 4, 3;
      4, 0, 1, 2, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 10, 11} =
      !![0, 0, 2, 4, 4, 0;
      0, 2, 2, 2, 3, 2;
      4, 0, 3, 3, 3, 1;
      4, 4, 4, 4, 0, 4;
      4, 1, 1, 4, 4, 4;
      4, 1, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3126 : Certificate {1, 2, 4, 5, 10, 11} := by
  refine ⟨!![0, 2, 3, 1, 4, 3;
      2, 1, 3, 1, 0, 0;
      3, 2, 0, 4, 2, 3;
      3, 0, 0, 2, 2, 0;
      0, 2, 0, 4, 0, 0;
      2, 4, 0, 3, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 10, 11} =
      !![0, 0, 0, 0, 4, 3;
      3, 2, 2, 2, 3, 2;
      2, 0, 3, 3, 3, 1;
      1, 4, 4, 4, 0, 4;
      4, 1, 1, 4, 4, 4;
      4, 1, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3129 : Certificate {0, 3, 4, 5, 10, 11} := by
  refine ⟨!![3, 4, 3, 0, 1, 0;
      3, 0, 2, 3, 2, 3;
      3, 1, 2, 2, 4, 2;
      2, 0, 2, 2, 3, 3;
      2, 2, 3, 1, 1, 0;
      3, 0, 2, 1, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 10, 11} =
      !![0, 3, 2, 4, 4, 0;
      0, 2, 1, 0, 0, 2;
      4, 3, 3, 3, 3, 1;
      4, 2, 4, 4, 0, 4;
      4, 4, 1, 4, 4, 4;
      4, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3130 : Certificate {1, 3, 4, 5, 10, 11} := by
  refine ⟨!![3, 4, 2, 4, 1, 1;
      4, 3, 0, 0, 4, 1;
      0, 2, 4, 2, 3, 2;
      0, 4, 0, 2, 4, 3;
      2, 2, 4, 2, 1, 4;
      1, 4, 3, 4, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 10, 11} =
      !![0, 0, 0, 0, 4, 3;
      0, 2, 1, 0, 0, 2;
      2, 3, 3, 3, 3, 1;
      1, 2, 4, 4, 0, 4;
      4, 4, 1, 4, 4, 4;
      4, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3132 : Certificate {2, 3, 4, 5, 10, 11} := by
  refine ⟨!![4, 1, 2, 2, 0, 3;
      2, 1, 3, 4, 2, 2;
      0, 1, 0, 2, 0, 2;
      4, 3, 4, 4, 3, 1;
      2, 1, 0, 2, 3, 4;
      1, 2, 0, 4, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 10, 11} =
      !![0, 0, 0, 0, 4, 3;
      0, 3, 2, 4, 4, 0;
      0, 3, 3, 3, 3, 1;
      4, 2, 4, 4, 0, 4;
      1, 4, 1, 4, 4, 4;
      1, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3143 : Certificate {0, 1, 2, 6, 10, 11} := by
  refine ⟨!![0, 3, 4, 1, 0, 3;
      3, 2, 0, 4, 2, 4;
      4, 3, 3, 0, 0, 0;
      4, 0, 0, 4, 0, 1;
      0, 2, 1, 1, 0, 4;
      1, 1, 3, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 6, 10, 11} =
      !![0, 3, 2, 3, 3, 2;
      0, 2, 1, 3, 3, 3;
      0, 4, 0, 3, 3, 1;
      4, 1, 4, 3, 0, 4;
      4, 4, 1, 0, 4, 4;
      4, 4, 1, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3147 : Certificate {0, 1, 3, 6, 10, 11} := by
  refine ⟨!![4, 1, 1, 4, 4, 1;
      1, 3, 2, 1, 3, 1;
      2, 4, 1, 4, 2, 4;
      0, 2, 2, 4, 0, 1;
      2, 1, 2, 0, 2, 3;
      1, 1, 4, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 6, 10, 11} =
      !![0, 0, 2, 0, 0, 2;
      0, 2, 2, 3, 3, 3;
      0, 4, 2, 3, 3, 1;
      4, 1, 2, 3, 0, 4;
      4, 4, 4, 0, 4, 4;
      4, 4, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3149 : Certificate {0, 2, 3, 6, 10, 11} := by
  refine ⟨!![3, 0, 2, 2, 1, 1;
      4, 3, 2, 1, 2, 2;
      4, 1, 4, 3, 3, 4;
      4, 0, 4, 0, 2, 3;
      4, 3, 0, 4, 3, 3;
      3, 4, 1, 2, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 6, 10, 11} =
      !![0, 0, 3, 2, 4, 0;
      0, 1, 2, 3, 3, 3;
      0, 0, 2, 3, 3, 1;
      4, 4, 2, 3, 0, 4;
      4, 1, 4, 0, 4, 4;
      4, 1, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3150 : Certificate {1, 2, 3, 6, 10, 11} := by
  refine ⟨!![2, 2, 0, 4, 0, 2;
      1, 4, 1, 2, 4, 0;
      0, 1, 3, 2, 0, 1;
      1, 1, 3, 1, 4, 1;
      0, 3, 4, 3, 0, 0;
      4, 3, 4, 3, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 6, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      2, 1, 2, 3, 3, 3;
      4, 0, 2, 3, 3, 1;
      1, 4, 2, 3, 0, 4;
      4, 1, 4, 0, 4, 4;
      4, 1, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3155 : Certificate {0, 1, 4, 6, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 3;
      4, 3, 2, 2, 1, 2;
      4, 1, 4, 3, 4, 3;
      2, 2, 2, 3, 2, 0;
      4, 0, 3, 4, 4, 2;
      1, 2, 3, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 6, 10, 11} =
      !![0, 0, 1, 0, 0, 2;
      0, 3, 2, 3, 3, 2;
      0, 4, 0, 3, 3, 1;
      4, 1, 4, 3, 0, 4;
      4, 4, 1, 0, 4, 4;
      4, 4, 3, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3157 : Certificate {0, 2, 4, 6, 10, 11} := by
  refine ⟨!![2, 1, 1, 3, 3, 3;
      2, 0, 0, 2, 3, 0;
      2, 3, 2, 3, 1, 1;
      1, 3, 1, 3, 3, 4;
      0, 2, 1, 2, 3, 0;
      2, 0, 0, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 6, 10, 11} =
      !![0, 0, 2, 2, 4, 0;
      0, 2, 2, 3, 3, 2;
      0, 0, 0, 3, 3, 1;
      4, 4, 4, 3, 0, 4;
      4, 1, 1, 0, 4, 4;
      4, 1, 3, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3158 : Certificate {1, 2, 4, 6, 10, 11} := by
  refine ⟨!![2, 0, 4, 0, 0, 0;
      0, 4, 4, 4, 0, 2;
      2, 2, 0, 0, 3, 3;
      1, 0, 0, 4, 4, 0;
      2, 2, 0, 2, 3, 0;
      3, 4, 0, 2, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 6, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 3, 3, 2;
      4, 0, 0, 3, 3, 1;
      1, 4, 4, 3, 0, 4;
      4, 1, 1, 0, 4, 4;
      4, 1, 3, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3161 : Certificate {0, 3, 4, 6, 10, 11} := by
  refine ⟨!![0, 2, 2, 2, 3, 4;
      1, 0, 0, 1, 4, 0;
      1, 1, 0, 0, 1, 4;
      0, 1, 4, 0, 3, 2;
      4, 4, 3, 3, 0, 2;
      1, 0, 0, 4, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 6, 10, 11} =
      !![0, 3, 2, 2, 4, 0;
      0, 2, 1, 0, 0, 2;
      0, 2, 0, 3, 3, 1;
      4, 2, 4, 3, 0, 4;
      4, 4, 1, 0, 4, 4;
      4, 4, 3, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3162 : Certificate {1, 3, 4, 6, 10, 11} := by
  refine ⟨!![0, 4, 4, 4, 1, 3;
      4, 2, 0, 2, 3, 4;
      4, 1, 3, 4, 2, 4;
      0, 2, 0, 1, 2, 4;
      1, 2, 3, 2, 1, 3;
      4, 3, 1, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 6, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 1, 0, 0, 2;
      4, 2, 0, 3, 3, 1;
      1, 2, 4, 3, 0, 4;
      4, 4, 1, 0, 4, 4;
      4, 4, 3, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3164 : Certificate {2, 3, 4, 6, 10, 11} := by
  refine ⟨!![2, 2, 4, 2, 3, 0;
      4, 0, 3, 0, 0, 0;
      0, 1, 4, 4, 2, 2;
      0, 0, 3, 4, 4, 0;
      2, 1, 3, 1, 2, 4;
      1, 2, 2, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 6, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 2, 2, 4, 0;
      0, 2, 0, 3, 3, 1;
      4, 2, 4, 3, 0, 4;
      1, 4, 1, 0, 4, 4;
      1, 4, 3, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3171 : Certificate {0, 1, 5, 6, 10, 11} := by
  refine ⟨!![4, 2, 0, 4, 4, 1;
      2, 0, 0, 3, 4, 3;
      3, 3, 2, 1, 3, 1;
      1, 0, 4, 1, 1, 3;
      3, 0, 3, 2, 3, 0;
      3, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 6, 10, 11} =
      !![0, 0, 0, 0, 0, 2;
      0, 3, 2, 3, 3, 2;
      0, 2, 0, 3, 3, 3;
      4, 1, 4, 3, 0, 4;
      4, 4, 4, 0, 4, 4;
      4, 4, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3173 : Certificate {0, 2, 5, 6, 10, 11} := by
  refine ⟨!![1, 0, 2, 3, 2, 4;
      2, 1, 4, 0, 2, 3;
      0, 3, 2, 4, 2, 4;
      0, 0, 4, 2, 4, 4;
      4, 2, 1, 0, 1, 4;
      2, 1, 4, 3, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 6, 10, 11} =
      !![0, 0, 4, 2, 4, 0;
      0, 2, 2, 3, 3, 2;
      0, 1, 0, 3, 3, 3;
      4, 4, 4, 3, 0, 4;
      4, 1, 4, 0, 4, 4;
      4, 1, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3174 : Certificate {1, 2, 5, 6, 10, 11} := by
  refine ⟨!![1, 4, 2, 4, 1, 3;
      1, 0, 2, 3, 4, 3;
      4, 4, 0, 0, 1, 1;
      3, 2, 0, 4, 2, 3;
      1, 1, 0, 2, 4, 1;
      0, 1, 0, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 6, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 3, 3, 2;
      2, 1, 0, 3, 3, 3;
      1, 4, 4, 3, 0, 4;
      4, 1, 4, 0, 4, 4;
      4, 1, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3177 : Certificate {0, 3, 5, 6, 10, 11} := by
  refine ⟨!![1, 2, 2, 1, 1, 2;
      0, 4, 0, 1, 3, 1;
      4, 4, 0, 0, 4, 1;
      0, 4, 4, 3, 2, 0;
      0, 1, 3, 4, 4, 2;
      0, 4, 0, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 6, 10, 11} =
      !![0, 3, 4, 2, 4, 0;
      0, 2, 0, 0, 0, 2;
      0, 2, 0, 3, 3, 3;
      4, 2, 4, 3, 0, 4;
      4, 4, 4, 0, 4, 4;
      4, 4, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3178 : Certificate {1, 3, 5, 6, 10, 11} := by
  refine ⟨!![4, 2, 3, 0, 0, 0;
      2, 0, 4, 1, 3, 1;
      2, 2, 1, 1, 0, 3;
      4, 1, 2, 3, 2, 0;
      4, 3, 1, 4, 4, 2;
      3, 3, 1, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 6, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 0, 0, 0, 2;
      2, 2, 0, 3, 3, 3;
      1, 2, 4, 3, 0, 4;
      4, 4, 4, 0, 4, 4;
      4, 4, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3180 : Certificate {2, 3, 5, 6, 10, 11} := by
  refine ⟨!![1, 1, 4, 1, 1, 2;
      0, 3, 1, 4, 1, 2;
      3, 0, 3, 1, 0, 3;
      0, 3, 0, 1, 0, 1;
      2, 4, 0, 3, 3, 0;
      1, 4, 0, 3, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 6, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 4, 2, 4, 0;
      1, 2, 0, 3, 3, 3;
      4, 2, 4, 3, 0, 4;
      1, 4, 4, 0, 4, 4;
      1, 4, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3185 : Certificate {0, 4, 5, 6, 10, 11} := by
  refine ⟨!![0, 3, 2, 0, 2, 2;
      0, 1, 0, 4, 2, 4;
      4, 0, 0, 4, 1, 0;
      3, 3, 4, 4, 3, 3;
      1, 3, 3, 2, 4, 4;
      0, 0, 0, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 6, 10, 11} =
      !![0, 2, 4, 2, 4, 0;
      0, 1, 0, 0, 0, 2;
      0, 2, 2, 3, 3, 2;
      4, 4, 4, 3, 0, 4;
      4, 1, 4, 0, 4, 4;
      4, 3, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3186 : Certificate {1, 4, 5, 6, 10, 11} := by
  refine ⟨!![0, 4, 1, 0, 1, 1;
      0, 4, 2, 4, 4, 1;
      4, 2, 0, 2, 3, 4;
      3, 1, 0, 0, 3, 2;
      1, 2, 2, 4, 1, 4;
      0, 1, 4, 3, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 6, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 1, 0, 0, 0, 2;
      3, 2, 2, 3, 3, 2;
      1, 4, 4, 3, 0, 4;
      4, 1, 4, 0, 4, 4;
      4, 3, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3188 : Certificate {2, 4, 5, 6, 10, 11} := by
  refine ⟨!![4, 1, 2, 3, 4, 1;
      1, 4, 4, 1, 4, 4;
      2, 2, 1, 3, 3, 3;
      2, 1, 3, 3, 3, 4;
      4, 2, 3, 0, 1, 3;
      4, 1, 2, 1, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 6, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 4, 2, 4, 0;
      2, 2, 2, 3, 3, 2;
      4, 4, 4, 3, 0, 4;
      1, 1, 4, 0, 4, 4;
      1, 3, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3192 : Certificate {3, 4, 5, 6, 10, 11} := by
  refine ⟨!![2, 3, 1, 4, 1, 2;
      2, 3, 2, 3, 3, 1;
      2, 2, 1, 3, 2, 2;
      4, 4, 4, 2, 1, 3;
      1, 0, 4, 4, 4, 2;
      2, 3, 1, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 6, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 4, 2, 4, 0;
      2, 1, 0, 0, 0, 2;
      2, 4, 4, 3, 0, 4;
      4, 1, 4, 0, 4, 4;
      4, 3, 4, 2, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3207 : Certificate {0, 1, 2, 7, 10, 11} := by
  refine ⟨!![0, 4, 3, 3, 2, 4;
      4, 2, 0, 0, 2, 3;
      0, 4, 2, 3, 2, 0;
      2, 2, 3, 1, 4, 0;
      4, 2, 1, 0, 0, 0;
      4, 3, 1, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 7, 10, 11} =
      !![0, 3, 2, 2, 3, 2;
      0, 2, 1, 4, 3, 3;
      0, 4, 0, 4, 3, 1;
      4, 2, 0, 3, 3, 1;
      4, 4, 1, 1, 4, 4;
      4, 4, 1, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3211 : Certificate {0, 1, 3, 7, 10, 11} := by
  refine ⟨!![0, 2, 2, 4, 1, 4;
      4, 4, 3, 2, 4, 4;
      0, 1, 3, 2, 3, 0;
      2, 1, 1, 3, 4, 3;
      4, 2, 3, 3, 1, 1;
      4, 2, 0, 2, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 7, 10, 11} =
      !![0, 0, 2, 4, 0, 2;
      0, 2, 2, 4, 3, 3;
      0, 4, 2, 4, 3, 1;
      4, 2, 3, 3, 3, 1;
      4, 4, 4, 1, 4, 4;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3213 : Certificate {0, 2, 3, 7, 10, 11} := by
  refine ⟨!![1, 3, 1, 2, 2, 0;
      2, 2, 3, 1, 2, 2;
      2, 3, 1, 3, 0, 2;
      1, 0, 1, 0, 3, 2;
      1, 4, 4, 4, 3, 3;
      4, 2, 3, 2, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 7, 10, 11} =
      !![0, 0, 3, 1, 4, 0;
      0, 1, 2, 4, 3, 3;
      0, 0, 2, 4, 3, 1;
      4, 0, 3, 3, 3, 1;
      4, 1, 4, 1, 4, 4;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3214 : Certificate {1, 2, 3, 7, 10, 11} := by
  refine ⟨!![4, 2, 4, 2, 1, 2;
      0, 1, 1, 2, 3, 2;
      0, 2, 4, 4, 1, 2;
      2, 3, 2, 4, 4, 3;
      4, 3, 2, 4, 2, 0;
      4, 2, 3, 1, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 7, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      2, 1, 2, 4, 3, 3;
      4, 0, 2, 4, 3, 1;
      2, 0, 3, 3, 3, 1;
      4, 1, 4, 1, 4, 4;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3219 : Certificate {0, 1, 4, 7, 10, 11} := by
  refine ⟨!![3, 2, 0, 1, 2, 1;
      4, 0, 1, 4, 2, 4;
      1, 4, 3, 2, 4, 4;
      2, 0, 3, 1, 1, 3;
      0, 4, 0, 1, 4, 0;
      1, 3, 0, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 7, 10, 11} =
      !![0, 0, 1, 4, 0, 2;
      0, 3, 2, 2, 3, 2;
      0, 4, 0, 4, 3, 1;
      4, 2, 3, 3, 3, 1;
      4, 4, 1, 1, 4, 4;
      4, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3221 : Certificate {0, 2, 4, 7, 10, 11} := by
  refine ⟨!![0, 2, 3, 3, 3, 3;
      3, 3, 1, 0, 1, 4;
      4, 3, 2, 1, 4, 0;
      2, 2, 4, 4, 4, 2;
      4, 3, 3, 1, 2, 2;
      0, 3, 1, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 7, 10, 11} =
      !![0, 0, 2, 1, 4, 0;
      0, 2, 2, 2, 3, 2;
      0, 0, 0, 4, 3, 1;
      4, 0, 3, 3, 3, 1;
      4, 1, 1, 1, 4, 4;
      4, 1, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3222 : Certificate {1, 2, 4, 7, 10, 11} := by
  refine ⟨!![0, 4, 1, 1, 1, 1;
      2, 3, 1, 1, 2, 3;
      1, 4, 1, 3, 1, 1;
      3, 4, 2, 1, 1, 1;
      1, 3, 3, 4, 0, 4;
      0, 4, 0, 0, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 7, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 2, 3, 2;
      4, 0, 0, 4, 3, 1;
      2, 0, 3, 3, 3, 1;
      4, 1, 1, 1, 4, 4;
      4, 1, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3225 : Certificate {0, 3, 4, 7, 10, 11} := by
  refine ⟨!![3, 0, 4, 3, 4, 2;
      0, 4, 1, 4, 2, 4;
      1, 4, 2, 0, 0, 0;
      0, 1, 4, 0, 3, 2;
      1, 1, 1, 2, 4, 4;
      2, 0, 0, 1, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 7, 10, 11} =
      !![0, 3, 2, 1, 4, 0;
      0, 2, 1, 4, 0, 2;
      0, 2, 0, 4, 3, 1;
      4, 3, 3, 3, 3, 1;
      4, 4, 1, 1, 4, 4;
      4, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3226 : Certificate {1, 3, 4, 7, 10, 11} := by
  refine ⟨!![3, 1, 0, 2, 3, 0;
      2, 3, 1, 2, 4, 4;
      2, 3, 4, 2, 4, 1;
      2, 0, 4, 3, 0, 2;
      1, 3, 3, 0, 2, 0;
      3, 1, 4, 1, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 7, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 1, 4, 0, 2;
      4, 2, 0, 4, 3, 1;
      2, 3, 3, 3, 3, 1;
      4, 4, 1, 1, 4, 4;
      4, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3228 : Certificate {2, 3, 4, 7, 10, 11} := by
  refine ⟨!![0, 3, 4, 3, 4, 2;
      3, 3, 0, 4, 4, 1;
      3, 2, 0, 3, 1, 4;
      2, 4, 1, 2, 2, 3;
      2, 1, 1, 0, 1, 4;
      0, 0, 4, 4, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 7, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 2, 1, 4, 0;
      0, 2, 0, 4, 3, 1;
      0, 3, 3, 3, 3, 1;
      1, 4, 1, 1, 4, 4;
      1, 4, 3, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3235 : Certificate {0, 1, 5, 7, 10, 11} := by
  refine ⟨!![0, 0, 3, 1, 4, 4;
      4, 0, 3, 0, 1, 4;
      2, 3, 3, 0, 2, 3;
      0, 2, 1, 4, 1, 0;
      1, 3, 4, 1, 0, 4;
      3, 1, 3, 2, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 7, 10, 11} =
      !![0, 0, 0, 4, 0, 2;
      0, 3, 2, 2, 3, 2;
      0, 2, 0, 4, 3, 3;
      4, 2, 3, 3, 3, 1;
      4, 4, 4, 1, 4, 4;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3237 : Certificate {0, 2, 5, 7, 10, 11} := by
  refine ⟨!![4, 1, 3, 4, 0, 0;
      1, 4, 0, 2, 4, 4;
      0, 3, 4, 0, 4, 1;
      4, 3, 1, 2, 2, 1;
      3, 0, 2, 2, 3, 0;
      3, 3, 2, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 7, 10, 11} =
      !![0, 0, 4, 1, 4, 0;
      0, 2, 2, 2, 3, 2;
      0, 1, 0, 4, 3, 3;
      4, 0, 3, 3, 3, 1;
      4, 1, 4, 1, 4, 4;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3238 : Certificate {1, 2, 5, 7, 10, 11} := by
  refine ⟨!![3, 1, 3, 1, 3, 2;
      0, 0, 3, 1, 4, 4;
      4, 1, 3, 3, 3, 2;
      0, 2, 3, 3, 2, 1;
      2, 2, 3, 3, 0, 3;
      1, 3, 2, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 7, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 2, 3, 2;
      2, 1, 0, 4, 3, 3;
      2, 0, 3, 3, 3, 1;
      4, 1, 4, 1, 4, 4;
      4, 1, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3241 : Certificate {0, 3, 5, 7, 10, 11} := by
  refine ⟨!![0, 4, 1, 1, 0, 3;
      0, 1, 2, 0, 4, 1;
      3, 4, 2, 1, 2, 2;
      2, 0, 1, 3, 4, 3;
      3, 4, 0, 2, 4, 4;
      1, 2, 1, 4, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 7, 10, 11} =
      !![0, 3, 4, 1, 4, 0;
      0, 2, 0, 4, 0, 2;
      0, 2, 0, 4, 3, 3;
      4, 3, 3, 3, 3, 1;
      4, 4, 4, 1, 4, 4;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3242 : Certificate {1, 3, 5, 7, 10, 11} := by
  refine ⟨!![0, 4, 1, 1, 0, 3;
      0, 0, 3, 1, 4, 4;
      1, 4, 3, 2, 1, 4;
      4, 3, 2, 4, 0, 2;
      1, 3, 2, 4, 3, 4;
      2, 2, 3, 1, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 7, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 0, 4, 0, 2;
      2, 2, 0, 4, 3, 3;
      2, 3, 3, 3, 3, 1;
      4, 4, 4, 1, 4, 4;
      4, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3244 : Certificate {2, 3, 5, 7, 10, 11} := by
  refine ⟨!![3, 1, 3, 3, 2, 1;
      2, 4, 0, 3, 2, 3;
      4, 1, 0, 4, 3, 2;
      1, 4, 2, 4, 3, 0;
      3, 4, 2, 4, 1, 2;
      0, 1, 3, 1, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 7, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 4, 1, 4, 0;
      1, 2, 0, 4, 3, 3;
      0, 3, 3, 3, 3, 1;
      1, 4, 4, 1, 4, 4;
      1, 4, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3249 : Certificate {0, 4, 5, 7, 10, 11} := by
  refine ⟨!![4, 1, 1, 4, 4, 1;
      3, 0, 2, 1, 2, 2;
      4, 3, 4, 3, 2, 0;
      1, 2, 1, 1, 3, 1;
      2, 4, 1, 0, 0, 0;
      4, 4, 2, 0, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 7, 10, 11} =
      !![0, 2, 4, 1, 4, 0;
      0, 1, 0, 4, 0, 2;
      0, 2, 2, 2, 3, 2;
      4, 3, 3, 3, 3, 1;
      4, 1, 4, 1, 4, 4;
      4, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3250 : Certificate {1, 4, 5, 7, 10, 11} := by
  refine ⟨!![3, 0, 1, 0, 4, 3;
      4, 3, 3, 3, 1, 4;
      0, 2, 3, 4, 3, 4;
      4, 3, 0, 0, 4, 1;
      0, 1, 3, 3, 3, 2;
      0, 3, 1, 1, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 7, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 1, 0, 4, 0, 2;
      3, 2, 2, 2, 3, 2;
      2, 3, 3, 3, 3, 1;
      4, 1, 4, 1, 4, 4;
      4, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3252 : Certificate {2, 4, 5, 7, 10, 11} := by
  refine ⟨!![2, 0, 4, 0, 1, 2;
      4, 3, 0, 1, 4, 1;
      2, 2, 0, 1, 1, 4;
      1, 3, 1, 3, 3, 0;
      2, 1, 1, 4, 0, 3;
      3, 3, 4, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 7, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 4, 1, 4, 0;
      2, 2, 2, 2, 3, 2;
      0, 3, 3, 3, 3, 1;
      1, 1, 4, 1, 4, 4;
      1, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3256 : Certificate {3, 4, 5, 7, 10, 11} := by
  refine ⟨!![4, 3, 2, 3, 0, 1;
      1, 2, 1, 0, 4, 4;
      1, 0, 2, 4, 1, 0;
      0, 2, 1, 2, 4, 0;
      3, 4, 2, 2, 1, 1;
      3, 2, 1, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 7, 10, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 4, 1, 4, 0;
      2, 1, 0, 4, 0, 2;
      3, 3, 3, 3, 3, 1;
      4, 1, 4, 1, 4, 4;
      4, 3, 4, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3267 : Certificate {0, 1, 6, 7, 10, 11} := by
  refine ⟨!![2, 3, 3, 1, 2, 2;
      3, 1, 4, 0, 0, 0;
      3, 2, 2, 0, 3, 2;
      0, 2, 4, 4, 0, 0;
      2, 2, 0, 1, 2, 3;
      3, 1, 2, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 6, 7, 10, 11} =
      !![0, 0, 0, 4, 0, 2;
      0, 3, 3, 2, 3, 2;
      0, 2, 3, 4, 3, 3;
      0, 4, 3, 4, 3, 1;
      4, 4, 0, 1, 4, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3269 : Certificate {0, 2, 6, 7, 10, 11} := by
  refine ⟨!![3, 1, 4, 2, 0, 4;
      3, 2, 2, 1, 3, 2;
      0, 1, 3, 0, 3, 2;
      1, 1, 3, 1, 1, 4;
      0, 3, 4, 1, 2, 3;
      1, 4, 2, 4, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 6, 7, 10, 11} =
      !![0, 0, 2, 1, 4, 0;
      0, 2, 3, 2, 3, 2;
      0, 1, 3, 4, 3, 3;
      0, 0, 3, 4, 3, 1;
      4, 1, 0, 1, 4, 4;
      4, 1, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3270 : Certificate {1, 2, 6, 7, 10, 11} := by
  refine ⟨!![3, 1, 0, 4, 4, 4;
      3, 2, 3, 3, 2, 2;
      3, 2, 3, 4, 2, 1;
      1, 1, 0, 0, 4, 4;
      2, 2, 4, 2, 3, 4;
      4, 0, 4, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 6, 7, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 3, 2, 3, 2;
      2, 1, 3, 4, 3, 3;
      4, 0, 3, 4, 3, 1;
      4, 1, 0, 1, 4, 4;
      4, 1, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3273 : Certificate {0, 3, 6, 7, 10, 11} := by
  refine ⟨!![1, 1, 4, 3, 3, 1;
      4, 2, 2, 3, 4, 1;
      2, 3, 0, 4, 0, 0;
      3, 3, 0, 0, 3, 2;
      3, 0, 1, 2, 0, 0;
      0, 0, 3, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 6, 7, 10, 11} =
      !![0, 3, 2, 1, 4, 0;
      0, 2, 0, 4, 0, 2;
      0, 2, 3, 4, 3, 3;
      0, 2, 3, 4, 3, 1;
      4, 4, 0, 1, 4, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3274 : Certificate {1, 3, 6, 7, 10, 11} := by
  refine ⟨!![1, 3, 0, 1, 4, 4;
      3, 2, 1, 4, 4, 4;
      1, 4, 2, 4, 3, 2;
      3, 4, 3, 4, 1, 1;
      3, 1, 4, 1, 3, 4;
      1, 3, 3, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 6, 7, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 0, 4, 0, 2;
      2, 2, 3, 4, 3, 3;
      4, 2, 3, 4, 3, 1;
      4, 4, 0, 1, 4, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3276 : Certificate {2, 3, 6, 7, 10, 11} := by
  refine ⟨!![4, 3, 2, 3, 0, 4;
      1, 4, 2, 4, 3, 0;
      1, 1, 1, 2, 1, 3;
      1, 2, 1, 3, 4, 0;
      1, 0, 4, 4, 0, 1;
      3, 1, 2, 3, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 6, 7, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 3, 2, 1, 4, 0;
      1, 2, 3, 4, 3, 3;
      0, 2, 3, 4, 3, 1;
      1, 4, 0, 1, 4, 4;
      1, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3281 : Certificate {0, 4, 6, 7, 10, 11} := by
  refine ⟨!![3, 2, 0, 2, 0, 4;
      2, 4, 1, 4, 2, 3;
      3, 0, 3, 1, 1, 4;
      2, 1, 2, 3, 2, 3;
      1, 4, 0, 3, 3, 2;
      0, 4, 3, 2, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 6, 7, 10, 11} =
      !![0, 2, 2, 1, 4, 0;
      0, 1, 0, 4, 0, 2;
      0, 2, 3, 2, 3, 2;
      0, 0, 3, 4, 3, 1;
      4, 1, 0, 1, 4, 4;
      4, 3, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3282 : Certificate {1, 4, 6, 7, 10, 11} := by
  refine ⟨!![4, 1, 4, 3, 4, 4;
      3, 3, 4, 2, 0, 0;
      4, 4, 2, 2, 0, 4;
      2, 1, 4, 4, 4, 4;
      4, 1, 4, 2, 2, 3;
      2, 2, 0, 1, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 6, 7, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 1, 0, 4, 0, 2;
      3, 2, 3, 2, 3, 2;
      4, 0, 3, 4, 3, 1;
      4, 1, 0, 1, 4, 4;
      4, 3, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3284 : Certificate {2, 4, 6, 7, 10, 11} := by
  refine ⟨!![1, 4, 1, 3, 1, 3;
      1, 0, 2, 3, 3, 3;
      4, 4, 2, 3, 0, 1;
      3, 0, 0, 1, 0, 0;
      3, 2, 3, 3, 1, 3;
      2, 2, 0, 4, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 6, 7, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 2, 2, 1, 4, 0;
      2, 2, 3, 2, 3, 2;
      0, 0, 3, 4, 3, 1;
      1, 1, 0, 1, 4, 4;
      1, 3, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3288 : Certificate {3, 4, 6, 7, 10, 11} := by
  refine ⟨!![0, 1, 4, 4, 0, 3;
      4, 0, 2, 4, 1, 1;
      2, 2, 4, 1, 3, 3;
      3, 3, 2, 3, 0, 4;
      0, 4, 1, 0, 3, 1;
      2, 3, 4, 3, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 6, 7, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 2, 2, 1, 4, 0;
      2, 1, 0, 4, 0, 2;
      2, 0, 3, 4, 3, 1;
      4, 1, 0, 1, 4, 4;
      4, 3, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3297 : Certificate {0, 5, 6, 7, 10, 11} := by
  refine ⟨!![2, 3, 3, 4, 4, 0;
      0, 4, 3, 2, 0, 0;
      0, 2, 0, 4, 3, 2;
      3, 0, 4, 1, 3, 2;
      2, 0, 1, 2, 4, 1;
      4, 3, 2, 3, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 6, 7, 10, 11} =
      !![0, 4, 2, 1, 4, 0;
      0, 0, 0, 4, 0, 2;
      0, 2, 3, 2, 3, 2;
      0, 0, 3, 4, 3, 3;
      4, 4, 0, 1, 4, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3298 : Certificate {1, 5, 6, 7, 10, 11} := by
  refine ⟨!![1, 1, 2, 2, 2, 2;
      2, 1, 2, 1, 4, 4;
      2, 4, 4, 3, 2, 1;
      3, 1, 3, 1, 3, 3;
      1, 3, 0, 0, 2, 3;
      4, 1, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 6, 7, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 0, 0, 4, 0, 2;
      3, 2, 3, 2, 3, 2;
      2, 0, 3, 4, 3, 3;
      4, 4, 0, 1, 4, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3300 : Certificate {2, 5, 6, 7, 10, 11} := by
  refine ⟨!![3, 3, 3, 2, 2, 1;
      2, 1, 1, 3, 1, 4;
      1, 3, 4, 2, 1, 4;
      3, 1, 2, 3, 0, 3;
      3, 0, 4, 4, 1, 2;
      1, 3, 0, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 6, 7, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      0, 4, 2, 1, 4, 0;
      2, 2, 3, 2, 3, 2;
      1, 0, 3, 4, 3, 3;
      1, 4, 0, 1, 4, 4;
      1, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3304 : Certificate {3, 5, 6, 7, 10, 11} := by
  refine ⟨!![2, 4, 3, 2, 2, 4;
      3, 4, 3, 1, 4, 1;
      1, 2, 1, 0, 4, 4;
      4, 0, 2, 3, 0, 0;
      4, 1, 0, 3, 0, 4;
      0, 1, 1, 2, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 6, 7, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      3, 4, 2, 1, 4, 0;
      2, 0, 0, 4, 0, 2;
      2, 0, 3, 4, 3, 3;
      4, 4, 0, 1, 4, 4;
      4, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3312 : Certificate {4, 5, 6, 7, 10, 11} := by
  refine ⟨!![3, 2, 1, 4, 0, 1;
      3, 1, 1, 3, 3, 1;
      3, 0, 0, 1, 4, 3;
      0, 0, 3, 2, 2, 2;
      4, 2, 4, 4, 2, 4;
      1, 4, 4, 4, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 6, 7, 10, 11} =
      !![0, 0, 4, 4, 4, 3;
      2, 4, 2, 1, 4, 0;
      1, 0, 0, 4, 0, 2;
      2, 2, 3, 2, 3, 2;
      1, 4, 0, 1, 4, 4;
      3, 4, 2, 4, 3, 1] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 3207 then
    if mask < 3149 then
      if mask < 3118 then
        if mask < 3102 then
          if mask < 3099 then
            if mask < 3095 then
              ⟨{0, 1, 2, 3, 10, 11}, certificate_3087⟩
            else
              ⟨{0, 1, 2, 4, 10, 11}, certificate_3095⟩
          else
            if mask < 3101 then
              ⟨{0, 1, 3, 4, 10, 11}, certificate_3099⟩
            else
              ⟨{0, 2, 3, 4, 10, 11}, certificate_3101⟩
        else
          if mask < 3115 then
            if mask < 3111 then
              ⟨{1, 2, 3, 4, 10, 11}, certificate_3102⟩
            else
              ⟨{0, 1, 2, 5, 10, 11}, certificate_3111⟩
          else
            if mask < 3117 then
              ⟨{0, 1, 3, 5, 10, 11}, certificate_3115⟩
            else
              ⟨{0, 2, 3, 5, 10, 11}, certificate_3117⟩
      else
        if mask < 3129 then
          if mask < 3125 then
            if mask < 3123 then
              ⟨{1, 2, 3, 5, 10, 11}, certificate_3118⟩
            else
              ⟨{0, 1, 4, 5, 10, 11}, certificate_3123⟩
          else
            if mask < 3126 then
              ⟨{0, 2, 4, 5, 10, 11}, certificate_3125⟩
            else
              ⟨{1, 2, 4, 5, 10, 11}, certificate_3126⟩
        else
          if mask < 3132 then
            if mask < 3130 then
              ⟨{0, 3, 4, 5, 10, 11}, certificate_3129⟩
            else
              ⟨{1, 3, 4, 5, 10, 11}, certificate_3130⟩
          else
            if mask < 3143 then
              ⟨{2, 3, 4, 5, 10, 11}, certificate_3132⟩
            else
              if mask < 3147 then
                ⟨{0, 1, 2, 6, 10, 11}, certificate_3143⟩
              else
                ⟨{0, 1, 3, 6, 10, 11}, certificate_3147⟩
    else
      if mask < 3173 then
        if mask < 3158 then
          if mask < 3155 then
            if mask < 3150 then
              ⟨{0, 2, 3, 6, 10, 11}, certificate_3149⟩
            else
              ⟨{1, 2, 3, 6, 10, 11}, certificate_3150⟩
          else
            if mask < 3157 then
              ⟨{0, 1, 4, 6, 10, 11}, certificate_3155⟩
            else
              ⟨{0, 2, 4, 6, 10, 11}, certificate_3157⟩
        else
          if mask < 3162 then
            if mask < 3161 then
              ⟨{1, 2, 4, 6, 10, 11}, certificate_3158⟩
            else
              ⟨{0, 3, 4, 6, 10, 11}, certificate_3161⟩
          else
            if mask < 3164 then
              ⟨{1, 3, 4, 6, 10, 11}, certificate_3162⟩
            else
              if mask < 3171 then
                ⟨{2, 3, 4, 6, 10, 11}, certificate_3164⟩
              else
                ⟨{0, 1, 5, 6, 10, 11}, certificate_3171⟩
      else
        if mask < 3180 then
          if mask < 3177 then
            if mask < 3174 then
              ⟨{0, 2, 5, 6, 10, 11}, certificate_3173⟩
            else
              ⟨{1, 2, 5, 6, 10, 11}, certificate_3174⟩
          else
            if mask < 3178 then
              ⟨{0, 3, 5, 6, 10, 11}, certificate_3177⟩
            else
              ⟨{1, 3, 5, 6, 10, 11}, certificate_3178⟩
        else
          if mask < 3186 then
            if mask < 3185 then
              ⟨{2, 3, 5, 6, 10, 11}, certificate_3180⟩
            else
              ⟨{0, 4, 5, 6, 10, 11}, certificate_3185⟩
          else
            if mask < 3188 then
              ⟨{1, 4, 5, 6, 10, 11}, certificate_3186⟩
            else
              if mask < 3192 then
                ⟨{2, 4, 5, 6, 10, 11}, certificate_3188⟩
              else
                ⟨{3, 4, 5, 6, 10, 11}, certificate_3192⟩
  else
    if mask < 3250 then
      if mask < 3226 then
        if mask < 3219 then
          if mask < 3213 then
            if mask < 3211 then
              ⟨{0, 1, 2, 7, 10, 11}, certificate_3207⟩
            else
              ⟨{0, 1, 3, 7, 10, 11}, certificate_3211⟩
          else
            if mask < 3214 then
              ⟨{0, 2, 3, 7, 10, 11}, certificate_3213⟩
            else
              ⟨{1, 2, 3, 7, 10, 11}, certificate_3214⟩
        else
          if mask < 3222 then
            if mask < 3221 then
              ⟨{0, 1, 4, 7, 10, 11}, certificate_3219⟩
            else
              ⟨{0, 2, 4, 7, 10, 11}, certificate_3221⟩
          else
            if mask < 3225 then
              ⟨{1, 2, 4, 7, 10, 11}, certificate_3222⟩
            else
              ⟨{0, 3, 4, 7, 10, 11}, certificate_3225⟩
      else
        if mask < 3238 then
          if mask < 3235 then
            if mask < 3228 then
              ⟨{1, 3, 4, 7, 10, 11}, certificate_3226⟩
            else
              ⟨{2, 3, 4, 7, 10, 11}, certificate_3228⟩
          else
            if mask < 3237 then
              ⟨{0, 1, 5, 7, 10, 11}, certificate_3235⟩
            else
              ⟨{0, 2, 5, 7, 10, 11}, certificate_3237⟩
        else
          if mask < 3242 then
            if mask < 3241 then
              ⟨{1, 2, 5, 7, 10, 11}, certificate_3238⟩
            else
              ⟨{0, 3, 5, 7, 10, 11}, certificate_3241⟩
          else
            if mask < 3244 then
              ⟨{1, 3, 5, 7, 10, 11}, certificate_3242⟩
            else
              if mask < 3249 then
                ⟨{2, 3, 5, 7, 10, 11}, certificate_3244⟩
              else
                ⟨{0, 4, 5, 7, 10, 11}, certificate_3249⟩
    else
      if mask < 3281 then
        if mask < 3269 then
          if mask < 3256 then
            if mask < 3252 then
              ⟨{1, 4, 5, 7, 10, 11}, certificate_3250⟩
            else
              ⟨{2, 4, 5, 7, 10, 11}, certificate_3252⟩
          else
            if mask < 3267 then
              ⟨{3, 4, 5, 7, 10, 11}, certificate_3256⟩
            else
              ⟨{0, 1, 6, 7, 10, 11}, certificate_3267⟩
        else
          if mask < 3273 then
            if mask < 3270 then
              ⟨{0, 2, 6, 7, 10, 11}, certificate_3269⟩
            else
              ⟨{1, 2, 6, 7, 10, 11}, certificate_3270⟩
          else
            if mask < 3274 then
              ⟨{0, 3, 6, 7, 10, 11}, certificate_3273⟩
            else
              if mask < 3276 then
                ⟨{1, 3, 6, 7, 10, 11}, certificate_3274⟩
              else
                ⟨{2, 3, 6, 7, 10, 11}, certificate_3276⟩
      else
        if mask < 3297 then
          if mask < 3284 then
            if mask < 3282 then
              ⟨{0, 4, 6, 7, 10, 11}, certificate_3281⟩
            else
              ⟨{1, 4, 6, 7, 10, 11}, certificate_3282⟩
          else
            if mask < 3288 then
              ⟨{2, 4, 6, 7, 10, 11}, certificate_3284⟩
            else
              ⟨{3, 4, 6, 7, 10, 11}, certificate_3288⟩
        else
          if mask < 3300 then
            if mask < 3298 then
              ⟨{0, 5, 6, 7, 10, 11}, certificate_3297⟩
            else
              ⟨{1, 5, 6, 7, 10, 11}, certificate_3298⟩
          else
            if mask < 3304 then
              ⟨{2, 5, 6, 7, 10, 11}, certificate_3300⟩
            else
              if mask < 3312 then
                ⟨{3, 5, 6, 7, 10, 11}, certificate_3304⟩
              else
                ⟨{4, 5, 6, 7, 10, 11}, certificate_3312⟩
end AMEProbe.QuinaryDirect.Batch12
#print axioms AMEProbe.QuinaryDirect.Batch12.lookup
