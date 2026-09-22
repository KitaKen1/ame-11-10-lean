import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch08
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_2079 : Certificate {0, 1, 2, 3, 4, 11} := by
  refine ⟨!![4, 0, 4, 3, 1, 1;
      0, 0, 3, 4, 4, 4;
      2, 1, 2, 1, 2, 4;
      3, 3, 2, 1, 1, 3;
      0, 1, 1, 0, 1, 2;
      0, 4, 4, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 4, 11} =
      !![0, 4, 0, 2, 0, 1;
      4, 2, 0, 3, 3, 1;
      4, 1, 4, 2, 4, 4;
      4, 4, 1, 4, 1, 4;
      4, 4, 1, 4, 3, 1;
      4, 4, 0, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2095 : Certificate {0, 1, 2, 3, 5, 11} := by
  refine ⟨!![3, 4, 3, 2, 3, 2;
      0, 2, 0, 4, 1, 3;
      4, 3, 4, 3, 3, 2;
      1, 4, 3, 4, 3, 1;
      0, 3, 3, 0, 3, 1;
      0, 0, 0, 2, 3, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 5, 11} =
      !![0, 2, 1, 2, 0, 3;
      4, 2, 0, 3, 3, 1;
      4, 1, 4, 2, 4, 4;
      4, 4, 1, 4, 4, 4;
      4, 4, 1, 4, 4, 1;
      4, 4, 0, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2103 : Certificate {0, 1, 2, 4, 5, 11} := by
  refine ⟨!![2, 0, 4, 0, 0, 0;
      4, 3, 0, 4, 3, 0;
      1, 1, 2, 2, 4, 1;
      3, 2, 0, 0, 4, 4;
      1, 2, 3, 0, 1, 4;
      2, 3, 0, 2, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 5, 11} =
      !![0, 3, 2, 2, 2, 2;
      4, 2, 0, 3, 3, 1;
      4, 1, 4, 4, 4, 4;
      4, 4, 1, 1, 4, 4;
      4, 4, 1, 3, 4, 1;
      4, 4, 0, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2107 : Certificate {0, 1, 3, 4, 5, 11} := by
  refine ⟨!![0, 3, 0, 1, 2, 3;
      1, 3, 1, 1, 3, 2;
      4, 1, 1, 0, 4, 4;
      2, 2, 2, 4, 4, 3;
      4, 2, 2, 3, 1, 2;
      3, 3, 3, 3, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 5, 11} =
      !![0, 0, 2, 1, 0, 2;
      4, 2, 3, 3, 3, 1;
      4, 1, 2, 4, 4, 4;
      4, 4, 4, 1, 4, 4;
      4, 4, 4, 3, 4, 1;
      4, 4, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2109 : Certificate {0, 2, 3, 4, 5, 11} := by
  refine ⟨!![1, 4, 2, 3, 4, 1;
      3, 3, 1, 1, 1, 4;
      2, 1, 1, 0, 1, 2;
      0, 1, 0, 2, 3, 4;
      0, 0, 3, 4, 4, 4;
      0, 4, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 5, 11} =
      !![0, 0, 3, 2, 4, 0;
      4, 0, 3, 3, 3, 1;
      4, 4, 2, 4, 4, 4;
      4, 1, 4, 1, 4, 4;
      4, 1, 4, 3, 4, 1;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2110 : Certificate {1, 2, 3, 4, 5, 11} := by
  refine ⟨!![4, 2, 0, 0, 0, 3;
      0, 1, 0, 2, 4, 1;
      1, 1, 2, 4, 3, 2;
      3, 0, 0, 2, 3, 0;
      1, 3, 3, 4, 4, 1;
      2, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 5, 11} =
      !![0, 0, 0, 0, 0, 3;
      2, 0, 3, 3, 3, 1;
      1, 4, 2, 4, 4, 4;
      4, 1, 4, 1, 4, 4;
      4, 1, 4, 3, 4, 1;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2127 : Certificate {0, 1, 2, 3, 6, 11} := by
  refine ⟨!![4, 2, 4, 0, 0, 0;
      4, 3, 3, 1, 3, 3;
      2, 1, 1, 2, 3, 4;
      3, 4, 4, 0, 1, 0;
      4, 3, 0, 2, 4, 4;
      1, 2, 0, 0, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 6, 11} =
      !![0, 2, 1, 2, 3, 3;
      0, 4, 0, 2, 3, 1;
      4, 1, 4, 2, 3, 4;
      4, 4, 1, 4, 0, 4;
      4, 4, 1, 4, 2, 1;
      4, 4, 0, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2135 : Certificate {0, 1, 2, 4, 6, 11} := by
  refine ⟨!![3, 3, 4, 1, 2, 2;
      3, 4, 3, 2, 0, 0;
      2, 2, 3, 1, 4, 2;
      3, 3, 2, 1, 0, 2;
      3, 4, 0, 3, 1, 1;
      4, 3, 3, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 6, 11} =
      !![0, 3, 2, 2, 3, 2;
      0, 4, 0, 0, 3, 1;
      4, 1, 4, 4, 3, 4;
      4, 4, 1, 1, 0, 4;
      4, 4, 1, 3, 2, 1;
      4, 4, 0, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2139 : Certificate {0, 1, 3, 4, 6, 11} := by
  refine ⟨!![3, 1, 0, 0, 0, 4;
      3, 2, 4, 1, 3, 2;
      4, 3, 4, 4, 2, 0;
      1, 2, 1, 3, 2, 4;
      3, 2, 1, 2, 4, 3;
      1, 1, 3, 2, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 6, 11} =
      !![0, 0, 2, 1, 0, 2;
      0, 4, 2, 0, 3, 1;
      4, 1, 2, 4, 3, 4;
      4, 4, 4, 1, 0, 4;
      4, 4, 4, 3, 2, 1;
      4, 4, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2141 : Certificate {0, 2, 3, 4, 6, 11} := by
  refine ⟨!![0, 4, 1, 4, 2, 2;
      1, 3, 4, 3, 2, 1;
      3, 1, 4, 0, 4, 2;
      1, 1, 2, 4, 3, 1;
      0, 0, 2, 1, 1, 1;
      4, 4, 1, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 6, 11} =
      !![0, 0, 3, 2, 2, 0;
      0, 0, 2, 0, 3, 1;
      4, 4, 2, 4, 3, 4;
      4, 1, 4, 1, 0, 4;
      4, 1, 4, 3, 2, 1;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2142 : Certificate {1, 2, 3, 4, 6, 11} := by
  refine ⟨!![0, 1, 4, 1, 3, 3;
      3, 2, 1, 3, 4, 2;
      4, 1, 2, 3, 4, 4;
      3, 2, 2, 1, 1, 3;
      0, 1, 1, 2, 4, 4;
      2, 2, 2, 4, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 6, 11} =
      !![0, 0, 0, 0, 4, 3;
      4, 0, 2, 0, 3, 1;
      1, 4, 2, 4, 3, 4;
      4, 1, 4, 1, 0, 4;
      4, 1, 4, 3, 2, 1;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2151 : Certificate {0, 1, 2, 5, 6, 11} := by
  refine ⟨!![3, 4, 1, 1, 0, 2;
      1, 1, 3, 3, 2, 2;
      3, 4, 4, 3, 2, 1;
      2, 1, 1, 4, 2, 3;
      3, 2, 1, 3, 0, 1;
      2, 3, 4, 4, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 6, 11} =
      !![0, 3, 2, 2, 3, 2;
      0, 2, 1, 0, 3, 3;
      4, 1, 4, 4, 3, 4;
      4, 4, 1, 4, 0, 4;
      4, 4, 1, 4, 2, 1;
      4, 4, 0, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2155 : Certificate {0, 1, 3, 5, 6, 11} := by
  refine ⟨!![4, 4, 3, 2, 3, 1;
      4, 2, 1, 1, 3, 0;
      1, 1, 4, 1, 0, 0;
      4, 4, 1, 1, 4, 4;
      3, 1, 4, 3, 3, 0;
      2, 4, 1, 4, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 6, 11} =
      !![0, 0, 2, 0, 0, 2;
      0, 2, 2, 0, 3, 3;
      4, 1, 2, 4, 3, 4;
      4, 4, 4, 4, 0, 4;
      4, 4, 4, 4, 2, 1;
      4, 4, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2157 : Certificate {0, 2, 3, 5, 6, 11} := by
  refine ⟨!![3, 4, 0, 2, 4, 3;
      2, 3, 2, 4, 1, 3;
      4, 4, 4, 0, 0, 1;
      4, 3, 4, 3, 3, 0;
      4, 3, 1, 4, 4, 1;
      1, 2, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 6, 11} =
      !![0, 0, 3, 4, 2, 0;
      0, 1, 2, 0, 3, 3;
      4, 4, 2, 4, 3, 4;
      4, 1, 4, 4, 0, 4;
      4, 1, 4, 4, 2, 1;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2158 : Certificate {1, 2, 3, 5, 6, 11} := by
  refine ⟨!![4, 1, 1, 4, 1, 2;
      4, 3, 3, 0, 1, 3;
      4, 3, 0, 3, 4, 4;
      2, 4, 2, 4, 4, 2;
      1, 0, 0, 4, 1, 0;
      4, 0, 0, 3, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 6, 11} =
      !![0, 0, 0, 0, 4, 3;
      2, 1, 2, 0, 3, 3;
      1, 4, 2, 4, 3, 4;
      4, 1, 4, 4, 0, 4;
      4, 1, 4, 4, 2, 1;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2163 : Certificate {0, 1, 4, 5, 6, 11} := by
  refine ⟨!![1, 3, 0, 2, 0, 2;
      1, 2, 0, 0, 1, 4;
      3, 4, 4, 2, 1, 3;
      2, 1, 1, 0, 3, 1;
      3, 3, 3, 1, 0, 1;
      4, 3, 3, 4, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 6, 11} =
      !![0, 0, 1, 0, 0, 2;
      0, 3, 2, 2, 3, 2;
      4, 1, 4, 4, 3, 4;
      4, 4, 1, 4, 0, 4;
      4, 4, 3, 4, 2, 1;
      4, 4, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2165 : Certificate {0, 2, 4, 5, 6, 11} := by
  refine ⟨!![1, 3, 2, 1, 0, 1;
      3, 1, 1, 2, 3, 4;
      4, 1, 2, 3, 2, 3;
      3, 3, 2, 2, 4, 2;
      3, 3, 4, 3, 0, 3;
      3, 1, 4, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 6, 11} =
      !![0, 0, 2, 4, 2, 0;
      0, 2, 2, 2, 3, 2;
      4, 4, 4, 4, 3, 4;
      4, 1, 1, 4, 0, 4;
      4, 1, 3, 4, 2, 1;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2166 : Certificate {1, 2, 4, 5, 6, 11} := by
  refine ⟨!![2, 1, 3, 2, 4, 4;
      4, 4, 1, 3, 1, 4;
      3, 3, 1, 2, 3, 0;
      3, 3, 3, 2, 0, 0;
      0, 4, 3, 0, 0, 0;
      2, 3, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 6, 11} =
      !![0, 0, 0, 0, 4, 3;
      3, 2, 2, 2, 3, 2;
      1, 4, 4, 4, 3, 4;
      4, 1, 1, 4, 0, 4;
      4, 1, 3, 4, 2, 1;
      4, 0, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2169 : Certificate {0, 3, 4, 5, 6, 11} := by
  refine ⟨!![2, 0, 4, 0, 1, 4;
      2, 3, 4, 3, 0, 3;
      2, 4, 3, 0, 4, 3;
      1, 3, 3, 4, 0, 3;
      1, 3, 0, 0, 1, 4;
      2, 3, 2, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 6, 11} =
      !![0, 3, 2, 4, 2, 0;
      0, 2, 1, 0, 0, 2;
      4, 2, 4, 4, 3, 4;
      4, 4, 1, 4, 0, 4;
      4, 4, 3, 4, 2, 1;
      4, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2170 : Certificate {1, 3, 4, 5, 6, 11} := by
  refine ⟨!![2, 3, 3, 3, 4, 0;
      2, 1, 3, 1, 3, 4;
      1, 3, 3, 4, 0, 4;
      2, 1, 4, 2, 1, 1;
      4, 4, 4, 1, 1, 2;
      0, 3, 3, 2, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 6, 11} =
      !![0, 0, 0, 0, 4, 3;
      0, 2, 1, 0, 0, 2;
      1, 2, 4, 4, 3, 4;
      4, 4, 1, 4, 0, 4;
      4, 4, 3, 4, 2, 1;
      4, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2172 : Certificate {2, 3, 4, 5, 6, 11} := by
  refine ⟨!![0, 1, 2, 0, 3, 2;
      3, 2, 1, 0, 1, 3;
      4, 3, 1, 1, 0, 0;
      3, 4, 1, 1, 0, 4;
      3, 4, 3, 2, 1, 0;
      3, 3, 1, 4, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 6, 11} =
      !![0, 0, 0, 0, 4, 3;
      0, 3, 2, 4, 2, 0;
      4, 2, 4, 4, 3, 4;
      1, 4, 1, 4, 0, 4;
      1, 4, 3, 4, 2, 1;
      0, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2191 : Certificate {0, 1, 2, 3, 7, 11} := by
  refine ⟨!![0, 4, 1, 3, 2, 3;
      4, 3, 2, 1, 0, 2;
      1, 4, 4, 4, 1, 1;
      2, 2, 1, 2, 1, 1;
      4, 3, 0, 2, 4, 4;
      4, 3, 0, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 7, 11} =
      !![0, 2, 1, 2, 4, 3;
      0, 4, 0, 2, 4, 1;
      4, 2, 0, 3, 3, 1;
      4, 4, 1, 4, 1, 4;
      4, 4, 1, 4, 4, 1;
      4, 4, 0, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2199 : Certificate {0, 1, 2, 4, 7, 11} := by
  refine ⟨!![3, 2, 4, 4, 0, 1;
      3, 2, 3, 3, 1, 3;
      2, 0, 3, 2, 0, 0;
      2, 2, 2, 4, 2, 2;
      2, 1, 0, 2, 4, 4;
      0, 4, 3, 0, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 7, 11} =
      !![0, 3, 2, 2, 2, 2;
      0, 4, 0, 0, 4, 1;
      4, 2, 0, 3, 3, 1;
      4, 4, 1, 1, 1, 4;
      4, 4, 1, 3, 4, 1;
      4, 4, 0, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2203 : Certificate {0, 1, 3, 4, 7, 11} := by
  refine ⟨!![2, 4, 1, 2, 4, 2;
      0, 2, 1, 0, 1, 3;
      4, 4, 3, 2, 3, 2;
      3, 0, 0, 1, 3, 1;
      1, 2, 4, 3, 1, 2;
      3, 2, 4, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 7, 11} =
      !![0, 0, 2, 1, 4, 2;
      0, 4, 2, 0, 4, 1;
      4, 2, 3, 3, 3, 1;
      4, 4, 4, 1, 1, 4;
      4, 4, 4, 3, 4, 1;
      4, 4, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2205 : Certificate {0, 2, 3, 4, 7, 11} := by
  refine ⟨!![3, 2, 2, 4, 1, 2;
      0, 2, 1, 0, 1, 3;
      1, 4, 2, 1, 4, 3;
      2, 2, 4, 4, 1, 1;
      4, 4, 1, 4, 1, 4;
      2, 2, 2, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 7, 11} =
      !![0, 0, 3, 2, 1, 0;
      0, 0, 2, 0, 4, 1;
      4, 0, 3, 3, 3, 1;
      4, 1, 4, 1, 1, 4;
      4, 1, 4, 3, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2206 : Certificate {1, 2, 3, 4, 7, 11} := by
  refine ⟨!![3, 3, 4, 2, 3, 4;
      2, 4, 2, 3, 3, 4;
      4, 4, 0, 4, 1, 1;
      0, 4, 1, 3, 2, 3;
      3, 1, 4, 4, 1, 2;
      3, 2, 3, 3, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 7, 11} =
      !![0, 0, 0, 0, 4, 3;
      4, 0, 2, 0, 4, 1;
      2, 0, 3, 3, 3, 1;
      4, 1, 4, 1, 1, 4;
      4, 1, 4, 3, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2215 : Certificate {0, 1, 2, 5, 7, 11} := by
  refine ⟨!![4, 2, 1, 3, 2, 3;
      1, 0, 1, 4, 4, 1;
      1, 1, 0, 1, 2, 2;
      1, 4, 3, 1, 3, 3;
      1, 0, 4, 0, 3, 3;
      1, 0, 4, 2, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 7, 11} =
      !![0, 3, 2, 2, 2, 2;
      0, 2, 1, 0, 4, 3;
      4, 2, 0, 3, 3, 1;
      4, 4, 1, 4, 1, 4;
      4, 4, 1, 4, 4, 1;
      4, 4, 0, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2219 : Certificate {0, 1, 3, 5, 7, 11} := by
  refine ⟨!![1, 4, 2, 1, 2, 4;
      3, 2, 4, 4, 1, 1;
      4, 4, 4, 3, 2, 1;
      2, 0, 0, 4, 2, 4;
      3, 2, 2, 0, 0, 3;
      3, 2, 2, 2, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 7, 11} =
      !![0, 0, 2, 0, 4, 2;
      0, 2, 2, 0, 4, 3;
      4, 2, 3, 3, 3, 1;
      4, 4, 4, 4, 1, 4;
      4, 4, 4, 4, 4, 1;
      4, 4, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2221 : Certificate {0, 2, 3, 5, 7, 11} := by
  refine ⟨!![3, 4, 4, 0, 1, 4;
      4, 2, 0, 1, 3, 1;
      3, 2, 2, 3, 0, 0;
      3, 1, 4, 0, 4, 2;
      0, 0, 3, 1, 4, 2;
      0, 0, 3, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 7, 11} =
      !![0, 0, 3, 4, 1, 0;
      0, 1, 2, 0, 4, 3;
      4, 0, 3, 3, 3, 1;
      4, 1, 4, 4, 1, 4;
      4, 1, 4, 4, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2222 : Certificate {1, 2, 3, 5, 7, 11} := by
  refine ⟨!![3, 0, 2, 1, 4, 3;
      2, 0, 1, 0, 1, 1;
      3, 3, 0, 4, 3, 4;
      1, 2, 4, 2, 1, 4;
      3, 0, 0, 2, 3, 0;
      3, 0, 0, 4, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 7, 11} =
      !![0, 0, 0, 0, 4, 3;
      2, 1, 2, 0, 4, 3;
      2, 0, 3, 3, 3, 1;
      4, 1, 4, 4, 1, 4;
      4, 1, 4, 4, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2227 : Certificate {0, 1, 4, 5, 7, 11} := by
  refine ⟨!![3, 4, 4, 4, 1, 0;
      3, 3, 4, 2, 2, 2;
      3, 2, 3, 3, 3, 1;
      0, 2, 3, 2, 0, 0;
      4, 2, 3, 4, 2, 1;
      1, 0, 0, 3, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 7, 11} =
      !![0, 0, 1, 0, 4, 2;
      0, 3, 2, 2, 2, 2;
      4, 2, 3, 3, 3, 1;
      4, 4, 1, 4, 1, 4;
      4, 4, 3, 4, 4, 1;
      4, 4, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2229 : Certificate {0, 2, 4, 5, 7, 11} := by
  refine ⟨!![2, 3, 3, 1, 3, 2;
      1, 1, 4, 2, 2, 2;
      0, 4, 4, 1, 1, 4;
      4, 1, 4, 0, 3, 3;
      0, 3, 1, 3, 1, 0;
      0, 4, 2, 4, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 7, 11} =
      !![0, 0, 2, 4, 1, 0;
      0, 2, 2, 2, 2, 2;
      4, 0, 3, 3, 3, 1;
      4, 1, 1, 4, 1, 4;
      4, 1, 3, 4, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2230 : Certificate {1, 2, 4, 5, 7, 11} := by
  refine ⟨!![2, 2, 0, 2, 4, 4;
      4, 1, 0, 3, 1, 4;
      2, 1, 4, 3, 0, 3;
      1, 1, 3, 4, 4, 1;
      1, 4, 1, 4, 3, 2;
      4, 3, 2, 3, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 7, 11} =
      !![0, 0, 0, 0, 4, 3;
      3, 2, 2, 2, 2, 2;
      2, 0, 3, 3, 3, 1;
      4, 1, 1, 4, 1, 4;
      4, 1, 3, 4, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2233 : Certificate {0, 3, 4, 5, 7, 11} := by
  refine ⟨!![1, 3, 3, 1, 3, 2;
      3, 2, 3, 4, 4, 4;
      4, 2, 1, 2, 2, 0;
      4, 4, 1, 1, 4, 4;
      3, 4, 0, 0, 3, 2;
      4, 2, 4, 0, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 7, 11} =
      !![0, 3, 2, 4, 1, 0;
      0, 2, 1, 0, 4, 2;
      4, 3, 3, 3, 3, 1;
      4, 4, 1, 4, 1, 4;
      4, 4, 3, 4, 4, 1;
      4, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2234 : Certificate {1, 3, 4, 5, 7, 11} := by
  refine ⟨!![4, 0, 0, 1, 2, 1;
      4, 3, 4, 2, 2, 4;
      3, 0, 4, 0, 4, 4;
      3, 2, 4, 4, 1, 3;
      0, 0, 1, 2, 4, 1;
      2, 0, 2, 4, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 7, 11} =
      !![0, 0, 0, 0, 4, 3;
      0, 2, 1, 0, 4, 2;
      2, 3, 3, 3, 3, 1;
      4, 4, 1, 4, 1, 4;
      4, 4, 3, 4, 4, 1;
      4, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2236 : Certificate {2, 3, 4, 5, 7, 11} := by
  refine ⟨!![3, 0, 0, 2, 4, 2;
      4, 4, 1, 1, 4, 2;
      1, 0, 4, 2, 3, 1;
      1, 1, 2, 2, 3, 2;
      2, 0, 1, 0, 0, 4;
      1, 0, 2, 0, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 7, 11} =
      !![0, 0, 0, 0, 4, 3;
      0, 3, 2, 4, 1, 0;
      0, 3, 3, 3, 3, 1;
      1, 4, 1, 4, 1, 4;
      1, 4, 3, 4, 4, 1;
      0, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2247 : Certificate {0, 1, 2, 6, 7, 11} := by
  refine ⟨!![3, 2, 4, 1, 1, 2;
      3, 4, 1, 2, 3, 0;
      2, 4, 4, 1, 2, 2;
      4, 2, 1, 0, 0, 0;
      1, 2, 2, 2, 4, 4;
      2, 0, 1, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 6, 7, 11} =
      !![0, 3, 2, 3, 2, 2;
      0, 2, 1, 3, 4, 3;
      0, 4, 0, 3, 4, 1;
      4, 4, 1, 0, 1, 4;
      4, 4, 1, 2, 4, 1;
      4, 4, 0, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2251 : Certificate {0, 1, 3, 6, 7, 11} := by
  refine ⟨!![0, 1, 3, 2, 3, 4;
      1, 1, 1, 1, 3, 1;
      1, 3, 1, 3, 3, 4;
      2, 0, 0, 4, 2, 4;
      3, 4, 3, 3, 2, 0;
      1, 4, 3, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 6, 7, 11} =
      !![0, 0, 2, 0, 4, 2;
      0, 2, 2, 3, 4, 3;
      0, 4, 2, 3, 4, 1;
      4, 4, 4, 0, 1, 4;
      4, 4, 4, 2, 4, 1;
      4, 4, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2253 : Certificate {0, 2, 3, 6, 7, 11} := by
  refine ⟨!![2, 0, 1, 2, 3, 4;
      3, 1, 2, 0, 0, 0;
      3, 3, 2, 2, 0, 3;
      2, 2, 1, 2, 1, 2;
      3, 2, 2, 0, 3, 2;
      1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 6, 7, 11} =
      !![0, 0, 3, 2, 1, 0;
      0, 1, 2, 3, 4, 3;
      0, 0, 2, 3, 4, 1;
      4, 1, 4, 0, 1, 4;
      4, 1, 4, 2, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2254 : Certificate {1, 2, 3, 6, 7, 11} := by
  refine ⟨!![2, 3, 3, 0, 2, 0;
      0, 1, 3, 2, 3, 4;
      2, 1, 1, 4, 0, 2;
      4, 3, 1, 0, 2, 3;
      1, 1, 2, 2, 2, 1;
      2, 3, 1, 4, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 6, 7, 11} =
      !![0, 0, 0, 4, 4, 3;
      2, 1, 2, 3, 4, 3;
      4, 0, 2, 3, 4, 1;
      4, 1, 4, 0, 1, 4;
      4, 1, 4, 2, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2259 : Certificate {0, 1, 4, 6, 7, 11} := by
  refine ⟨!![0, 2, 2, 3, 0, 1;
      0, 1, 2, 1, 1, 3;
      1, 1, 3, 1, 4, 0;
      3, 1, 3, 0, 1, 4;
      3, 3, 4, 2, 0, 3;
      4, 1, 3, 3, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 6, 7, 11} =
      !![0, 0, 1, 0, 4, 2;
      0, 3, 2, 3, 2, 2;
      0, 4, 0, 3, 4, 1;
      4, 4, 1, 0, 1, 4;
      4, 4, 3, 2, 4, 1;
      4, 4, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2261 : Certificate {0, 2, 4, 6, 7, 11} := by
  refine ⟨!![0, 4, 1, 0, 2, 2;
      0, 4, 3, 4, 4, 2;
      1, 3, 0, 1, 3, 1;
      3, 4, 3, 2, 0, 3;
      3, 1, 4, 4, 4, 2;
      4, 4, 1, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 6, 7, 11} =
      !![0, 0, 2, 2, 1, 0;
      0, 2, 2, 3, 2, 2;
      0, 0, 0, 3, 4, 1;
      4, 1, 1, 0, 1, 4;
      4, 1, 3, 2, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2262 : Certificate {1, 2, 4, 6, 7, 11} := by
  refine ⟨!![0, 2, 3, 0, 1, 1;
      0, 1, 1, 4, 0, 3;
      1, 3, 2, 3, 1, 3;
      3, 0, 3, 3, 2, 2;
      3, 2, 4, 0, 1, 1;
      4, 4, 4, 1, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 6, 7, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 3, 2, 2;
      4, 0, 0, 3, 4, 1;
      4, 1, 1, 0, 1, 4;
      4, 1, 3, 2, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2265 : Certificate {0, 3, 4, 6, 7, 11} := by
  refine ⟨!![4, 1, 0, 3, 1, 0;
      3, 2, 4, 4, 1, 0;
      4, 2, 3, 2, 1, 2;
      4, 4, 3, 1, 3, 1;
      1, 2, 1, 2, 4, 4;
      3, 1, 0, 1, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 6, 7, 11} =
      !![0, 3, 2, 2, 1, 0;
      0, 2, 1, 0, 4, 2;
      0, 2, 0, 3, 4, 1;
      4, 4, 1, 0, 1, 4;
      4, 4, 3, 2, 4, 1;
      4, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2266 : Certificate {1, 3, 4, 6, 7, 11} := by
  refine ⟨!![3, 2, 2, 4, 2, 1;
      3, 2, 1, 2, 1, 1;
      2, 4, 1, 0, 3, 1;
      2, 1, 1, 4, 0, 0;
      0, 3, 1, 0, 0, 4;
      1, 3, 4, 3, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 6, 7, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 1, 0, 4, 2;
      4, 2, 0, 3, 4, 1;
      4, 4, 1, 0, 1, 4;
      4, 4, 3, 2, 4, 1;
      4, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2268 : Certificate {2, 3, 4, 6, 7, 11} := by
  refine ⟨!![1, 4, 4, 1, 0, 2;
      3, 2, 1, 1, 4, 1;
      0, 1, 3, 1, 4, 2;
      2, 1, 1, 1, 4, 0;
      2, 1, 4, 3, 2, 3;
      0, 4, 0, 3, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 6, 7, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 2, 2, 1, 0;
      0, 2, 0, 3, 4, 1;
      1, 4, 1, 0, 1, 4;
      1, 4, 3, 2, 4, 1;
      0, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2275 : Certificate {0, 1, 5, 6, 7, 11} := by
  refine ⟨!![4, 4, 1, 1, 4, 4;
      4, 3, 1, 4, 0, 1;
      2, 4, 4, 3, 0, 2;
      0, 1, 1, 1, 2, 2;
      1, 2, 2, 3, 3, 4;
      1, 1, 1, 4, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 6, 7, 11} =
      !![0, 0, 0, 0, 4, 2;
      0, 3, 2, 3, 2, 2;
      0, 2, 0, 3, 4, 3;
      4, 4, 4, 0, 1, 4;
      4, 4, 4, 2, 4, 1;
      4, 4, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2277 : Certificate {0, 2, 5, 6, 7, 11} := by
  refine ⟨!![1, 4, 1, 4, 2, 3;
      3, 4, 3, 1, 4, 0;
      4, 2, 0, 4, 2, 4;
      2, 2, 3, 0, 3, 2;
      1, 3, 4, 4, 1, 0;
      4, 1, 1, 1, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 6, 7, 11} =
      !![0, 0, 4, 2, 1, 0;
      0, 2, 2, 3, 2, 2;
      0, 1, 0, 3, 4, 3;
      4, 1, 4, 0, 1, 4;
      4, 1, 4, 2, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2278 : Certificate {1, 2, 5, 6, 7, 11} := by
  refine ⟨!![4, 2, 2, 3, 1, 0;
      3, 1, 4, 0, 0, 1;
      1, 4, 4, 0, 3, 2;
      2, 0, 2, 1, 2, 1;
      2, 0, 4, 4, 2, 2;
      0, 0, 2, 0, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 6, 7, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 2, 3, 2, 2;
      2, 1, 0, 3, 4, 3;
      4, 1, 4, 0, 1, 4;
      4, 1, 4, 2, 4, 1;
      4, 0, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2281 : Certificate {0, 3, 5, 6, 7, 11} := by
  refine ⟨!![0, 2, 3, 4, 4, 1;
      1, 1, 0, 3, 3, 4;
      2, 2, 1, 2, 1, 2;
      3, 0, 4, 2, 1, 2;
      4, 4, 3, 4, 0, 1;
      1, 4, 4, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 6, 7, 11} =
      !![0, 3, 4, 2, 1, 0;
      0, 2, 0, 0, 4, 2;
      0, 2, 0, 3, 4, 3;
      4, 4, 4, 0, 1, 4;
      4, 4, 4, 2, 4, 1;
      4, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2282 : Certificate {1, 3, 5, 6, 7, 11} := by
  refine ⟨!![0, 1, 4, 2, 2, 3;
      1, 3, 0, 2, 3, 0;
      2, 4, 3, 1, 2, 3;
      3, 3, 2, 3, 0, 1;
      4, 1, 4, 3, 3, 2;
      1, 3, 2, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 6, 7, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 0, 0, 4, 2;
      2, 2, 0, 3, 4, 3;
      4, 4, 4, 0, 1, 4;
      4, 4, 4, 2, 4, 1;
      4, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2284 : Certificate {2, 3, 5, 6, 7, 11} := by
  refine ⟨!![2, 3, 4, 0, 2, 0;
      4, 2, 4, 1, 0, 1;
      4, 3, 1, 3, 1, 1;
      1, 2, 1, 2, 2, 2;
      0, 4, 2, 1, 2, 4;
      4, 2, 1, 1, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 6, 7, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 3, 4, 2, 1, 0;
      1, 2, 0, 3, 4, 3;
      1, 4, 4, 0, 1, 4;
      1, 4, 4, 2, 4, 1;
      0, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2289 : Certificate {0, 4, 5, 6, 7, 11} := by
  refine ⟨!![0, 0, 1, 2, 4, 3;
      3, 3, 0, 4, 4, 2;
      2, 3, 2, 3, 1, 1;
      1, 2, 3, 0, 0, 0;
      0, 3, 1, 0, 3, 2;
      1, 3, 3, 3, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 6, 7, 11} =
      !![0, 2, 4, 2, 1, 0;
      0, 1, 0, 0, 4, 2;
      0, 2, 2, 3, 2, 2;
      4, 1, 4, 0, 1, 4;
      4, 3, 4, 2, 4, 1;
      4, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2290 : Certificate {1, 4, 5, 6, 7, 11} := by
  refine ⟨!![0, 0, 4, 3, 1, 2;
      4, 2, 0, 3, 2, 0;
      1, 4, 3, 1, 2, 1;
      3, 0, 2, 1, 2, 3;
      0, 3, 4, 1, 0, 1;
      3, 1, 2, 4, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 6, 7, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 1, 0, 0, 4, 2;
      3, 2, 2, 3, 2, 2;
      4, 1, 4, 0, 1, 4;
      4, 3, 4, 2, 4, 1;
      4, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2292 : Certificate {2, 4, 5, 6, 7, 11} := by
  refine ⟨!![0, 0, 2, 4, 3, 1;
      2, 4, 2, 0, 1, 2;
      2, 3, 4, 4, 3, 1;
      3, 0, 3, 3, 1, 1;
      2, 1, 4, 3, 4, 0;
      2, 2, 4, 2, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 6, 7, 11} =
      !![0, 0, 0, 4, 4, 3;
      0, 2, 4, 2, 1, 0;
      2, 2, 2, 3, 2, 2;
      1, 1, 4, 0, 1, 4;
      1, 3, 4, 2, 4, 1;
      0, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2296 : Certificate {3, 4, 5, 6, 7, 11} := by
  refine ⟨!![4, 2, 4, 4, 3, 3;
      3, 2, 1, 2, 0, 3;
      0, 2, 3, 4, 3, 0;
      3, 0, 0, 2, 4, 2;
      1, 3, 4, 4, 1, 1;
      0, 1, 3, 2, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 6, 7, 11} =
      !![0, 0, 0, 4, 4, 3;
      3, 2, 4, 2, 1, 0;
      2, 1, 0, 0, 4, 2;
      4, 1, 4, 0, 1, 4;
      4, 3, 4, 2, 4, 1;
      3, 3, 3, 3, 0, 2] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 2221 then
    if mask < 2158 then
      if mask < 2135 then
        if mask < 2107 then
          if mask < 2095 then
            ⟨{0, 1, 2, 3, 4, 11}, certificate_2079⟩
          else
            if mask < 2103 then
              ⟨{0, 1, 2, 3, 5, 11}, certificate_2095⟩
            else
              ⟨{0, 1, 2, 4, 5, 11}, certificate_2103⟩
        else
          if mask < 2110 then
            if mask < 2109 then
              ⟨{0, 1, 3, 4, 5, 11}, certificate_2107⟩
            else
              ⟨{0, 2, 3, 4, 5, 11}, certificate_2109⟩
          else
            if mask < 2127 then
              ⟨{1, 2, 3, 4, 5, 11}, certificate_2110⟩
            else
              ⟨{0, 1, 2, 3, 6, 11}, certificate_2127⟩
      else
        if mask < 2142 then
          if mask < 2139 then
            ⟨{0, 1, 2, 4, 6, 11}, certificate_2135⟩
          else
            if mask < 2141 then
              ⟨{0, 1, 3, 4, 6, 11}, certificate_2139⟩
            else
              ⟨{0, 2, 3, 4, 6, 11}, certificate_2141⟩
        else
          if mask < 2155 then
            if mask < 2151 then
              ⟨{1, 2, 3, 4, 6, 11}, certificate_2142⟩
            else
              ⟨{0, 1, 2, 5, 6, 11}, certificate_2151⟩
          else
            if mask < 2157 then
              ⟨{0, 1, 3, 5, 6, 11}, certificate_2155⟩
            else
              ⟨{0, 2, 3, 5, 6, 11}, certificate_2157⟩
    else
      if mask < 2191 then
        if mask < 2166 then
          if mask < 2163 then
            ⟨{1, 2, 3, 5, 6, 11}, certificate_2158⟩
          else
            if mask < 2165 then
              ⟨{0, 1, 4, 5, 6, 11}, certificate_2163⟩
            else
              ⟨{0, 2, 4, 5, 6, 11}, certificate_2165⟩
        else
          if mask < 2170 then
            if mask < 2169 then
              ⟨{1, 2, 4, 5, 6, 11}, certificate_2166⟩
            else
              ⟨{0, 3, 4, 5, 6, 11}, certificate_2169⟩
          else
            if mask < 2172 then
              ⟨{1, 3, 4, 5, 6, 11}, certificate_2170⟩
            else
              ⟨{2, 3, 4, 5, 6, 11}, certificate_2172⟩
      else
        if mask < 2205 then
          if mask < 2199 then
            ⟨{0, 1, 2, 3, 7, 11}, certificate_2191⟩
          else
            if mask < 2203 then
              ⟨{0, 1, 2, 4, 7, 11}, certificate_2199⟩
            else
              ⟨{0, 1, 3, 4, 7, 11}, certificate_2203⟩
        else
          if mask < 2215 then
            if mask < 2206 then
              ⟨{0, 2, 3, 4, 7, 11}, certificate_2205⟩
            else
              ⟨{1, 2, 3, 4, 7, 11}, certificate_2206⟩
          else
            if mask < 2219 then
              ⟨{0, 1, 2, 5, 7, 11}, certificate_2215⟩
            else
              ⟨{0, 1, 3, 5, 7, 11}, certificate_2219⟩
  else
    if mask < 2262 then
      if mask < 2236 then
        if mask < 2229 then
          if mask < 2222 then
            ⟨{0, 2, 3, 5, 7, 11}, certificate_2221⟩
          else
            if mask < 2227 then
              ⟨{1, 2, 3, 5, 7, 11}, certificate_2222⟩
            else
              ⟨{0, 1, 4, 5, 7, 11}, certificate_2227⟩
        else
          if mask < 2233 then
            if mask < 2230 then
              ⟨{0, 2, 4, 5, 7, 11}, certificate_2229⟩
            else
              ⟨{1, 2, 4, 5, 7, 11}, certificate_2230⟩
          else
            if mask < 2234 then
              ⟨{0, 3, 4, 5, 7, 11}, certificate_2233⟩
            else
              ⟨{1, 3, 4, 5, 7, 11}, certificate_2234⟩
      else
        if mask < 2253 then
          if mask < 2247 then
            ⟨{2, 3, 4, 5, 7, 11}, certificate_2236⟩
          else
            if mask < 2251 then
              ⟨{0, 1, 2, 6, 7, 11}, certificate_2247⟩
            else
              ⟨{0, 1, 3, 6, 7, 11}, certificate_2251⟩
        else
          if mask < 2259 then
            if mask < 2254 then
              ⟨{0, 2, 3, 6, 7, 11}, certificate_2253⟩
            else
              ⟨{1, 2, 3, 6, 7, 11}, certificate_2254⟩
          else
            if mask < 2261 then
              ⟨{0, 1, 4, 6, 7, 11}, certificate_2259⟩
            else
              ⟨{0, 2, 4, 6, 7, 11}, certificate_2261⟩
    else
      if mask < 2281 then
        if mask < 2268 then
          if mask < 2265 then
            ⟨{1, 2, 4, 6, 7, 11}, certificate_2262⟩
          else
            if mask < 2266 then
              ⟨{0, 3, 4, 6, 7, 11}, certificate_2265⟩
            else
              ⟨{1, 3, 4, 6, 7, 11}, certificate_2266⟩
        else
          if mask < 2277 then
            if mask < 2275 then
              ⟨{2, 3, 4, 6, 7, 11}, certificate_2268⟩
            else
              ⟨{0, 1, 5, 6, 7, 11}, certificate_2275⟩
          else
            if mask < 2278 then
              ⟨{0, 2, 5, 6, 7, 11}, certificate_2277⟩
            else
              ⟨{1, 2, 5, 6, 7, 11}, certificate_2278⟩
      else
        if mask < 2289 then
          if mask < 2282 then
            ⟨{0, 3, 5, 6, 7, 11}, certificate_2281⟩
          else
            if mask < 2284 then
              ⟨{1, 3, 5, 6, 7, 11}, certificate_2282⟩
            else
              ⟨{2, 3, 5, 6, 7, 11}, certificate_2284⟩
        else
          if mask < 2292 then
            if mask < 2290 then
              ⟨{0, 4, 5, 6, 7, 11}, certificate_2289⟩
            else
              ⟨{1, 4, 5, 6, 7, 11}, certificate_2290⟩
          else
            if mask < 2296 then
              ⟨{2, 4, 5, 6, 7, 11}, certificate_2292⟩
            else
              ⟨{3, 4, 5, 6, 7, 11}, certificate_2296⟩
end AMEProbe.QuinaryDirect.Batch08
#print axioms AMEProbe.QuinaryDirect.Batch08.lookup
