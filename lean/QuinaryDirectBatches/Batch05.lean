import QuinaryDirectBase

/-! Generated direct inverse certificates; both cut identity and inverse product are
checked by Lean's kernel. Data provenance: sjbevins/AME-paper-materials,
commit 2713599bec8fb429f6bb796b1ee4628dd4b51ef4; MIT license retained in ../../THIRD_PARTY_LICENSES/ame_materials_LICENSE. -/
namespace AMEProbe.QuinaryDirect.Batch05
open GraphState QuinaryGraph AMEProbe.QuinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_1295 : Certificate {0, 1, 2, 3, 8, 10} := by
  refine ⟨!![1, 0, 3, 1, 4, 3;
      1, 2, 0, 3, 2, 0;
      4, 3, 0, 4, 4, 1;
      1, 3, 4, 1, 3, 1;
      2, 0, 0, 1, 0, 2;
      2, 4, 4, 4, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 3, 8, 10} =
      !![0, 2, 1, 2, 1, 3;
      0, 4, 0, 2, 4, 3;
      4, 2, 0, 3, 0, 3;
      4, 1, 4, 2, 1, 0;
      4, 4, 1, 4, 4, 3;
      3, 0, 2, 2, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1303 : Certificate {0, 1, 2, 4, 8, 10} := by
  refine ⟨!![1, 3, 2, 2, 1, 2;
      0, 4, 1, 2, 4, 4;
      4, 0, 1, 3, 2, 2;
      4, 4, 2, 3, 0, 0;
      4, 3, 4, 2, 4, 0;
      3, 1, 0, 3, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 4, 8, 10} =
      !![0, 3, 2, 2, 4, 3;
      0, 4, 0, 0, 4, 3;
      4, 2, 0, 3, 0, 3;
      4, 1, 4, 4, 1, 0;
      4, 4, 1, 3, 4, 3;
      3, 0, 2, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1307 : Certificate {0, 1, 3, 4, 8, 10} := by
  refine ⟨!![0, 3, 3, 0, 3, 4;
      1, 2, 2, 3, 4, 3;
      1, 3, 1, 1, 0, 4;
      1, 2, 2, 1, 3, 2;
      3, 2, 1, 2, 2, 0;
      4, 3, 2, 1, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 4, 8, 10} =
      !![0, 0, 2, 1, 1, 0;
      0, 4, 2, 0, 4, 3;
      4, 2, 3, 3, 0, 3;
      4, 1, 2, 4, 1, 0;
      4, 4, 4, 3, 4, 3;
      3, 0, 2, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1309 : Certificate {0, 2, 3, 4, 8, 10} := by
  refine ⟨!![1, 1, 0, 2, 3, 2;
      4, 2, 3, 3, 0, 2;
      0, 1, 4, 3, 1, 1;
      4, 2, 3, 1, 4, 1;
      4, 3, 3, 1, 0, 3;
      3, 4, 0, 0, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 4, 8, 10} =
      !![0, 0, 3, 2, 4, 4;
      0, 0, 2, 0, 4, 3;
      4, 0, 3, 3, 0, 3;
      4, 4, 2, 4, 1, 0;
      4, 1, 4, 3, 4, 3;
      3, 2, 2, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1310 : Certificate {1, 2, 3, 4, 8, 10} := by
  refine ⟨!![2, 0, 1, 4, 0, 2;
      0, 3, 3, 0, 3, 4;
      2, 1, 0, 2, 1, 3;
      2, 3, 4, 2, 2, 0;
      1, 4, 1, 0, 3, 1;
      3, 1, 4, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 4, 8, 10} =
      !![0, 0, 0, 0, 4, 4;
      4, 0, 2, 0, 4, 3;
      2, 0, 3, 3, 0, 3;
      1, 4, 2, 4, 1, 0;
      4, 1, 4, 3, 4, 3;
      0, 2, 2, 3, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1319 : Certificate {0, 1, 2, 5, 8, 10} := by
  refine ⟨!![3, 0, 3, 1, 1, 2;
      1, 0, 4, 4, 4, 4;
      1, 1, 1, 3, 0, 3;
      1, 3, 0, 0, 4, 3;
      4, 4, 0, 1, 1, 4;
      1, 2, 2, 1, 2, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 5, 8, 10} =
      !![0, 3, 2, 2, 4, 3;
      0, 2, 1, 0, 1, 3;
      4, 2, 0, 3, 0, 3;
      4, 1, 4, 4, 1, 0;
      4, 4, 1, 4, 4, 3;
      3, 0, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1323 : Certificate {0, 1, 3, 5, 8, 10} := by
  refine ⟨!![4, 2, 1, 1, 2, 0;
      1, 4, 2, 2, 3, 4;
      2, 0, 3, 2, 3, 1;
      3, 2, 1, 0, 1, 4;
      2, 0, 4, 1, 4, 3;
      4, 1, 2, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 5, 8, 10} =
      !![0, 0, 2, 0, 1, 0;
      0, 2, 2, 0, 1, 3;
      4, 2, 3, 3, 0, 3;
      4, 1, 2, 4, 1, 0;
      4, 4, 4, 4, 4, 3;
      3, 0, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1325 : Certificate {0, 2, 3, 5, 8, 10} := by
  refine ⟨!![2, 3, 2, 0, 0, 1;
      3, 3, 1, 3, 0, 3;
      4, 1, 2, 2, 2, 2;
      4, 4, 3, 3, 2, 1;
      1, 3, 2, 3, 3, 1;
      1, 1, 1, 0, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 5, 8, 10} =
      !![0, 0, 3, 4, 4, 4;
      0, 1, 2, 0, 1, 3;
      4, 0, 3, 3, 0, 3;
      4, 4, 2, 4, 1, 0;
      4, 1, 4, 4, 4, 3;
      3, 2, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1326 : Certificate {1, 2, 3, 5, 8, 10} := by
  refine ⟨!![2, 2, 2, 1, 3, 3;
      3, 4, 1, 2, 2, 1;
      3, 3, 1, 1, 4, 2;
      0, 3, 4, 3, 2, 4;
      0, 4, 1, 3, 3, 3;
      4, 1, 4, 2, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 5, 8, 10} =
      !![0, 0, 0, 0, 4, 4;
      2, 1, 2, 0, 1, 3;
      2, 0, 3, 3, 0, 3;
      1, 4, 2, 4, 1, 0;
      4, 1, 4, 4, 4, 3;
      0, 2, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1331 : Certificate {0, 1, 4, 5, 8, 10} := by
  refine ⟨!![4, 3, 4, 0, 2, 4;
      2, 1, 2, 1, 2, 0;
      2, 0, 3, 2, 3, 1;
      0, 3, 2, 1, 4, 4;
      4, 0, 2, 3, 2, 4;
      3, 4, 2, 3, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 5, 8, 10} =
      !![0, 0, 1, 0, 1, 0;
      0, 3, 2, 2, 4, 3;
      4, 2, 3, 3, 0, 3;
      4, 1, 4, 4, 1, 0;
      4, 4, 3, 4, 4, 3;
      3, 0, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1333 : Certificate {0, 2, 4, 5, 8, 10} := by
  refine ⟨!![0, 1, 0, 3, 3, 4;
      1, 3, 2, 4, 1, 4;
      0, 4, 1, 1, 1, 1;
      3, 2, 3, 3, 2, 1;
      4, 0, 1, 2, 2, 0;
      2, 1, 3, 2, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 5, 8, 10} =
      !![0, 0, 2, 4, 4, 4;
      0, 2, 2, 2, 4, 3;
      4, 0, 3, 3, 0, 3;
      4, 4, 4, 4, 1, 0;
      4, 1, 3, 4, 4, 3;
      3, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1334 : Certificate {1, 2, 4, 5, 8, 10} := by
  refine ⟨!![0, 2, 0, 1, 1, 3;
      4, 0, 3, 4, 0, 0;
      0, 1, 1, 2, 2, 4;
      2, 3, 1, 3, 4, 4;
      1, 2, 0, 4, 0, 0;
      3, 3, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 5, 8, 10} =
      !![0, 0, 0, 0, 4, 4;
      3, 2, 2, 2, 4, 3;
      2, 0, 3, 3, 0, 3;
      1, 4, 4, 4, 1, 0;
      4, 1, 3, 4, 4, 3;
      0, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1337 : Certificate {0, 3, 4, 5, 8, 10} := by
  refine ⟨!![1, 2, 4, 3, 1, 3;
      4, 1, 4, 4, 0, 1;
      1, 1, 4, 3, 3, 0;
      2, 2, 3, 0, 3, 2;
      1, 3, 3, 4, 2, 3;
      0, 0, 4, 4, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 5, 8, 10} =
      !![0, 3, 2, 4, 4, 4;
      0, 2, 1, 0, 1, 0;
      4, 3, 3, 3, 0, 3;
      4, 2, 4, 4, 1, 0;
      4, 4, 3, 4, 4, 3;
      3, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1338 : Certificate {1, 3, 4, 5, 8, 10} := by
  refine ⟨!![4, 4, 2, 0, 3, 2;
      2, 0, 4, 2, 0, 0;
      3, 2, 4, 0, 3, 1;
      3, 1, 4, 4, 2, 0;
      3, 4, 3, 1, 2, 4;
      1, 1, 2, 4, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 5, 8, 10} =
      !![0, 0, 0, 0, 4, 4;
      0, 2, 1, 0, 1, 0;
      2, 3, 3, 3, 0, 3;
      1, 2, 4, 4, 1, 0;
      4, 4, 3, 4, 4, 3;
      0, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1340 : Certificate {2, 3, 4, 5, 8, 10} := by
  refine ⟨!![1, 2, 1, 1, 4, 4;
      4, 4, 1, 4, 3, 3;
      2, 2, 4, 1, 3, 4;
      2, 0, 1, 4, 0, 2;
      2, 1, 4, 4, 1, 4;
      2, 4, 1, 1, 4, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 5, 8, 10} =
      !![0, 0, 0, 0, 4, 4;
      0, 3, 2, 4, 4, 4;
      0, 3, 3, 3, 0, 3;
      4, 2, 4, 4, 1, 0;
      1, 4, 3, 4, 4, 3;
      2, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1351 : Certificate {0, 1, 2, 6, 8, 10} := by
  refine ⟨!![4, 1, 4, 4, 4, 3;
      1, 4, 2, 3, 1, 3;
      1, 2, 3, 4, 3, 4;
      2, 1, 0, 0, 3, 1;
      3, 1, 0, 1, 2, 1;
      1, 4, 1, 3, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 6, 8, 10} =
      !![0, 3, 2, 3, 4, 3;
      0, 2, 1, 3, 1, 3;
      0, 4, 0, 3, 4, 3;
      4, 1, 4, 3, 1, 0;
      4, 4, 1, 2, 4, 3;
      3, 0, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1355 : Certificate {0, 1, 3, 6, 8, 10} := by
  refine ⟨!![1, 3, 1, 4, 4, 3;
      0, 2, 4, 4, 3, 4;
      3, 0, 2, 3, 1, 3;
      0, 2, 4, 2, 2, 3;
      0, 0, 1, 4, 3, 4;
      3, 2, 0, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 6, 8, 10} =
      !![0, 0, 2, 0, 1, 0;
      0, 2, 2, 3, 1, 3;
      0, 4, 2, 3, 4, 3;
      4, 1, 2, 3, 1, 0;
      4, 4, 4, 2, 4, 3;
      3, 0, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1357 : Certificate {0, 2, 3, 6, 8, 10} := by
  refine ⟨!![1, 3, 2, 1, 4, 2;
      0, 3, 1, 1, 2, 1;
      3, 4, 3, 2, 2, 3;
      0, 3, 1, 4, 1, 0;
      0, 4, 4, 2, 4, 2;
      3, 4, 2, 2, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 6, 8, 10} =
      !![0, 0, 3, 2, 4, 4;
      0, 1, 2, 3, 1, 3;
      0, 0, 2, 3, 4, 3;
      4, 4, 2, 3, 1, 0;
      4, 1, 4, 2, 4, 3;
      3, 2, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1358 : Certificate {1, 2, 3, 6, 8, 10} := by
  refine ⟨!![1, 2, 1, 0, 2, 3;
      1, 0, 2, 1, 4, 4;
      3, 1, 0, 4, 1, 1;
      2, 2, 3, 4, 0, 1;
      3, 0, 2, 2, 0, 1;
      4, 3, 0, 4, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 6, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      2, 1, 2, 3, 1, 3;
      4, 0, 2, 3, 4, 3;
      1, 4, 2, 3, 1, 0;
      4, 1, 4, 2, 4, 3;
      0, 2, 2, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1363 : Certificate {0, 1, 4, 6, 8, 10} := by
  refine ⟨!![3, 1, 2, 0, 1, 4;
      3, 4, 3, 3, 1, 3;
      4, 0, 1, 4, 3, 4;
      4, 4, 2, 2, 2, 3;
      2, 0, 4, 1, 2, 1;
      1, 4, 4, 1, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 6, 8, 10} =
      !![0, 0, 1, 0, 1, 0;
      0, 3, 2, 3, 4, 3;
      0, 4, 0, 3, 4, 3;
      4, 1, 4, 3, 1, 0;
      4, 4, 3, 2, 4, 3;
      3, 0, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1365 : Certificate {0, 2, 4, 6, 8, 10} := by
  refine ⟨!![4, 2, 4, 4, 3, 1;
      4, 0, 0, 2, 3, 0;
      1, 3, 2, 3, 2, 0;
      3, 2, 3, 2, 0, 4;
      0, 4, 2, 4, 3, 4;
      2, 1, 3, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 6, 8, 10} =
      !![0, 0, 2, 2, 4, 4;
      0, 2, 2, 3, 4, 3;
      0, 0, 0, 3, 4, 3;
      4, 4, 4, 3, 1, 0;
      4, 1, 3, 2, 4, 3;
      3, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1366 : Certificate {1, 2, 4, 6, 8, 10} := by
  refine ⟨!![1, 2, 3, 2, 4, 2;
      4, 1, 3, 1, 1, 2;
      4, 3, 3, 0, 1, 4;
      1, 0, 3, 1, 3, 4;
      4, 2, 4, 2, 4, 2;
      4, 3, 3, 2, 3, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 6, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 4, 3;
      4, 0, 0, 3, 4, 3;
      1, 4, 4, 3, 1, 0;
      4, 1, 3, 2, 4, 3;
      0, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1369 : Certificate {0, 3, 4, 6, 8, 10} := by
  refine ⟨!![0, 1, 0, 3, 2, 2;
      3, 0, 0, 4, 1, 0;
      1, 4, 1, 2, 0, 4;
      4, 1, 4, 1, 4, 0;
      3, 2, 4, 0, 3, 1;
      0, 3, 1, 3, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 6, 8, 10} =
      !![0, 3, 2, 2, 4, 4;
      0, 2, 1, 0, 1, 0;
      0, 2, 0, 3, 4, 3;
      4, 2, 4, 3, 1, 0;
      4, 4, 3, 2, 4, 3;
      3, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1370 : Certificate {1, 3, 4, 6, 8, 10} := by
  refine ⟨!![0, 1, 0, 3, 2, 2;
      1, 3, 4, 4, 0, 2;
      2, 0, 4, 2, 3, 3;
      3, 1, 1, 4, 3, 3;
      1, 0, 3, 0, 2, 3;
      0, 4, 1, 1, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 6, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 1, 0, 1, 0;
      4, 2, 0, 3, 4, 3;
      1, 2, 4, 3, 1, 0;
      4, 4, 3, 2, 4, 3;
      0, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1372 : Certificate {2, 3, 4, 6, 8, 10} := by
  refine ⟨!![4, 3, 1, 4, 2, 4;
      2, 2, 3, 1, 2, 2;
      4, 4, 2, 4, 4, 0;
      0, 4, 4, 3, 2, 3;
      4, 1, 0, 3, 1, 1;
      0, 0, 1, 4, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 6, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 2, 2, 4, 4;
      0, 2, 0, 3, 4, 3;
      4, 2, 4, 3, 1, 0;
      1, 4, 3, 2, 4, 3;
      2, 2, 3, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1379 : Certificate {0, 1, 5, 6, 8, 10} := by
  refine ⟨!![4, 4, 1, 3, 2, 2;
      0, 2, 1, 2, 4, 2;
      1, 2, 4, 4, 3, 4;
      3, 3, 3, 2, 2, 3;
      1, 0, 0, 0, 0, 0;
      0, 4, 0, 0, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 6, 8, 10} =
      !![0, 0, 0, 0, 1, 0;
      0, 3, 2, 3, 4, 3;
      0, 2, 0, 3, 1, 3;
      4, 1, 4, 3, 1, 0;
      4, 4, 4, 2, 4, 3;
      3, 0, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1381 : Certificate {0, 2, 5, 6, 8, 10} := by
  refine ⟨!![1, 4, 4, 3, 3, 4;
      0, 2, 1, 2, 4, 2;
      4, 3, 4, 0, 4, 3;
      2, 1, 3, 0, 0, 0;
      4, 1, 0, 1, 1, 4;
      0, 3, 2, 4, 0, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 6, 8, 10} =
      !![0, 0, 4, 2, 4, 4;
      0, 2, 2, 3, 4, 3;
      0, 1, 0, 3, 1, 3;
      4, 4, 4, 3, 1, 0;
      4, 1, 4, 2, 4, 3;
      3, 2, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1382 : Certificate {1, 2, 5, 6, 8, 10} := by
  refine ⟨!![4, 4, 4, 3, 2, 2;
      1, 3, 2, 4, 2, 0;
      3, 0, 1, 4, 1, 1;
      4, 2, 4, 2, 1, 4;
      3, 3, 2, 0, 3, 2;
      2, 0, 4, 3, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 6, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 3, 4, 3;
      2, 1, 0, 3, 1, 3;
      1, 4, 4, 3, 1, 0;
      4, 1, 4, 2, 4, 3;
      0, 2, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1385 : Certificate {0, 3, 5, 6, 8, 10} := by
  refine ⟨!![1, 0, 2, 4, 0, 0;
      4, 4, 2, 0, 4, 3;
      2, 3, 4, 2, 1, 1;
      1, 4, 2, 4, 2, 2;
      2, 3, 1, 0, 2, 4;
      4, 4, 0, 1, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 6, 8, 10} =
      !![0, 3, 4, 2, 4, 4;
      0, 2, 0, 0, 1, 0;
      0, 2, 0, 3, 1, 3;
      4, 2, 4, 3, 1, 0;
      4, 4, 4, 2, 4, 3;
      3, 2, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1386 : Certificate {1, 3, 5, 6, 8, 10} := by
  refine ⟨!![2, 2, 3, 4, 4, 3;
      4, 3, 0, 2, 2, 4;
      4, 2, 1, 2, 4, 2;
      4, 3, 1, 3, 0, 3;
      2, 0, 0, 1, 1, 2;
      3, 2, 4, 1, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 6, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 0, 0, 1, 0;
      2, 2, 0, 3, 1, 3;
      1, 2, 4, 3, 1, 0;
      4, 4, 4, 2, 4, 3;
      0, 2, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1388 : Certificate {2, 3, 5, 6, 8, 10} := by
  refine ⟨!![0, 2, 4, 3, 0, 0;
      1, 1, 0, 0, 1, 2;
      2, 4, 1, 4, 0, 4;
      1, 4, 2, 3, 4, 1;
      2, 2, 4, 4, 1, 2;
      1, 4, 4, 3, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 6, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 4, 2, 4, 4;
      1, 2, 0, 3, 1, 3;
      4, 2, 4, 3, 1, 0;
      1, 4, 4, 2, 4, 3;
      2, 2, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1393 : Certificate {0, 4, 5, 6, 8, 10} := by
  refine ⟨!![2, 1, 0, 4, 1, 2;
      3, 3, 2, 2, 2, 3;
      4, 0, 0, 2, 3, 0;
      4, 2, 3, 2, 1, 1;
      2, 3, 3, 3, 3, 2;
      2, 2, 2, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 6, 8, 10} =
      !![0, 2, 4, 2, 4, 4;
      0, 1, 0, 0, 1, 0;
      0, 2, 2, 3, 4, 3;
      4, 4, 4, 3, 1, 0;
      4, 3, 4, 2, 4, 3;
      3, 3, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1394 : Certificate {1, 4, 5, 6, 8, 10} := by
  refine ⟨!![1, 3, 3, 2, 0, 1;
      1, 2, 0, 3, 3, 1;
      2, 4, 1, 3, 1, 3;
      1, 3, 1, 1, 4, 3;
      4, 4, 0, 2, 2, 4;
      4, 3, 4, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 6, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 1, 0, 0, 1, 0;
      3, 2, 2, 3, 4, 3;
      1, 4, 4, 3, 1, 0;
      4, 3, 4, 2, 4, 3;
      0, 3, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1396 : Certificate {2, 4, 5, 6, 8, 10} := by
  refine ⟨!![2, 3, 1, 0, 4, 0;
      1, 1, 0, 0, 1, 2;
      3, 1, 4, 2, 4, 0;
      0, 0, 3, 4, 4, 2;
      1, 0, 1, 1, 2, 1;
      3, 0, 1, 0, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 6, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 4, 2, 4, 4;
      2, 2, 2, 3, 4, 3;
      4, 4, 4, 3, 1, 0;
      1, 3, 4, 2, 4, 3;
      2, 3, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1400 : Certificate {3, 4, 5, 6, 8, 10} := by
  refine ⟨!![0, 3, 4, 1, 4, 3;
      1, 3, 1, 4, 2, 4;
      0, 0, 3, 4, 1, 1;
      4, 2, 3, 1, 0, 3;
      4, 1, 2, 4, 0, 0;
      1, 2, 0, 0, 0, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 6, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 4, 2, 4, 4;
      2, 1, 0, 0, 1, 0;
      2, 4, 4, 3, 1, 0;
      4, 3, 4, 2, 4, 3;
      2, 3, 1, 1, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1415 : Certificate {0, 1, 2, 7, 8, 10} := by
  refine ⟨!![4, 2, 2, 4, 2, 4;
      1, 1, 3, 3, 2, 0;
      4, 2, 1, 4, 3, 4;
      3, 4, 0, 0, 2, 4;
      4, 3, 2, 1, 3, 3;
      1, 1, 2, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 2, 7, 8, 10} =
      !![0, 3, 2, 2, 4, 3;
      0, 2, 1, 4, 1, 3;
      0, 4, 0, 4, 4, 3;
      4, 2, 0, 3, 0, 3;
      4, 4, 1, 4, 4, 3;
      3, 0, 2, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1419 : Certificate {0, 1, 3, 7, 8, 10} := by
  refine ⟨!![1, 4, 3, 0, 0, 2;
      1, 2, 1, 2, 1, 1;
      3, 2, 1, 0, 3, 1;
      1, 4, 0, 2, 2, 3;
      1, 0, 3, 2, 1, 1;
      4, 4, 1, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 3, 7, 8, 10} =
      !![0, 0, 2, 4, 1, 0;
      0, 2, 2, 4, 1, 3;
      0, 4, 2, 4, 4, 3;
      4, 2, 3, 3, 0, 3;
      4, 4, 4, 4, 4, 3;
      3, 0, 2, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1421 : Certificate {0, 2, 3, 7, 8, 10} := by
  refine ⟨!![1, 1, 3, 0, 0, 2;
      3, 2, 3, 1, 3, 3;
      4, 2, 2, 2, 4, 2;
      4, 3, 3, 3, 0, 1;
      1, 2, 3, 2, 1, 1;
      4, 2, 1, 2, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 3, 7, 8, 10} =
      !![0, 0, 3, 1, 4, 4;
      0, 1, 2, 4, 1, 3;
      0, 0, 2, 4, 4, 3;
      4, 0, 3, 3, 0, 3;
      4, 1, 4, 4, 4, 3;
      3, 2, 2, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1422 : Certificate {1, 2, 3, 7, 8, 10} := by
  refine ⟨!![2, 1, 0, 4, 4, 0;
      4, 1, 4, 4, 1, 2;
      3, 2, 0, 3, 0, 4;
      4, 1, 1, 1, 3, 3;
      0, 1, 0, 2, 1, 4;
      0, 3, 4, 2, 1, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 3, 7, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      2, 1, 2, 4, 1, 3;
      4, 0, 2, 4, 4, 3;
      2, 0, 3, 3, 0, 3;
      4, 1, 4, 4, 4, 3;
      0, 2, 2, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1427 : Certificate {0, 1, 4, 7, 8, 10} := by
  refine ⟨!![1, 2, 1, 2, 4, 4;
      2, 3, 0, 0, 3, 1;
      2, 4, 0, 4, 0, 3;
      1, 2, 3, 4, 1, 0;
      0, 3, 3, 0, 1, 2;
      1, 1, 4, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 4, 7, 8, 10} =
      !![0, 0, 1, 4, 1, 0;
      0, 3, 2, 2, 4, 3;
      0, 4, 0, 4, 4, 3;
      4, 2, 3, 3, 0, 3;
      4, 4, 3, 4, 4, 3;
      3, 0, 3, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1429 : Certificate {0, 2, 4, 7, 8, 10} := by
  refine ⟨!![3, 3, 3, 0, 3, 3;
      4, 0, 1, 4, 4, 1;
      3, 1, 2, 2, 0, 4;
      2, 3, 1, 1, 4, 0;
      1, 3, 2, 1, 2, 1;
      1, 2, 3, 4, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 4, 7, 8, 10} =
      !![0, 0, 2, 1, 4, 4;
      0, 2, 2, 2, 4, 3;
      0, 0, 0, 4, 4, 3;
      4, 0, 3, 3, 0, 3;
      4, 1, 3, 4, 4, 3;
      3, 2, 3, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1430 : Certificate {1, 2, 4, 7, 8, 10} := by
  refine ⟨!![2, 3, 4, 2, 3, 3;
      2, 4, 1, 1, 3, 0;
      1, 2, 1, 3, 1, 0;
      2, 4, 3, 3, 0, 1;
      3, 4, 2, 4, 3, 2;
      4, 2, 0, 3, 2, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 4, 7, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 2, 4, 3;
      4, 0, 0, 4, 4, 3;
      2, 0, 3, 3, 0, 3;
      4, 1, 3, 4, 4, 3;
      0, 2, 3, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1433 : Certificate {0, 3, 4, 7, 8, 10} := by
  refine ⟨!![3, 3, 3, 0, 0, 2;
      1, 0, 4, 1, 1, 4;
      2, 1, 3, 1, 3, 3;
      3, 3, 0, 2, 2, 3;
      4, 3, 4, 4, 2, 2;
      0, 2, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 4, 7, 8, 10} =
      !![0, 3, 2, 1, 4, 4;
      0, 2, 1, 4, 1, 0;
      0, 2, 0, 4, 4, 3;
      4, 3, 3, 3, 0, 3;
      4, 4, 3, 4, 4, 3;
      3, 2, 3, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1434 : Certificate {1, 3, 4, 7, 8, 10} := by
  refine ⟨!![4, 4, 4, 1, 2, 4;
      3, 2, 1, 3, 0, 3;
      3, 2, 4, 3, 2, 3;
      0, 0, 2, 2, 2, 1;
      1, 0, 1, 3, 0, 2;
      3, 0, 2, 0, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 4, 7, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 1, 4, 1, 0;
      4, 2, 0, 4, 4, 3;
      2, 3, 3, 3, 0, 3;
      4, 4, 3, 4, 4, 3;
      0, 2, 3, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1436 : Certificate {2, 3, 4, 7, 8, 10} := by
  refine ⟨!![3, 2, 0, 2, 4, 1;
      3, 3, 4, 3, 0, 0;
      2, 4, 2, 4, 4, 3;
      3, 2, 2, 4, 1, 2;
      4, 2, 1, 0, 4, 3;
      2, 1, 2, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 4, 7, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 2, 1, 4, 4;
      0, 2, 0, 4, 4, 3;
      0, 3, 3, 3, 0, 3;
      1, 4, 3, 4, 4, 3;
      2, 2, 3, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1443 : Certificate {0, 1, 5, 7, 8, 10} := by
  refine ⟨!![0, 1, 3, 1, 1, 1;
      1, 1, 0, 3, 3, 2;
      4, 3, 0, 3, 0, 1;
      3, 4, 4, 1, 2, 1;
      4, 4, 4, 1, 2, 1;
      4, 1, 2, 3, 3, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 5, 7, 8, 10} =
      !![0, 0, 0, 4, 1, 0;
      0, 3, 2, 2, 4, 3;
      0, 2, 0, 4, 1, 3;
      4, 2, 3, 3, 0, 3;
      4, 4, 4, 4, 4, 3;
      3, 0, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1445 : Certificate {0, 2, 5, 7, 8, 10} := by
  refine ⟨!![4, 1, 1, 2, 0, 1;
      2, 0, 4, 3, 2, 0;
      1, 4, 2, 0, 4, 3;
      2, 1, 3, 0, 0, 0;
      0, 0, 4, 4, 0, 3;
      0, 2, 2, 1, 1, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 5, 7, 8, 10} =
      !![0, 0, 4, 1, 4, 4;
      0, 2, 2, 2, 4, 3;
      0, 1, 0, 4, 1, 3;
      4, 0, 3, 3, 0, 3;
      4, 1, 4, 4, 4, 3;
      3, 2, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1446 : Certificate {1, 2, 5, 7, 8, 10} := by
  refine ⟨!![4, 0, 4, 1, 4, 1;
      0, 2, 1, 2, 2, 2;
      1, 0, 4, 1, 0, 3;
      2, 3, 2, 2, 2, 0;
      1, 0, 0, 3, 1, 2;
      1, 2, 3, 0, 2, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 5, 7, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 2, 2, 4, 3;
      2, 1, 0, 4, 1, 3;
      2, 0, 3, 3, 0, 3;
      4, 1, 4, 4, 4, 3;
      0, 2, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1449 : Certificate {0, 3, 5, 7, 8, 10} := by
  refine ⟨!![4, 4, 1, 4, 2, 4;
      2, 0, 4, 3, 2, 0;
      4, 1, 3, 0, 0, 0;
      2, 4, 3, 2, 2, 3;
      3, 0, 0, 1, 3, 3;
      0, 3, 2, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 5, 7, 8, 10} =
      !![0, 3, 4, 1, 4, 4;
      0, 2, 0, 4, 1, 0;
      0, 2, 0, 4, 1, 3;
      4, 3, 3, 3, 0, 3;
      4, 4, 4, 4, 4, 3;
      3, 2, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1450 : Certificate {1, 3, 5, 7, 8, 10} := by
  refine ⟨!![1, 2, 0, 3, 0, 1;
      2, 2, 1, 2, 1, 0;
      2, 1, 2, 2, 3, 3;
      1, 4, 0, 3, 1, 2;
      2, 1, 3, 4, 4, 2;
      1, 0, 2, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 5, 7, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 0, 4, 1, 0;
      2, 2, 0, 4, 1, 3;
      2, 3, 3, 3, 0, 3;
      4, 4, 4, 4, 4, 3;
      0, 2, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1452 : Certificate {2, 3, 5, 7, 8, 10} := by
  refine ⟨!![4, 2, 3, 4, 1, 1;
      1, 0, 1, 4, 1, 4;
      4, 0, 2, 3, 3, 0;
      0, 3, 2, 3, 0, 4;
      4, 0, 3, 0, 4, 4;
      0, 2, 0, 2, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 5, 7, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 3, 4, 1, 4, 4;
      1, 2, 0, 4, 1, 3;
      0, 3, 3, 3, 0, 3;
      1, 4, 4, 4, 4, 3;
      2, 2, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1457 : Certificate {0, 4, 5, 7, 8, 10} := by
  refine ⟨!![1, 1, 2, 3, 0, 3;
      0, 3, 3, 4, 4, 1;
      0, 3, 2, 0, 2, 4;
      3, 1, 2, 2, 4, 2;
      3, 4, 4, 3, 0, 1;
      4, 0, 2, 2, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 5, 7, 8, 10} =
      !![0, 2, 4, 1, 4, 4;
      0, 1, 0, 4, 1, 0;
      0, 2, 2, 2, 4, 3;
      4, 3, 3, 3, 0, 3;
      4, 3, 4, 4, 4, 3;
      3, 3, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1458 : Certificate {1, 4, 5, 7, 8, 10} := by
  refine ⟨!![4, 0, 2, 3, 1, 3;
      3, 3, 2, 0, 1, 2;
      4, 3, 4, 3, 3, 2;
      0, 3, 1, 3, 4, 3;
      2, 1, 4, 3, 3, 1;
      2, 1, 0, 4, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 5, 7, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 1, 0, 4, 1, 0;
      3, 2, 2, 2, 4, 3;
      2, 3, 3, 3, 0, 3;
      4, 3, 4, 4, 4, 3;
      0, 3, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1460 : Certificate {2, 4, 5, 7, 8, 10} := by
  refine ⟨!![4, 0, 2, 3, 1, 3;
      2, 2, 3, 4, 2, 1;
      4, 2, 3, 4, 3, 3;
      2, 2, 1, 3, 2, 3;
      0, 4, 1, 1, 0, 4;
      2, 4, 3, 1, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 5, 7, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      0, 2, 4, 1, 4, 4;
      2, 2, 2, 2, 4, 3;
      0, 3, 3, 3, 0, 3;
      1, 3, 4, 4, 4, 3;
      2, 3, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1464 : Certificate {3, 4, 5, 7, 8, 10} := by
  refine ⟨!![1, 1, 1, 0, 4, 0;
      4, 0, 3, 2, 0, 4;
      3, 2, 0, 2, 4, 1;
      3, 0, 3, 4, 1, 4;
      2, 3, 4, 2, 3, 0;
      4, 2, 3, 4, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 5, 7, 8, 10} =
      !![0, 0, 0, 4, 4, 4;
      3, 2, 4, 1, 4, 4;
      2, 1, 0, 4, 1, 0;
      3, 3, 3, 3, 0, 3;
      4, 3, 4, 4, 4, 3;
      2, 3, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1475 : Certificate {0, 1, 6, 7, 8, 10} := by
  refine ⟨!![2, 0, 3, 0, 1, 4;
      4, 3, 3, 4, 0, 0;
      3, 0, 2, 1, 3, 1;
      3, 3, 1, 1, 0, 0;
      4, 3, 1, 1, 0, 0;
      4, 3, 3, 3, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 1, 6, 7, 8, 10} =
      !![0, 0, 0, 4, 1, 0;
      0, 3, 3, 2, 4, 3;
      0, 2, 3, 4, 1, 3;
      0, 4, 3, 4, 4, 3;
      4, 4, 2, 4, 4, 3;
      3, 0, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1477 : Certificate {0, 2, 6, 7, 8, 10} := by
  refine ⟨!![0, 1, 4, 3, 1, 4;
      1, 0, 1, 2, 1, 2;
      1, 4, 2, 0, 4, 3;
      1, 2, 1, 0, 1, 2;
      2, 0, 0, 1, 2, 4;
      0, 0, 0, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 2, 6, 7, 8, 10} =
      !![0, 0, 2, 1, 4, 4;
      0, 2, 3, 2, 4, 3;
      0, 1, 3, 4, 1, 3;
      0, 0, 3, 4, 4, 3;
      4, 1, 2, 4, 4, 3;
      3, 2, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1478 : Certificate {1, 2, 6, 7, 8, 10} := by
  refine ⟨!![0, 3, 2, 4, 3, 2;
      1, 4, 1, 1, 3, 2;
      1, 4, 1, 2, 2, 2;
      1, 2, 0, 2, 4, 1;
      2, 1, 2, 3, 4, 1;
      0, 3, 2, 3, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 2, 6, 7, 8, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 2, 3, 2, 4, 3;
      2, 1, 3, 4, 1, 3;
      4, 0, 3, 4, 4, 3;
      4, 1, 2, 4, 4, 3;
      0, 2, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1481 : Certificate {0, 3, 6, 7, 8, 10} := by
  refine ⟨!![4, 2, 2, 3, 0, 2;
      3, 0, 3, 1, 3, 1;
      2, 3, 4, 0, 0, 0;
      1, 4, 4, 4, 1, 2;
      0, 0, 3, 2, 0, 0;
      3, 0, 3, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 3, 6, 7, 8, 10} =
      !![0, 3, 2, 1, 4, 4;
      0, 2, 0, 4, 1, 0;
      0, 2, 3, 4, 1, 3;
      0, 2, 3, 4, 4, 3;
      4, 4, 2, 4, 4, 3;
      3, 2, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1482 : Certificate {1, 3, 6, 7, 8, 10} := by
  refine ⟨!![3, 2, 3, 2, 3, 2;
      0, 1, 4, 0, 3, 2;
      0, 2, 3, 1, 0, 4;
      3, 3, 4, 4, 4, 1;
      3, 2, 1, 4, 3, 2;
      3, 3, 2, 1, 3, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 3, 6, 7, 8, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 0, 4, 1, 0;
      2, 2, 3, 4, 1, 3;
      4, 2, 3, 4, 4, 3;
      4, 4, 2, 4, 4, 3;
      0, 2, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1484 : Certificate {2, 3, 6, 7, 8, 10} := by
  refine ⟨!![2, 4, 4, 1, 2, 0;
      4, 1, 1, 3, 2, 1;
      0, 1, 1, 3, 0, 2;
      1, 0, 2, 1, 2, 3;
      4, 3, 1, 4, 4, 0;
      4, 1, 1, 2, 4, 0], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 3, 6, 7, 8, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 3, 2, 1, 4, 4;
      1, 2, 3, 4, 1, 3;
      0, 2, 3, 4, 4, 3;
      1, 4, 2, 4, 4, 3;
      2, 2, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1489 : Certificate {0, 4, 6, 7, 8, 10} := by
  refine ⟨!![3, 4, 4, 3, 4, 0;
      1, 2, 4, 4, 1, 2;
      0, 2, 3, 0, 3, 1;
      1, 2, 1, 2, 1, 2;
      0, 1, 2, 3, 0, 0;
      2, 4, 3, 2, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 4, 6, 7, 8, 10} =
      !![0, 2, 2, 1, 4, 4;
      0, 1, 0, 4, 1, 0;
      0, 2, 3, 2, 4, 3;
      0, 0, 3, 4, 4, 3;
      4, 3, 2, 4, 4, 3;
      3, 3, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1490 : Certificate {1, 4, 6, 7, 8, 10} := by
  refine ⟨!![3, 0, 0, 2, 2, 3;
      4, 4, 1, 4, 4, 1;
      2, 2, 3, 3, 1, 3;
      0, 4, 3, 1, 3, 2;
      1, 1, 2, 2, 4, 1;
      1, 3, 2, 4, 2, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 4, 6, 7, 8, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 1, 0, 4, 1, 0;
      3, 2, 3, 2, 4, 3;
      4, 0, 3, 4, 4, 3;
      4, 3, 2, 4, 4, 3;
      0, 3, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1492 : Certificate {2, 4, 6, 7, 8, 10} := by
  refine ⟨!![1, 0, 0, 4, 4, 1;
      3, 2, 2, 2, 1, 0;
      0, 1, 1, 1, 1, 1;
      4, 2, 4, 4, 0, 1;
      4, 3, 1, 2, 0, 4;
      1, 4, 4, 3, 4, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 4, 6, 7, 8, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 2, 2, 1, 4, 4;
      2, 2, 3, 2, 4, 3;
      0, 0, 3, 4, 4, 3;
      1, 3, 2, 4, 4, 3;
      2, 3, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1496 : Certificate {3, 4, 6, 7, 8, 10} := by
  refine ⟨!![1, 0, 0, 4, 4, 1;
      1, 3, 3, 0, 1, 3;
      0, 4, 4, 4, 0, 1;
      2, 4, 1, 3, 3, 4;
      4, 1, 4, 0, 4, 4;
      3, 1, 1, 3, 3, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 4, 6, 7, 8, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 2, 2, 1, 4, 4;
      2, 1, 0, 4, 1, 0;
      2, 0, 3, 4, 4, 3;
      4, 3, 2, 4, 4, 3;
      2, 3, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1505 : Certificate {0, 5, 6, 7, 8, 10} := by
  refine ⟨!![1, 0, 1, 0, 2, 1;
      3, 4, 3, 1, 3, 1;
      3, 1, 1, 1, 1, 2;
      4, 4, 0, 2, 4, 3;
      4, 0, 0, 2, 4, 3;
      2, 2, 4, 1, 4, 3], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {0, 5, 6, 7, 8, 10} =
      !![0, 4, 2, 1, 4, 4;
      0, 0, 0, 4, 1, 0;
      0, 2, 3, 2, 4, 3;
      0, 0, 3, 4, 1, 3;
      4, 4, 2, 4, 4, 3;
      3, 1, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1506 : Certificate {1, 5, 6, 7, 8, 10} := by
  refine ⟨!![1, 2, 2, 1, 2, 3;
      0, 4, 0, 1, 2, 3;
      4, 4, 1, 0, 3, 1;
      4, 2, 4, 1, 4, 1;
      4, 3, 4, 1, 4, 1;
      2, 1, 1, 3, 4, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {1, 5, 6, 7, 8, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 0, 0, 4, 1, 0;
      3, 2, 3, 2, 4, 3;
      2, 0, 3, 4, 1, 3;
      4, 4, 2, 4, 4, 3;
      0, 1, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1508 : Certificate {2, 5, 6, 7, 8, 10} := by
  refine ⟨!![0, 1, 1, 0, 2, 1;
      3, 2, 3, 4, 2, 4;
      2, 4, 1, 3, 2, 4;
      3, 3, 0, 0, 3, 1;
      0, 2, 3, 2, 0, 1;
      4, 1, 1, 0, 0, 4], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {2, 5, 6, 7, 8, 10} =
      !![0, 0, 4, 4, 4, 4;
      0, 4, 2, 1, 4, 4;
      2, 2, 3, 2, 4, 3;
      1, 0, 3, 4, 1, 3;
      1, 4, 2, 4, 4, 3;
      2, 1, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1512 : Certificate {3, 5, 6, 7, 8, 10} := by
  refine ⟨!![4, 2, 3, 4, 2, 4;
      4, 2, 2, 0, 4, 2;
      3, 1, 2, 4, 3, 4;
      1, 2, 1, 3, 2, 4;
      3, 3, 1, 0, 3, 1;
      2, 4, 1, 3, 2, 1], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {3, 5, 6, 7, 8, 10} =
      !![0, 0, 4, 4, 4, 4;
      3, 4, 2, 1, 4, 4;
      2, 0, 0, 4, 1, 0;
      2, 0, 3, 4, 1, 3;
      4, 4, 2, 4, 4, 3;
      2, 1, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1520 : Certificate {4, 5, 6, 7, 8, 10} := by
  refine ⟨!![0, 2, 0, 2, 4, 2;
      4, 4, 2, 2, 3, 4;
      4, 4, 4, 0, 1, 0;
      3, 2, 0, 4, 1, 0;
      3, 0, 1, 2, 2, 3;
      4, 4, 0, 4, 1, 2], ?_⟩
  have hc : executableCutMatrix (k := 6) (t := 6) graph {4, 5, 6, 7, 8, 10} =
      !![0, 0, 4, 4, 4, 4;
      2, 4, 2, 1, 4, 4;
      1, 0, 0, 4, 1, 0;
      2, 2, 3, 2, 4, 3;
      3, 4, 2, 4, 4, 3;
      3, 1, 1, 4, 4, 2] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 1415 then
    if mask < 1357 then
      if mask < 1326 then
        if mask < 1310 then
          if mask < 1307 then
            if mask < 1303 then
              ⟨{0, 1, 2, 3, 8, 10}, certificate_1295⟩
            else
              ⟨{0, 1, 2, 4, 8, 10}, certificate_1303⟩
          else
            if mask < 1309 then
              ⟨{0, 1, 3, 4, 8, 10}, certificate_1307⟩
            else
              ⟨{0, 2, 3, 4, 8, 10}, certificate_1309⟩
        else
          if mask < 1323 then
            if mask < 1319 then
              ⟨{1, 2, 3, 4, 8, 10}, certificate_1310⟩
            else
              ⟨{0, 1, 2, 5, 8, 10}, certificate_1319⟩
          else
            if mask < 1325 then
              ⟨{0, 1, 3, 5, 8, 10}, certificate_1323⟩
            else
              ⟨{0, 2, 3, 5, 8, 10}, certificate_1325⟩
      else
        if mask < 1337 then
          if mask < 1333 then
            if mask < 1331 then
              ⟨{1, 2, 3, 5, 8, 10}, certificate_1326⟩
            else
              ⟨{0, 1, 4, 5, 8, 10}, certificate_1331⟩
          else
            if mask < 1334 then
              ⟨{0, 2, 4, 5, 8, 10}, certificate_1333⟩
            else
              ⟨{1, 2, 4, 5, 8, 10}, certificate_1334⟩
        else
          if mask < 1340 then
            if mask < 1338 then
              ⟨{0, 3, 4, 5, 8, 10}, certificate_1337⟩
            else
              ⟨{1, 3, 4, 5, 8, 10}, certificate_1338⟩
          else
            if mask < 1351 then
              ⟨{2, 3, 4, 5, 8, 10}, certificate_1340⟩
            else
              if mask < 1355 then
                ⟨{0, 1, 2, 6, 8, 10}, certificate_1351⟩
              else
                ⟨{0, 1, 3, 6, 8, 10}, certificate_1355⟩
    else
      if mask < 1381 then
        if mask < 1366 then
          if mask < 1363 then
            if mask < 1358 then
              ⟨{0, 2, 3, 6, 8, 10}, certificate_1357⟩
            else
              ⟨{1, 2, 3, 6, 8, 10}, certificate_1358⟩
          else
            if mask < 1365 then
              ⟨{0, 1, 4, 6, 8, 10}, certificate_1363⟩
            else
              ⟨{0, 2, 4, 6, 8, 10}, certificate_1365⟩
        else
          if mask < 1370 then
            if mask < 1369 then
              ⟨{1, 2, 4, 6, 8, 10}, certificate_1366⟩
            else
              ⟨{0, 3, 4, 6, 8, 10}, certificate_1369⟩
          else
            if mask < 1372 then
              ⟨{1, 3, 4, 6, 8, 10}, certificate_1370⟩
            else
              if mask < 1379 then
                ⟨{2, 3, 4, 6, 8, 10}, certificate_1372⟩
              else
                ⟨{0, 1, 5, 6, 8, 10}, certificate_1379⟩
      else
        if mask < 1388 then
          if mask < 1385 then
            if mask < 1382 then
              ⟨{0, 2, 5, 6, 8, 10}, certificate_1381⟩
            else
              ⟨{1, 2, 5, 6, 8, 10}, certificate_1382⟩
          else
            if mask < 1386 then
              ⟨{0, 3, 5, 6, 8, 10}, certificate_1385⟩
            else
              ⟨{1, 3, 5, 6, 8, 10}, certificate_1386⟩
        else
          if mask < 1394 then
            if mask < 1393 then
              ⟨{2, 3, 5, 6, 8, 10}, certificate_1388⟩
            else
              ⟨{0, 4, 5, 6, 8, 10}, certificate_1393⟩
          else
            if mask < 1396 then
              ⟨{1, 4, 5, 6, 8, 10}, certificate_1394⟩
            else
              if mask < 1400 then
                ⟨{2, 4, 5, 6, 8, 10}, certificate_1396⟩
              else
                ⟨{3, 4, 5, 6, 8, 10}, certificate_1400⟩
  else
    if mask < 1458 then
      if mask < 1434 then
        if mask < 1427 then
          if mask < 1421 then
            if mask < 1419 then
              ⟨{0, 1, 2, 7, 8, 10}, certificate_1415⟩
            else
              ⟨{0, 1, 3, 7, 8, 10}, certificate_1419⟩
          else
            if mask < 1422 then
              ⟨{0, 2, 3, 7, 8, 10}, certificate_1421⟩
            else
              ⟨{1, 2, 3, 7, 8, 10}, certificate_1422⟩
        else
          if mask < 1430 then
            if mask < 1429 then
              ⟨{0, 1, 4, 7, 8, 10}, certificate_1427⟩
            else
              ⟨{0, 2, 4, 7, 8, 10}, certificate_1429⟩
          else
            if mask < 1433 then
              ⟨{1, 2, 4, 7, 8, 10}, certificate_1430⟩
            else
              ⟨{0, 3, 4, 7, 8, 10}, certificate_1433⟩
      else
        if mask < 1446 then
          if mask < 1443 then
            if mask < 1436 then
              ⟨{1, 3, 4, 7, 8, 10}, certificate_1434⟩
            else
              ⟨{2, 3, 4, 7, 8, 10}, certificate_1436⟩
          else
            if mask < 1445 then
              ⟨{0, 1, 5, 7, 8, 10}, certificate_1443⟩
            else
              ⟨{0, 2, 5, 7, 8, 10}, certificate_1445⟩
        else
          if mask < 1450 then
            if mask < 1449 then
              ⟨{1, 2, 5, 7, 8, 10}, certificate_1446⟩
            else
              ⟨{0, 3, 5, 7, 8, 10}, certificate_1449⟩
          else
            if mask < 1452 then
              ⟨{1, 3, 5, 7, 8, 10}, certificate_1450⟩
            else
              if mask < 1457 then
                ⟨{2, 3, 5, 7, 8, 10}, certificate_1452⟩
              else
                ⟨{0, 4, 5, 7, 8, 10}, certificate_1457⟩
    else
      if mask < 1489 then
        if mask < 1477 then
          if mask < 1464 then
            if mask < 1460 then
              ⟨{1, 4, 5, 7, 8, 10}, certificate_1458⟩
            else
              ⟨{2, 4, 5, 7, 8, 10}, certificate_1460⟩
          else
            if mask < 1475 then
              ⟨{3, 4, 5, 7, 8, 10}, certificate_1464⟩
            else
              ⟨{0, 1, 6, 7, 8, 10}, certificate_1475⟩
        else
          if mask < 1481 then
            if mask < 1478 then
              ⟨{0, 2, 6, 7, 8, 10}, certificate_1477⟩
            else
              ⟨{1, 2, 6, 7, 8, 10}, certificate_1478⟩
          else
            if mask < 1482 then
              ⟨{0, 3, 6, 7, 8, 10}, certificate_1481⟩
            else
              if mask < 1484 then
                ⟨{1, 3, 6, 7, 8, 10}, certificate_1482⟩
              else
                ⟨{2, 3, 6, 7, 8, 10}, certificate_1484⟩
      else
        if mask < 1505 then
          if mask < 1492 then
            if mask < 1490 then
              ⟨{0, 4, 6, 7, 8, 10}, certificate_1489⟩
            else
              ⟨{1, 4, 6, 7, 8, 10}, certificate_1490⟩
          else
            if mask < 1496 then
              ⟨{2, 4, 6, 7, 8, 10}, certificate_1492⟩
            else
              ⟨{3, 4, 6, 7, 8, 10}, certificate_1496⟩
        else
          if mask < 1508 then
            if mask < 1506 then
              ⟨{0, 5, 6, 7, 8, 10}, certificate_1505⟩
            else
              ⟨{1, 5, 6, 7, 8, 10}, certificate_1506⟩
          else
            if mask < 1512 then
              ⟨{2, 5, 6, 7, 8, 10}, certificate_1508⟩
            else
              if mask < 1520 then
                ⟨{3, 5, 6, 7, 8, 10}, certificate_1512⟩
              else
                ⟨{4, 5, 6, 7, 8, 10}, certificate_1520⟩
end AMEProbe.QuinaryDirect.Batch05
#print axioms AMEProbe.QuinaryDirect.Batch05.lookup
