import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch05
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_1287 : Certificate {0, 1, 2, 8, 10} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 8, 10} =
      !![1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 1;
      1, 0, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1291 : Certificate {0, 1, 3, 8, 10} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 8, 10} =
      !![0, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1293 : Certificate {0, 2, 3, 8, 10} := by
  refine ⟨!![1, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 8, 10} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1294 : Certificate {1, 2, 3, 8, 10} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 8, 10} =
      !![0, 0, 1, 0, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1299 : Certificate {0, 1, 4, 8, 10} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 1;
      0, 1, 0, 0, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 8, 10} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 1;
      1, 0, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1301 : Certificate {0, 2, 4, 8, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 8, 10} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1302 : Certificate {1, 2, 4, 8, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 1, 1, 0;
      0, 0, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 8, 10} =
      !![0, 0, 0, 0, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1305 : Certificate {0, 3, 4, 8, 10} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 8, 10} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1306 : Certificate {1, 3, 4, 8, 10} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 8, 10} =
      !![0, 1, 0, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1308 : Certificate {2, 3, 4, 8, 10} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 1;
      0, 1, 1, 0, 0, 0, 1;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 8, 10} =
      !![0, 1, 0, 0, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1315 : Certificate {0, 1, 5, 8, 10} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 8, 10} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1317 : Certificate {0, 2, 5, 8, 10} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 1;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 8, 10} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1318 : Certificate {1, 2, 5, 8, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 8, 10} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1321 : Certificate {0, 3, 5, 8, 10} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 8, 10} =
      !![0, 0, 0, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1322 : Certificate {1, 3, 5, 8, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0;
      0, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1324 : Certificate {2, 3, 5, 8, 10} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1329 : Certificate {0, 4, 5, 8, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 8, 10} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1330 : Certificate {1, 4, 5, 8, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 8, 10} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1332 : Certificate {2, 4, 5, 8, 10} := by
  refine ⟨!![0, 1, 1, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 1, 0;
      0, 0, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 8, 10} =
      !![0, 0, 1, 0, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1336 : Certificate {3, 4, 5, 8, 10} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 8, 10} =
      !![1, 0, 1, 0, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1347 : Certificate {0, 1, 6, 8, 10} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 6, 8, 10} =
      !![0, 0, 0, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1349 : Certificate {0, 2, 6, 8, 10} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 6, 8, 10} =
      !![0, 0, 1, 1, 1;
      1, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1350 : Certificate {1, 2, 6, 8, 10} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 1;
      1, 0, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 6, 8, 10} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1353 : Certificate {0, 3, 6, 8, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 6, 8, 10} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1354 : Certificate {1, 3, 6, 8, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 6, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1356 : Certificate {2, 3, 6, 8, 10} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 6, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1361 : Certificate {0, 4, 6, 8, 10} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 6, 8, 10} =
      !![0, 1, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1362 : Certificate {1, 4, 6, 8, 10} := by
  refine ⟨!![0, 1, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 6, 8, 10} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1364 : Certificate {2, 4, 6, 8, 10} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 6, 8, 10} =
      !![0, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1368 : Certificate {3, 4, 6, 8, 10} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 6, 8, 10} =
      !![1, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1377 : Certificate {0, 5, 6, 8, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 6, 8, 10} =
      !![0, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1378 : Certificate {1, 5, 6, 8, 10} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 6, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      0, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1380 : Certificate {2, 5, 6, 8, 10} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 1, 0;
      0, 0, 0, 1, 1, 1, 0;
      0, 1, 0, 0, 1, 1, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 6, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1384 : Certificate {3, 5, 6, 8, 10} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 6, 8, 10} =
      !![1, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1392 : Certificate {4, 5, 6, 8, 10} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 6, 8, 10} =
      !![0, 1, 1, 0, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1411 : Certificate {0, 1, 7, 8, 10} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 7, 8, 10} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1413 : Certificate {0, 2, 7, 8, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 7, 8, 10} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1414 : Certificate {1, 2, 7, 8, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 7, 8, 10} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1417 : Certificate {0, 3, 7, 8, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 7, 8, 10} =
      !![0, 0, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1418 : Certificate {1, 3, 7, 8, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 7, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1420 : Certificate {2, 3, 7, 8, 10} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 7, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1425 : Certificate {0, 4, 7, 8, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 7, 8, 10} =
      !![0, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1426 : Certificate {1, 4, 7, 8, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 7, 8, 10} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1428 : Certificate {2, 4, 7, 8, 10} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 7, 8, 10} =
      !![0, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1432 : Certificate {3, 4, 7, 8, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 7, 8, 10} =
      !![1, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1441 : Certificate {0, 5, 7, 8, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 7, 8, 10} =
      !![0, 0, 1, 1, 1;
      0, 1, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1442 : Certificate {1, 5, 7, 8, 10} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 7, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      0, 0, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1444 : Certificate {2, 5, 7, 8, 10} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 7, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1448 : Certificate {3, 5, 7, 8, 10} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 1;
      0, 0, 1, 0, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 7, 8, 10} =
      !![1, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1456 : Certificate {4, 5, 7, 8, 10} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 7, 8, 10} =
      !![0, 1, 1, 0, 0;
      1, 0, 1, 1, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1473 : Certificate {0, 6, 7, 8, 10} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 6, 7, 8, 10} =
      !![0, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      1, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1474 : Certificate {1, 6, 7, 8, 10} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 6, 7, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1476 : Certificate {2, 6, 7, 8, 10} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 6, 7, 8, 10} =
      !![0, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1480 : Certificate {3, 6, 7, 8, 10} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 6, 7, 8, 10} =
      !![1, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1488 : Certificate {4, 6, 7, 8, 10} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 6, 7, 8, 10} =
      !![0, 1, 1, 0, 0;
      1, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1504 : Certificate {5, 6, 7, 8, 10} := by
  refine ⟨!![1, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 6, 7, 8, 10} =
      !![1, 1, 1, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 1364 then
    if mask < 1322 then
      if mask < 1305 then
        if mask < 1294 then
          if mask < 1291 then
            ⟨{0, 1, 2, 8, 10}, certificate_1287⟩
          else
            if mask < 1293 then
              ⟨{0, 1, 3, 8, 10}, certificate_1291⟩
            else
              ⟨{0, 2, 3, 8, 10}, certificate_1293⟩
        else
          if mask < 1301 then
            if mask < 1299 then
              ⟨{1, 2, 3, 8, 10}, certificate_1294⟩
            else
              ⟨{0, 1, 4, 8, 10}, certificate_1299⟩
          else
            if mask < 1302 then
              ⟨{0, 2, 4, 8, 10}, certificate_1301⟩
            else
              ⟨{1, 2, 4, 8, 10}, certificate_1302⟩
      else
        if mask < 1315 then
          if mask < 1306 then
            ⟨{0, 3, 4, 8, 10}, certificate_1305⟩
          else
            if mask < 1308 then
              ⟨{1, 3, 4, 8, 10}, certificate_1306⟩
            else
              ⟨{2, 3, 4, 8, 10}, certificate_1308⟩
        else
          if mask < 1318 then
            if mask < 1317 then
              ⟨{0, 1, 5, 8, 10}, certificate_1315⟩
            else
              ⟨{0, 2, 5, 8, 10}, certificate_1317⟩
          else
            if mask < 1321 then
              ⟨{1, 2, 5, 8, 10}, certificate_1318⟩
            else
              ⟨{0, 3, 5, 8, 10}, certificate_1321⟩
    else
      if mask < 1349 then
        if mask < 1330 then
          if mask < 1324 then
            ⟨{1, 3, 5, 8, 10}, certificate_1322⟩
          else
            if mask < 1329 then
              ⟨{2, 3, 5, 8, 10}, certificate_1324⟩
            else
              ⟨{0, 4, 5, 8, 10}, certificate_1329⟩
        else
          if mask < 1336 then
            if mask < 1332 then
              ⟨{1, 4, 5, 8, 10}, certificate_1330⟩
            else
              ⟨{2, 4, 5, 8, 10}, certificate_1332⟩
          else
            if mask < 1347 then
              ⟨{3, 4, 5, 8, 10}, certificate_1336⟩
            else
              ⟨{0, 1, 6, 8, 10}, certificate_1347⟩
      else
        if mask < 1354 then
          if mask < 1350 then
            ⟨{0, 2, 6, 8, 10}, certificate_1349⟩
          else
            if mask < 1353 then
              ⟨{1, 2, 6, 8, 10}, certificate_1350⟩
            else
              ⟨{0, 3, 6, 8, 10}, certificate_1353⟩
        else
          if mask < 1361 then
            if mask < 1356 then
              ⟨{1, 3, 6, 8, 10}, certificate_1354⟩
            else
              ⟨{2, 3, 6, 8, 10}, certificate_1356⟩
          else
            if mask < 1362 then
              ⟨{0, 4, 6, 8, 10}, certificate_1361⟩
            else
              ⟨{1, 4, 6, 8, 10}, certificate_1362⟩
  else
    if mask < 1426 then
      if mask < 1411 then
        if mask < 1378 then
          if mask < 1368 then
            ⟨{2, 4, 6, 8, 10}, certificate_1364⟩
          else
            if mask < 1377 then
              ⟨{3, 4, 6, 8, 10}, certificate_1368⟩
            else
              ⟨{0, 5, 6, 8, 10}, certificate_1377⟩
        else
          if mask < 1384 then
            if mask < 1380 then
              ⟨{1, 5, 6, 8, 10}, certificate_1378⟩
            else
              ⟨{2, 5, 6, 8, 10}, certificate_1380⟩
          else
            if mask < 1392 then
              ⟨{3, 5, 6, 8, 10}, certificate_1384⟩
            else
              ⟨{4, 5, 6, 8, 10}, certificate_1392⟩
      else
        if mask < 1417 then
          if mask < 1413 then
            ⟨{0, 1, 7, 8, 10}, certificate_1411⟩
          else
            if mask < 1414 then
              ⟨{0, 2, 7, 8, 10}, certificate_1413⟩
            else
              ⟨{1, 2, 7, 8, 10}, certificate_1414⟩
        else
          if mask < 1420 then
            if mask < 1418 then
              ⟨{0, 3, 7, 8, 10}, certificate_1417⟩
            else
              ⟨{1, 3, 7, 8, 10}, certificate_1418⟩
          else
            if mask < 1425 then
              ⟨{2, 3, 7, 8, 10}, certificate_1420⟩
            else
              ⟨{0, 4, 7, 8, 10}, certificate_1425⟩
    else
      if mask < 1456 then
        if mask < 1441 then
          if mask < 1428 then
            ⟨{1, 4, 7, 8, 10}, certificate_1426⟩
          else
            if mask < 1432 then
              ⟨{2, 4, 7, 8, 10}, certificate_1428⟩
            else
              ⟨{3, 4, 7, 8, 10}, certificate_1432⟩
        else
          if mask < 1444 then
            if mask < 1442 then
              ⟨{0, 5, 7, 8, 10}, certificate_1441⟩
            else
              ⟨{1, 5, 7, 8, 10}, certificate_1442⟩
          else
            if mask < 1448 then
              ⟨{2, 5, 7, 8, 10}, certificate_1444⟩
            else
              ⟨{3, 5, 7, 8, 10}, certificate_1448⟩
      else
        if mask < 1476 then
          if mask < 1473 then
            ⟨{4, 5, 7, 8, 10}, certificate_1456⟩
          else
            if mask < 1474 then
              ⟨{0, 6, 7, 8, 10}, certificate_1473⟩
            else
              ⟨{1, 6, 7, 8, 10}, certificate_1474⟩
        else
          if mask < 1488 then
            if mask < 1480 then
              ⟨{2, 6, 7, 8, 10}, certificate_1476⟩
            else
              ⟨{3, 6, 7, 8, 10}, certificate_1480⟩
          else
            if mask < 1504 then
              ⟨{4, 6, 7, 8, 10}, certificate_1488⟩
            else
              ⟨{5, 6, 7, 8, 10}, certificate_1504⟩
end AMEProbe.BinaryDirect.Batch05
#print axioms AMEProbe.BinaryDirect.Batch05.lookup
