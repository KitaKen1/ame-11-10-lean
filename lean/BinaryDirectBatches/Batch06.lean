import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch06
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_1543 : Certificate {0, 1, 2, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 9, 10} =
      !![1, 0, 0, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1547 : Certificate {0, 1, 3, 9, 10} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 9, 10} =
      !![0, 0, 0, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1549 : Certificate {0, 2, 3, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 9, 10} =
      !![0, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1550 : Certificate {1, 2, 3, 9, 10} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1;
      0, 0, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 9, 10} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 1, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1555 : Certificate {0, 1, 4, 9, 10} := by
  refine ⟨!![1, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 9, 10} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1557 : Certificate {0, 2, 4, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 9, 10} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1558 : Certificate {1, 2, 4, 9, 10} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 9, 10} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1561 : Certificate {0, 3, 4, 9, 10} := by
  refine ⟨!![1, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 9, 10} =
      !![0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1562 : Certificate {1, 3, 4, 9, 10} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 9, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1564 : Certificate {2, 3, 4, 9, 10} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 1, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 1, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 9, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1571 : Certificate {0, 1, 5, 9, 10} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 9, 10} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 1, 1;
      1, 1, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1573 : Certificate {0, 2, 5, 9, 10} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 1, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 9, 10} =
      !![0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1574 : Certificate {1, 2, 5, 9, 10} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 9, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1577 : Certificate {0, 3, 5, 9, 10} := by
  refine ⟨!![1, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 9, 10} =
      !![0, 0, 0, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1578 : Certificate {1, 3, 5, 9, 10} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1580 : Certificate {2, 3, 5, 9, 10} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1585 : Certificate {0, 4, 5, 9, 10} := by
  refine ⟨!![1, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 9, 10} =
      !![0, 1, 0, 0, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 0, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1586 : Certificate {1, 4, 5, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 1;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 1;
      1, 0, 1, 1, 1, 0, 1;
      1, 0, 0, 1, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 9, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1588 : Certificate {2, 4, 5, 9, 10} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 9, 10} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 0, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1592 : Certificate {3, 4, 5, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 1;
      1, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 9, 10} =
      !![1, 0, 1, 1, 0;
      0, 1, 0, 0, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1603 : Certificate {0, 1, 6, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 6, 9, 10} =
      !![0, 0, 0, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1605 : Certificate {0, 2, 6, 9, 10} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 6, 9, 10} =
      !![0, 0, 1, 0, 1;
      1, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1606 : Certificate {1, 2, 6, 9, 10} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 6, 9, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1609 : Certificate {0, 3, 6, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 6, 9, 10} =
      !![0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1610 : Certificate {1, 3, 6, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 6, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1612 : Certificate {2, 3, 6, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 6, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1617 : Certificate {0, 4, 6, 9, 10} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 6, 9, 10} =
      !![0, 1, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      0, 0, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1618 : Certificate {1, 4, 6, 9, 10} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 0, 1, 0, 1, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 6, 9, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1620 : Certificate {2, 4, 6, 9, 10} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 6, 9, 10} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1624 : Certificate {3, 4, 6, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 6, 9, 10} =
      !![1, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1633 : Certificate {0, 5, 6, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 6, 9, 10} =
      !![0, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1634 : Certificate {1, 5, 6, 9, 10} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 6, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1636 : Certificate {2, 5, 6, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 6, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1640 : Certificate {3, 5, 6, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 6, 9, 10} =
      !![1, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1648 : Certificate {4, 5, 6, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 6, 9, 10} =
      !![0, 1, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1667 : Certificate {0, 1, 7, 9, 10} := by
  refine ⟨!![1, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 7, 9, 10} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 0, 0, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1669 : Certificate {0, 2, 7, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 7, 9, 10} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1670 : Certificate {1, 2, 7, 9, 10} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 1;
      0, 0, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 7, 9, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1673 : Certificate {0, 3, 7, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 7, 9, 10} =
      !![0, 0, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 0, 0, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1674 : Certificate {1, 3, 7, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 7, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1676 : Certificate {2, 3, 7, 9, 10} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 7, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1681 : Certificate {0, 4, 7, 9, 10} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 7, 9, 10} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      0, 0, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1682 : Certificate {1, 4, 7, 9, 10} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 7, 9, 10} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1684 : Certificate {2, 4, 7, 9, 10} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 7, 9, 10} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1688 : Certificate {3, 4, 7, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 7, 9, 10} =
      !![1, 0, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1697 : Certificate {0, 5, 7, 9, 10} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 7, 9, 10} =
      !![0, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1698 : Certificate {1, 5, 7, 9, 10} := by
  refine ⟨!![1, 0, 1, 1, 1, 1, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 1, 1, 0;
      1, 0, 1, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 7, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1700 : Certificate {2, 5, 7, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 7, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1704 : Certificate {3, 5, 7, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 7, 9, 10} =
      !![1, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1712 : Certificate {4, 5, 7, 9, 10} := by
  refine ⟨!![1, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 1, 1, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 7, 9, 10} =
      !![0, 1, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1729 : Certificate {0, 6, 7, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      1, 0, 0, 1, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 6, 7, 9, 10} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      1, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1730 : Certificate {1, 6, 7, 9, 10} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 6, 7, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1732 : Certificate {2, 6, 7, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 6, 7, 9, 10} =
      !![0, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1736 : Certificate {3, 6, 7, 9, 10} := by
  refine ⟨!![0, 0, 0, 0, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 6, 7, 9, 10} =
      !![1, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1744 : Certificate {4, 6, 7, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 6, 7, 9, 10} =
      !![0, 1, 1, 1, 0;
      1, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1760 : Certificate {5, 6, 7, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 6, 7, 9, 10} =
      !![1, 1, 1, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 1620 then
    if mask < 1578 then
      if mask < 1561 then
        if mask < 1550 then
          if mask < 1547 then
            ⟨{0, 1, 2, 9, 10}, certificate_1543⟩
          else
            if mask < 1549 then
              ⟨{0, 1, 3, 9, 10}, certificate_1547⟩
            else
              ⟨{0, 2, 3, 9, 10}, certificate_1549⟩
        else
          if mask < 1557 then
            if mask < 1555 then
              ⟨{1, 2, 3, 9, 10}, certificate_1550⟩
            else
              ⟨{0, 1, 4, 9, 10}, certificate_1555⟩
          else
            if mask < 1558 then
              ⟨{0, 2, 4, 9, 10}, certificate_1557⟩
            else
              ⟨{1, 2, 4, 9, 10}, certificate_1558⟩
      else
        if mask < 1571 then
          if mask < 1562 then
            ⟨{0, 3, 4, 9, 10}, certificate_1561⟩
          else
            if mask < 1564 then
              ⟨{1, 3, 4, 9, 10}, certificate_1562⟩
            else
              ⟨{2, 3, 4, 9, 10}, certificate_1564⟩
        else
          if mask < 1574 then
            if mask < 1573 then
              ⟨{0, 1, 5, 9, 10}, certificate_1571⟩
            else
              ⟨{0, 2, 5, 9, 10}, certificate_1573⟩
          else
            if mask < 1577 then
              ⟨{1, 2, 5, 9, 10}, certificate_1574⟩
            else
              ⟨{0, 3, 5, 9, 10}, certificate_1577⟩
    else
      if mask < 1605 then
        if mask < 1586 then
          if mask < 1580 then
            ⟨{1, 3, 5, 9, 10}, certificate_1578⟩
          else
            if mask < 1585 then
              ⟨{2, 3, 5, 9, 10}, certificate_1580⟩
            else
              ⟨{0, 4, 5, 9, 10}, certificate_1585⟩
        else
          if mask < 1592 then
            if mask < 1588 then
              ⟨{1, 4, 5, 9, 10}, certificate_1586⟩
            else
              ⟨{2, 4, 5, 9, 10}, certificate_1588⟩
          else
            if mask < 1603 then
              ⟨{3, 4, 5, 9, 10}, certificate_1592⟩
            else
              ⟨{0, 1, 6, 9, 10}, certificate_1603⟩
      else
        if mask < 1610 then
          if mask < 1606 then
            ⟨{0, 2, 6, 9, 10}, certificate_1605⟩
          else
            if mask < 1609 then
              ⟨{1, 2, 6, 9, 10}, certificate_1606⟩
            else
              ⟨{0, 3, 6, 9, 10}, certificate_1609⟩
        else
          if mask < 1617 then
            if mask < 1612 then
              ⟨{1, 3, 6, 9, 10}, certificate_1610⟩
            else
              ⟨{2, 3, 6, 9, 10}, certificate_1612⟩
          else
            if mask < 1618 then
              ⟨{0, 4, 6, 9, 10}, certificate_1617⟩
            else
              ⟨{1, 4, 6, 9, 10}, certificate_1618⟩
  else
    if mask < 1682 then
      if mask < 1667 then
        if mask < 1634 then
          if mask < 1624 then
            ⟨{2, 4, 6, 9, 10}, certificate_1620⟩
          else
            if mask < 1633 then
              ⟨{3, 4, 6, 9, 10}, certificate_1624⟩
            else
              ⟨{0, 5, 6, 9, 10}, certificate_1633⟩
        else
          if mask < 1640 then
            if mask < 1636 then
              ⟨{1, 5, 6, 9, 10}, certificate_1634⟩
            else
              ⟨{2, 5, 6, 9, 10}, certificate_1636⟩
          else
            if mask < 1648 then
              ⟨{3, 5, 6, 9, 10}, certificate_1640⟩
            else
              ⟨{4, 5, 6, 9, 10}, certificate_1648⟩
      else
        if mask < 1673 then
          if mask < 1669 then
            ⟨{0, 1, 7, 9, 10}, certificate_1667⟩
          else
            if mask < 1670 then
              ⟨{0, 2, 7, 9, 10}, certificate_1669⟩
            else
              ⟨{1, 2, 7, 9, 10}, certificate_1670⟩
        else
          if mask < 1676 then
            if mask < 1674 then
              ⟨{0, 3, 7, 9, 10}, certificate_1673⟩
            else
              ⟨{1, 3, 7, 9, 10}, certificate_1674⟩
          else
            if mask < 1681 then
              ⟨{2, 3, 7, 9, 10}, certificate_1676⟩
            else
              ⟨{0, 4, 7, 9, 10}, certificate_1681⟩
    else
      if mask < 1712 then
        if mask < 1697 then
          if mask < 1684 then
            ⟨{1, 4, 7, 9, 10}, certificate_1682⟩
          else
            if mask < 1688 then
              ⟨{2, 4, 7, 9, 10}, certificate_1684⟩
            else
              ⟨{3, 4, 7, 9, 10}, certificate_1688⟩
        else
          if mask < 1700 then
            if mask < 1698 then
              ⟨{0, 5, 7, 9, 10}, certificate_1697⟩
            else
              ⟨{1, 5, 7, 9, 10}, certificate_1698⟩
          else
            if mask < 1704 then
              ⟨{2, 5, 7, 9, 10}, certificate_1700⟩
            else
              ⟨{3, 5, 7, 9, 10}, certificate_1704⟩
      else
        if mask < 1732 then
          if mask < 1729 then
            ⟨{4, 5, 7, 9, 10}, certificate_1712⟩
          else
            if mask < 1730 then
              ⟨{0, 6, 7, 9, 10}, certificate_1729⟩
            else
              ⟨{1, 6, 7, 9, 10}, certificate_1730⟩
        else
          if mask < 1744 then
            if mask < 1736 then
              ⟨{2, 6, 7, 9, 10}, certificate_1732⟩
            else
              ⟨{3, 6, 7, 9, 10}, certificate_1736⟩
          else
            if mask < 1760 then
              ⟨{4, 6, 7, 9, 10}, certificate_1744⟩
            else
              ⟨{5, 6, 7, 9, 10}, certificate_1760⟩
end AMEProbe.BinaryDirect.Batch06
#print axioms AMEProbe.BinaryDirect.Batch06.lookup
