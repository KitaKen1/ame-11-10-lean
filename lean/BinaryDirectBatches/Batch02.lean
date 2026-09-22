import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch02
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_527 : Certificate {0, 1, 2, 3, 9} := by
  refine ⟨!![1, 1, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 3, 9} =
      !![0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_535 : Certificate {0, 1, 2, 4, 9} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 4, 9} =
      !![1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_539 : Certificate {0, 1, 3, 4, 9} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 4, 9} =
      !![0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_541 : Certificate {0, 2, 3, 4, 9} := by
  refine ⟨!![1, 1, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 4, 9} =
      !![0, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_542 : Certificate {1, 2, 3, 4, 9} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 4, 9} =
      !![0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_551 : Certificate {0, 1, 2, 5, 9} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 5, 9} =
      !![1, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_555 : Certificate {0, 1, 3, 5, 9} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 5, 9} =
      !![0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_557 : Certificate {0, 2, 3, 5, 9} := by
  refine ⟨!![0, 0, 0, 1, 1, 1, 0;
      0, 0, 0, 0, 1, 1, 0;
      0, 1, 1, 1, 1, 1, 0;
      0, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 5, 9} =
      !![0, 0, 0, 0, 0;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_558 : Certificate {1, 2, 3, 5, 9} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 5, 9} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_563 : Certificate {0, 1, 4, 5, 9} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 5, 9} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_565 : Certificate {0, 2, 4, 5, 9} := by
  refine ⟨!![0, 0, 0, 1, 1, 1, 0;
      1, 0, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 5, 9} =
      !![0, 0, 1, 0, 0;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_566 : Certificate {1, 2, 4, 5, 9} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 5, 9} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_569 : Certificate {0, 3, 4, 5, 9} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 5, 9} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_570 : Certificate {1, 3, 4, 5, 9} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 5, 9} =
      !![0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_572 : Certificate {2, 3, 4, 5, 9} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 5, 9} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 0, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_583 : Certificate {0, 1, 2, 6, 9} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 6, 9} =
      !![1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_587 : Certificate {0, 1, 3, 6, 9} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 6, 9} =
      !![0, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_589 : Certificate {0, 2, 3, 6, 9} := by
  refine ⟨!![0, 0, 1, 0, 1, 1, 0;
      0, 0, 0, 0, 1, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 6, 9} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_590 : Certificate {1, 2, 3, 6, 9} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 6, 9} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_595 : Certificate {0, 1, 4, 6, 9} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 6, 9} =
      !![0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_597 : Certificate {0, 2, 4, 6, 9} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 6, 9} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_598 : Certificate {1, 2, 4, 6, 9} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 1;
      1, 0, 1, 1, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 6, 9} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_601 : Certificate {0, 3, 4, 6, 9} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 6, 9} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_602 : Certificate {1, 3, 4, 6, 9} := by
  refine ⟨!![0, 0, 0, 1, 1, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 1, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 6, 9} =
      !![0, 1, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_604 : Certificate {2, 3, 4, 6, 9} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 6, 9} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_611 : Certificate {0, 1, 5, 6, 9} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 6, 9} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_613 : Certificate {0, 2, 5, 6, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 6, 9} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_614 : Certificate {1, 2, 5, 6, 9} := by
  refine ⟨!![1, 1, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 6, 9} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_617 : Certificate {0, 3, 5, 6, 9} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 6, 9} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_618 : Certificate {1, 3, 5, 6, 9} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 6, 9} =
      !![0, 1, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_620 : Certificate {2, 3, 5, 6, 9} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 6, 9} =
      !![0, 1, 1, 1, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_625 : Certificate {0, 4, 5, 6, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 6, 9} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_626 : Certificate {1, 4, 5, 6, 9} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 6, 9} =
      !![0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_628 : Certificate {2, 4, 5, 6, 9} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 6, 9} =
      !![0, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_632 : Certificate {3, 4, 5, 6, 9} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 6, 9} =
      !![1, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_647 : Certificate {0, 1, 2, 7, 9} := by
  refine ⟨!![1, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 7, 9} =
      !![1, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_651 : Certificate {0, 1, 3, 7, 9} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 7, 9} =
      !![0, 0, 0, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_653 : Certificate {0, 2, 3, 7, 9} := by
  refine ⟨!![0, 1, 0, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 7, 9} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_654 : Certificate {1, 2, 3, 7, 9} := by
  refine ⟨!![0, 1, 0, 1, 0, 1, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 7, 9} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_659 : Certificate {0, 1, 4, 7, 9} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 7, 9} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_661 : Certificate {0, 2, 4, 7, 9} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 1;
      1, 0, 0, 0, 1, 0, 1;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 7, 9} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_662 : Certificate {1, 2, 4, 7, 9} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 7, 9} =
      !![0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_665 : Certificate {0, 3, 4, 7, 9} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 7, 9} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_666 : Certificate {1, 3, 4, 7, 9} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 7, 9} =
      !![0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_668 : Certificate {2, 3, 4, 7, 9} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 7, 9} =
      !![0, 1, 0, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_675 : Certificate {0, 1, 5, 7, 9} := by
  refine ⟨!![1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 7, 9} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_677 : Certificate {0, 2, 5, 7, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 7, 9} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_678 : Certificate {1, 2, 5, 7, 9} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 7, 9} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_681 : Certificate {0, 3, 5, 7, 9} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 7, 9} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_682 : Certificate {1, 3, 5, 7, 9} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 7, 9} =
      !![0, 1, 1, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_684 : Certificate {2, 3, 5, 7, 9} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 7, 9} =
      !![0, 1, 1, 1, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_689 : Certificate {0, 4, 5, 7, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 1;
      0, 0, 0, 0, 1, 0, 1;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 1;
      1, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 7, 9} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      0, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_690 : Certificate {1, 4, 5, 7, 9} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 7, 9} =
      !![0, 0, 1, 1, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_692 : Certificate {2, 4, 5, 7, 9} := by
  refine ⟨!![0, 1, 0, 0, 1, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 7, 9} =
      !![0, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_696 : Certificate {3, 4, 5, 7, 9} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 7, 9} =
      !![1, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_707 : Certificate {0, 1, 6, 7, 9} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 6, 7, 9} =
      !![0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_709 : Certificate {0, 2, 6, 7, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 6, 7, 9} =
      !![0, 0, 1, 1, 0;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_710 : Certificate {1, 2, 6, 7, 9} := by
  refine ⟨!![0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 6, 7, 9} =
      !![0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 0, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_713 : Certificate {0, 3, 6, 7, 9} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 1, 0;
      0, 0, 0, 0, 1, 1, 0;
      0, 1, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 6, 7, 9} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_714 : Certificate {1, 3, 6, 7, 9} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 1, 0;
      0, 1, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 6, 7, 9} =
      !![0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_716 : Certificate {2, 3, 6, 7, 9} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 6, 7, 9} =
      !![0, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_721 : Certificate {0, 4, 6, 7, 9} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 6, 7, 9} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      0, 0, 0, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_722 : Certificate {1, 4, 6, 7, 9} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 6, 7, 9} =
      !![0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_724 : Certificate {2, 4, 6, 7, 9} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 0, 0, 0, 1, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 6, 7, 9} =
      !![0, 0, 1, 1, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_728 : Certificate {3, 4, 6, 7, 9} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 1;
      1, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 1;
      0, 1, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 6, 7, 9} =
      !![1, 0, 1, 1, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_737 : Certificate {0, 5, 6, 7, 9} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 6, 7, 9} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_738 : Certificate {1, 5, 6, 7, 9} := by
  refine ⟨!![1, 0, 1, 0, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 6, 7, 9} =
      !![0, 1, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_740 : Certificate {2, 5, 6, 7, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 1;
      1, 1, 1, 0, 1, 0, 1;
      0, 0, 0, 0, 1, 0, 1;
      0, 1, 0, 0, 1, 0, 1;
      0, 0, 1, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 6, 7, 9} =
      !![0, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_744 : Certificate {3, 5, 6, 7, 9} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 6, 7, 9} =
      !![1, 1, 1, 1, 1;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_752 : Certificate {4, 5, 6, 7, 9} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 6, 7, 9} =
      !![0, 1, 1, 1, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 647 then
    if mask < 589 then
      if mask < 558 then
        if mask < 542 then
          if mask < 539 then
            if mask < 535 then
              ⟨{0, 1, 2, 3, 9}, certificate_527⟩
            else
              ⟨{0, 1, 2, 4, 9}, certificate_535⟩
          else
            if mask < 541 then
              ⟨{0, 1, 3, 4, 9}, certificate_539⟩
            else
              ⟨{0, 2, 3, 4, 9}, certificate_541⟩
        else
          if mask < 555 then
            if mask < 551 then
              ⟨{1, 2, 3, 4, 9}, certificate_542⟩
            else
              ⟨{0, 1, 2, 5, 9}, certificate_551⟩
          else
            if mask < 557 then
              ⟨{0, 1, 3, 5, 9}, certificate_555⟩
            else
              ⟨{0, 2, 3, 5, 9}, certificate_557⟩
      else
        if mask < 569 then
          if mask < 565 then
            if mask < 563 then
              ⟨{1, 2, 3, 5, 9}, certificate_558⟩
            else
              ⟨{0, 1, 4, 5, 9}, certificate_563⟩
          else
            if mask < 566 then
              ⟨{0, 2, 4, 5, 9}, certificate_565⟩
            else
              ⟨{1, 2, 4, 5, 9}, certificate_566⟩
        else
          if mask < 572 then
            if mask < 570 then
              ⟨{0, 3, 4, 5, 9}, certificate_569⟩
            else
              ⟨{1, 3, 4, 5, 9}, certificate_570⟩
          else
            if mask < 583 then
              ⟨{2, 3, 4, 5, 9}, certificate_572⟩
            else
              if mask < 587 then
                ⟨{0, 1, 2, 6, 9}, certificate_583⟩
              else
                ⟨{0, 1, 3, 6, 9}, certificate_587⟩
    else
      if mask < 613 then
        if mask < 598 then
          if mask < 595 then
            if mask < 590 then
              ⟨{0, 2, 3, 6, 9}, certificate_589⟩
            else
              ⟨{1, 2, 3, 6, 9}, certificate_590⟩
          else
            if mask < 597 then
              ⟨{0, 1, 4, 6, 9}, certificate_595⟩
            else
              ⟨{0, 2, 4, 6, 9}, certificate_597⟩
        else
          if mask < 602 then
            if mask < 601 then
              ⟨{1, 2, 4, 6, 9}, certificate_598⟩
            else
              ⟨{0, 3, 4, 6, 9}, certificate_601⟩
          else
            if mask < 604 then
              ⟨{1, 3, 4, 6, 9}, certificate_602⟩
            else
              if mask < 611 then
                ⟨{2, 3, 4, 6, 9}, certificate_604⟩
              else
                ⟨{0, 1, 5, 6, 9}, certificate_611⟩
      else
        if mask < 620 then
          if mask < 617 then
            if mask < 614 then
              ⟨{0, 2, 5, 6, 9}, certificate_613⟩
            else
              ⟨{1, 2, 5, 6, 9}, certificate_614⟩
          else
            if mask < 618 then
              ⟨{0, 3, 5, 6, 9}, certificate_617⟩
            else
              ⟨{1, 3, 5, 6, 9}, certificate_618⟩
        else
          if mask < 626 then
            if mask < 625 then
              ⟨{2, 3, 5, 6, 9}, certificate_620⟩
            else
              ⟨{0, 4, 5, 6, 9}, certificate_625⟩
          else
            if mask < 628 then
              ⟨{1, 4, 5, 6, 9}, certificate_626⟩
            else
              if mask < 632 then
                ⟨{2, 4, 5, 6, 9}, certificate_628⟩
              else
                ⟨{3, 4, 5, 6, 9}, certificate_632⟩
  else
    if mask < 690 then
      if mask < 666 then
        if mask < 659 then
          if mask < 653 then
            if mask < 651 then
              ⟨{0, 1, 2, 7, 9}, certificate_647⟩
            else
              ⟨{0, 1, 3, 7, 9}, certificate_651⟩
          else
            if mask < 654 then
              ⟨{0, 2, 3, 7, 9}, certificate_653⟩
            else
              ⟨{1, 2, 3, 7, 9}, certificate_654⟩
        else
          if mask < 662 then
            if mask < 661 then
              ⟨{0, 1, 4, 7, 9}, certificate_659⟩
            else
              ⟨{0, 2, 4, 7, 9}, certificate_661⟩
          else
            if mask < 665 then
              ⟨{1, 2, 4, 7, 9}, certificate_662⟩
            else
              ⟨{0, 3, 4, 7, 9}, certificate_665⟩
      else
        if mask < 678 then
          if mask < 675 then
            if mask < 668 then
              ⟨{1, 3, 4, 7, 9}, certificate_666⟩
            else
              ⟨{2, 3, 4, 7, 9}, certificate_668⟩
          else
            if mask < 677 then
              ⟨{0, 1, 5, 7, 9}, certificate_675⟩
            else
              ⟨{0, 2, 5, 7, 9}, certificate_677⟩
        else
          if mask < 682 then
            if mask < 681 then
              ⟨{1, 2, 5, 7, 9}, certificate_678⟩
            else
              ⟨{0, 3, 5, 7, 9}, certificate_681⟩
          else
            if mask < 684 then
              ⟨{1, 3, 5, 7, 9}, certificate_682⟩
            else
              if mask < 689 then
                ⟨{2, 3, 5, 7, 9}, certificate_684⟩
              else
                ⟨{0, 4, 5, 7, 9}, certificate_689⟩
    else
      if mask < 721 then
        if mask < 709 then
          if mask < 696 then
            if mask < 692 then
              ⟨{1, 4, 5, 7, 9}, certificate_690⟩
            else
              ⟨{2, 4, 5, 7, 9}, certificate_692⟩
          else
            if mask < 707 then
              ⟨{3, 4, 5, 7, 9}, certificate_696⟩
            else
              ⟨{0, 1, 6, 7, 9}, certificate_707⟩
        else
          if mask < 713 then
            if mask < 710 then
              ⟨{0, 2, 6, 7, 9}, certificate_709⟩
            else
              ⟨{1, 2, 6, 7, 9}, certificate_710⟩
          else
            if mask < 714 then
              ⟨{0, 3, 6, 7, 9}, certificate_713⟩
            else
              if mask < 716 then
                ⟨{1, 3, 6, 7, 9}, certificate_714⟩
              else
                ⟨{2, 3, 6, 7, 9}, certificate_716⟩
      else
        if mask < 737 then
          if mask < 724 then
            if mask < 722 then
              ⟨{0, 4, 6, 7, 9}, certificate_721⟩
            else
              ⟨{1, 4, 6, 7, 9}, certificate_722⟩
          else
            if mask < 728 then
              ⟨{2, 4, 6, 7, 9}, certificate_724⟩
            else
              ⟨{3, 4, 6, 7, 9}, certificate_728⟩
        else
          if mask < 740 then
            if mask < 738 then
              ⟨{0, 5, 6, 7, 9}, certificate_737⟩
            else
              ⟨{1, 5, 6, 7, 9}, certificate_738⟩
          else
            if mask < 744 then
              ⟨{2, 5, 6, 7, 9}, certificate_740⟩
            else
              if mask < 752 then
                ⟨{3, 5, 6, 7, 9}, certificate_744⟩
              else
                ⟨{4, 5, 6, 7, 9}, certificate_752⟩
end AMEProbe.BinaryDirect.Batch02
#print axioms AMEProbe.BinaryDirect.Batch02.lookup
