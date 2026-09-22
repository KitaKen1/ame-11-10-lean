import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch10
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_2567 : Certificate {0, 1, 2, 9, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 9, 11} =
      !![1, 0, 0, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2571 : Certificate {0, 1, 3, 9, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 9, 11} =
      !![0, 0, 0, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2573 : Certificate {0, 2, 3, 9, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 1;
      0, 1, 0, 1, 1, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 9, 11} =
      !![0, 0, 0, 0, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2574 : Certificate {1, 2, 3, 9, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 9, 11} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2579 : Certificate {0, 1, 4, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 1;
      1, 0, 0, 1, 1, 0, 1;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 1;
      1, 1, 0, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 9, 11} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2581 : Certificate {0, 2, 4, 9, 11} := by
  refine ⟨!![0, 0, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 9, 11} =
      !![0, 0, 1, 0, 0;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2582 : Certificate {1, 2, 4, 9, 11} := by
  refine ⟨!![0, 0, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 9, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2585 : Certificate {0, 3, 4, 9, 11} := by
  refine ⟨!![1, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 9, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2586 : Certificate {1, 3, 4, 9, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 9, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2588 : Certificate {2, 3, 4, 9, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 9, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2595 : Certificate {0, 1, 5, 9, 11} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 9, 11} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 1, 1;
      1, 1, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2597 : Certificate {0, 2, 5, 9, 11} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 1, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 9, 11} =
      !![0, 0, 0, 0, 0;
      1, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2598 : Certificate {1, 2, 5, 9, 11} := by
  refine ⟨!![1, 0, 1, 0, 1, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 9, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2601 : Certificate {0, 3, 5, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 1, 0;
      0, 1, 0, 1, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 9, 11} =
      !![0, 0, 0, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2602 : Certificate {1, 3, 5, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2604 : Certificate {2, 3, 5, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      1, 0, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 0, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2609 : Certificate {0, 4, 5, 9, 11} := by
  refine ⟨!![1, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 9, 11} =
      !![0, 1, 0, 0, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2610 : Certificate {1, 4, 5, 9, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 9, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2612 : Certificate {2, 4, 5, 9, 11} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 9, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2616 : Certificate {3, 4, 5, 9, 11} := by
  refine ⟨!![1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 9, 11} =
      !![1, 0, 1, 1, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 0;
      1, 0, 1, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2627 : Certificate {0, 1, 6, 9, 11} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 6, 9, 11} =
      !![0, 0, 0, 1, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2629 : Certificate {0, 2, 6, 9, 11} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 6, 9, 11} =
      !![0, 0, 1, 0, 0;
      1, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 1;
      0, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2630 : Certificate {1, 2, 6, 9, 11} := by
  refine ⟨!![0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 6, 9, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2633 : Certificate {0, 3, 6, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 6, 9, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2634 : Certificate {1, 3, 6, 9, 11} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 6, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2636 : Certificate {2, 3, 6, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 6, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2641 : Certificate {0, 4, 6, 9, 11} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 6, 9, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 0, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2642 : Certificate {1, 4, 6, 9, 11} := by
  refine ⟨!![0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 1, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 6, 9, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2644 : Certificate {2, 4, 6, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      0, 0, 0, 1, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 6, 9, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2648 : Certificate {3, 4, 6, 9, 11} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 6, 9, 11} =
      !![1, 0, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2657 : Certificate {0, 5, 6, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 6, 9, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2658 : Certificate {1, 5, 6, 9, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 6, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2660 : Certificate {2, 5, 6, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 6, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 0;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      0, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2664 : Certificate {3, 5, 6, 9, 11} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 1;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 6, 9, 11} =
      !![1, 1, 1, 1, 0;
      0, 0, 1, 0, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2672 : Certificate {4, 5, 6, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 6, 9, 11} =
      !![0, 1, 1, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2691 : Certificate {0, 1, 7, 9, 11} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 7, 9, 11} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      0, 1, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 1;
      0, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2693 : Certificate {0, 2, 7, 9, 11} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 7, 9, 11} =
      !![0, 0, 1, 0, 0;
      1, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2694 : Certificate {1, 2, 7, 9, 11} := by
  refine ⟨!![0, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 7, 9, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2697 : Certificate {0, 3, 7, 9, 11} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 1;
      0, 1, 0, 1, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 7, 9, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 1, 1;
      0, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2698 : Certificate {1, 3, 7, 9, 11} := by
  refine ⟨!![0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 7, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2700 : Certificate {2, 3, 7, 9, 11} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 7, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2705 : Certificate {0, 4, 7, 9, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 7, 9, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2706 : Certificate {1, 4, 7, 9, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 1;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 7, 9, 11} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2708 : Certificate {2, 4, 7, 9, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 7, 9, 11} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2712 : Certificate {3, 4, 7, 9, 11} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 7, 9, 11} =
      !![1, 0, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2721 : Certificate {0, 5, 7, 9, 11} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 7, 9, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      1, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2722 : Certificate {1, 5, 7, 9, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 7, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2724 : Certificate {2, 5, 7, 9, 11} := by
  refine ⟨!![1, 0, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 7, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2728 : Certificate {3, 5, 7, 9, 11} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 7, 9, 11} =
      !![1, 1, 1, 1, 0;
      0, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2736 : Certificate {4, 5, 7, 9, 11} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 7, 9, 11} =
      !![0, 1, 1, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2753 : Certificate {0, 6, 7, 9, 11} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 0, 1, 1;
      0, 0, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 6, 7, 9, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      1, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 0, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2754 : Certificate {1, 6, 7, 9, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 6, 7, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2756 : Certificate {2, 6, 7, 9, 11} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 6, 7, 9, 11} =
      !![0, 1, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2760 : Certificate {3, 6, 7, 9, 11} := by
  refine ⟨!![0, 0, 0, 0, 1, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 6, 7, 9, 11} =
      !![1, 1, 1, 1, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2768 : Certificate {4, 6, 7, 9, 11} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 6, 7, 9, 11} =
      !![0, 1, 1, 1, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_2784 : Certificate {5, 6, 7, 9, 11} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 6, 7, 9, 11} =
      !![1, 1, 1, 1, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 2644 then
    if mask < 2602 then
      if mask < 2585 then
        if mask < 2574 then
          if mask < 2571 then
            ⟨{0, 1, 2, 9, 11}, certificate_2567⟩
          else
            if mask < 2573 then
              ⟨{0, 1, 3, 9, 11}, certificate_2571⟩
            else
              ⟨{0, 2, 3, 9, 11}, certificate_2573⟩
        else
          if mask < 2581 then
            if mask < 2579 then
              ⟨{1, 2, 3, 9, 11}, certificate_2574⟩
            else
              ⟨{0, 1, 4, 9, 11}, certificate_2579⟩
          else
            if mask < 2582 then
              ⟨{0, 2, 4, 9, 11}, certificate_2581⟩
            else
              ⟨{1, 2, 4, 9, 11}, certificate_2582⟩
      else
        if mask < 2595 then
          if mask < 2586 then
            ⟨{0, 3, 4, 9, 11}, certificate_2585⟩
          else
            if mask < 2588 then
              ⟨{1, 3, 4, 9, 11}, certificate_2586⟩
            else
              ⟨{2, 3, 4, 9, 11}, certificate_2588⟩
        else
          if mask < 2598 then
            if mask < 2597 then
              ⟨{0, 1, 5, 9, 11}, certificate_2595⟩
            else
              ⟨{0, 2, 5, 9, 11}, certificate_2597⟩
          else
            if mask < 2601 then
              ⟨{1, 2, 5, 9, 11}, certificate_2598⟩
            else
              ⟨{0, 3, 5, 9, 11}, certificate_2601⟩
    else
      if mask < 2629 then
        if mask < 2610 then
          if mask < 2604 then
            ⟨{1, 3, 5, 9, 11}, certificate_2602⟩
          else
            if mask < 2609 then
              ⟨{2, 3, 5, 9, 11}, certificate_2604⟩
            else
              ⟨{0, 4, 5, 9, 11}, certificate_2609⟩
        else
          if mask < 2616 then
            if mask < 2612 then
              ⟨{1, 4, 5, 9, 11}, certificate_2610⟩
            else
              ⟨{2, 4, 5, 9, 11}, certificate_2612⟩
          else
            if mask < 2627 then
              ⟨{3, 4, 5, 9, 11}, certificate_2616⟩
            else
              ⟨{0, 1, 6, 9, 11}, certificate_2627⟩
      else
        if mask < 2634 then
          if mask < 2630 then
            ⟨{0, 2, 6, 9, 11}, certificate_2629⟩
          else
            if mask < 2633 then
              ⟨{1, 2, 6, 9, 11}, certificate_2630⟩
            else
              ⟨{0, 3, 6, 9, 11}, certificate_2633⟩
        else
          if mask < 2641 then
            if mask < 2636 then
              ⟨{1, 3, 6, 9, 11}, certificate_2634⟩
            else
              ⟨{2, 3, 6, 9, 11}, certificate_2636⟩
          else
            if mask < 2642 then
              ⟨{0, 4, 6, 9, 11}, certificate_2641⟩
            else
              ⟨{1, 4, 6, 9, 11}, certificate_2642⟩
  else
    if mask < 2706 then
      if mask < 2691 then
        if mask < 2658 then
          if mask < 2648 then
            ⟨{2, 4, 6, 9, 11}, certificate_2644⟩
          else
            if mask < 2657 then
              ⟨{3, 4, 6, 9, 11}, certificate_2648⟩
            else
              ⟨{0, 5, 6, 9, 11}, certificate_2657⟩
        else
          if mask < 2664 then
            if mask < 2660 then
              ⟨{1, 5, 6, 9, 11}, certificate_2658⟩
            else
              ⟨{2, 5, 6, 9, 11}, certificate_2660⟩
          else
            if mask < 2672 then
              ⟨{3, 5, 6, 9, 11}, certificate_2664⟩
            else
              ⟨{4, 5, 6, 9, 11}, certificate_2672⟩
      else
        if mask < 2697 then
          if mask < 2693 then
            ⟨{0, 1, 7, 9, 11}, certificate_2691⟩
          else
            if mask < 2694 then
              ⟨{0, 2, 7, 9, 11}, certificate_2693⟩
            else
              ⟨{1, 2, 7, 9, 11}, certificate_2694⟩
        else
          if mask < 2700 then
            if mask < 2698 then
              ⟨{0, 3, 7, 9, 11}, certificate_2697⟩
            else
              ⟨{1, 3, 7, 9, 11}, certificate_2698⟩
          else
            if mask < 2705 then
              ⟨{2, 3, 7, 9, 11}, certificate_2700⟩
            else
              ⟨{0, 4, 7, 9, 11}, certificate_2705⟩
    else
      if mask < 2736 then
        if mask < 2721 then
          if mask < 2708 then
            ⟨{1, 4, 7, 9, 11}, certificate_2706⟩
          else
            if mask < 2712 then
              ⟨{2, 4, 7, 9, 11}, certificate_2708⟩
            else
              ⟨{3, 4, 7, 9, 11}, certificate_2712⟩
        else
          if mask < 2724 then
            if mask < 2722 then
              ⟨{0, 5, 7, 9, 11}, certificate_2721⟩
            else
              ⟨{1, 5, 7, 9, 11}, certificate_2722⟩
          else
            if mask < 2728 then
              ⟨{2, 5, 7, 9, 11}, certificate_2724⟩
            else
              ⟨{3, 5, 7, 9, 11}, certificate_2728⟩
      else
        if mask < 2756 then
          if mask < 2753 then
            ⟨{4, 5, 7, 9, 11}, certificate_2736⟩
          else
            if mask < 2754 then
              ⟨{0, 6, 7, 9, 11}, certificate_2753⟩
            else
              ⟨{1, 6, 7, 9, 11}, certificate_2754⟩
        else
          if mask < 2768 then
            if mask < 2760 then
              ⟨{2, 6, 7, 9, 11}, certificate_2756⟩
            else
              ⟨{3, 6, 7, 9, 11}, certificate_2760⟩
          else
            if mask < 2784 then
              ⟨{4, 6, 7, 9, 11}, certificate_2768⟩
            else
              ⟨{5, 6, 7, 9, 11}, certificate_2784⟩
end AMEProbe.BinaryDirect.Batch10
#print axioms AMEProbe.BinaryDirect.Batch10.lookup
