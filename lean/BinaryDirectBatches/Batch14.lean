import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch14
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_3587 : Certificate {0, 1, 9, 10, 11} := by
  refine ⟨!![1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 1, 1, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 1, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 9, 10, 11} =
      !![0, 0, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3589 : Certificate {0, 2, 9, 10, 11} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 9, 10, 11} =
      !![0, 0, 0, 1, 0;
      1, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3590 : Certificate {1, 2, 9, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 1;
      0, 1, 1, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 9, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3593 : Certificate {0, 3, 9, 10, 11} := by
  refine ⟨!![1, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 9, 10, 11} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 1, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3594 : Certificate {1, 3, 9, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1;
      1, 0, 1, 0, 0, 0, 1;
      1, 0, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 0, 1;
      1, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3596 : Certificate {2, 3, 9, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 1, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3601 : Certificate {0, 4, 9, 10, 11} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      0, 0, 1, 0, 1, 0, 1;
      0, 0, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 9, 10, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      0, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3602 : Certificate {1, 4, 9, 10, 11} := by
  refine ⟨!![0, 1, 0, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 9, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 0, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3604 : Certificate {2, 4, 9, 10, 11} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 9, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3608 : Certificate {3, 4, 9, 10, 11} := by
  refine ⟨!![0, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 9, 10, 11} =
      !![1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3617 : Certificate {0, 5, 9, 10, 11} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 9, 10, 11} =
      !![0, 0, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3618 : Certificate {1, 5, 9, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      1, 0, 1, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3620 : Certificate {2, 5, 9, 10, 11} := by
  refine ⟨!![0, 1, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3624 : Certificate {3, 5, 9, 10, 11} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 9, 10, 11} =
      !![1, 1, 1, 0, 0;
      0, 0, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3632 : Certificate {4, 5, 9, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      1, 0, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3649 : Certificate {0, 6, 9, 10, 11} := by
  refine ⟨!![0, 1, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 6, 9, 10, 11} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3650 : Certificate {1, 6, 9, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 6, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3652 : Certificate {2, 6, 9, 10, 11} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 6, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3656 : Certificate {3, 6, 9, 10, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 6, 9, 10, 11} =
      !![1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3664 : Certificate {4, 6, 9, 10, 11} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 6, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      0, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3680 : Certificate {5, 6, 9, 10, 11} := by
  refine ⟨!![1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 6, 9, 10, 11} =
      !![1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3713 : Certificate {0, 7, 9, 10, 11} := by
  refine ⟨!![1, 0, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 7, 9, 10, 11} =
      !![0, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3714 : Certificate {1, 7, 9, 10, 11} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 7, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      1, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3716 : Certificate {2, 7, 9, 10, 11} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 1;
      1, 1, 0, 0, 1, 0, 1;
      0, 0, 0, 0, 1, 0, 1;
      1, 0, 0, 1, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 7, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3720 : Certificate {3, 7, 9, 10, 11} := by
  refine ⟨!![1, 0, 0, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 7, 9, 10, 11} =
      !![1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3728 : Certificate {4, 7, 9, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 7, 9, 10, 11} =
      !![0, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3744 : Certificate {5, 7, 9, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 7, 9, 10, 11} =
      !![1, 1, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3776 : Certificate {6, 7, 9, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {6, 7, 9, 10, 11} =
      !![1, 1, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 3632 then
    if mask < 3602 then
      if mask < 3593 then
        if mask < 3589 then
          ⟨{0, 1, 9, 10, 11}, certificate_3587⟩
        else
          if mask < 3590 then
            ⟨{0, 2, 9, 10, 11}, certificate_3589⟩
          else
            ⟨{1, 2, 9, 10, 11}, certificate_3590⟩
      else
        if mask < 3596 then
          if mask < 3594 then
            ⟨{0, 3, 9, 10, 11}, certificate_3593⟩
          else
            ⟨{1, 3, 9, 10, 11}, certificate_3594⟩
        else
          if mask < 3601 then
            ⟨{2, 3, 9, 10, 11}, certificate_3596⟩
          else
            ⟨{0, 4, 9, 10, 11}, certificate_3601⟩
    else
      if mask < 3617 then
        if mask < 3604 then
          ⟨{1, 4, 9, 10, 11}, certificate_3602⟩
        else
          if mask < 3608 then
            ⟨{2, 4, 9, 10, 11}, certificate_3604⟩
          else
            ⟨{3, 4, 9, 10, 11}, certificate_3608⟩
      else
        if mask < 3620 then
          if mask < 3618 then
            ⟨{0, 5, 9, 10, 11}, certificate_3617⟩
          else
            ⟨{1, 5, 9, 10, 11}, certificate_3618⟩
        else
          if mask < 3624 then
            ⟨{2, 5, 9, 10, 11}, certificate_3620⟩
          else
            ⟨{3, 5, 9, 10, 11}, certificate_3624⟩
  else
    if mask < 3713 then
      if mask < 3652 then
        if mask < 3649 then
          ⟨{4, 5, 9, 10, 11}, certificate_3632⟩
        else
          if mask < 3650 then
            ⟨{0, 6, 9, 10, 11}, certificate_3649⟩
          else
            ⟨{1, 6, 9, 10, 11}, certificate_3650⟩
      else
        if mask < 3664 then
          if mask < 3656 then
            ⟨{2, 6, 9, 10, 11}, certificate_3652⟩
          else
            ⟨{3, 6, 9, 10, 11}, certificate_3656⟩
        else
          if mask < 3680 then
            ⟨{4, 6, 9, 10, 11}, certificate_3664⟩
          else
            ⟨{5, 6, 9, 10, 11}, certificate_3680⟩
    else
      if mask < 3720 then
        if mask < 3714 then
          ⟨{0, 7, 9, 10, 11}, certificate_3713⟩
        else
          if mask < 3716 then
            ⟨{1, 7, 9, 10, 11}, certificate_3714⟩
          else
            ⟨{2, 7, 9, 10, 11}, certificate_3716⟩
      else
        if mask < 3744 then
          if mask < 3728 then
            ⟨{3, 7, 9, 10, 11}, certificate_3720⟩
          else
            ⟨{4, 7, 9, 10, 11}, certificate_3728⟩
        else
          if mask < 3776 then
            ⟨{5, 7, 9, 10, 11}, certificate_3744⟩
          else
            ⟨{6, 7, 9, 10, 11}, certificate_3776⟩
end AMEProbe.BinaryDirect.Batch14
#print axioms AMEProbe.BinaryDirect.Batch14.lookup
