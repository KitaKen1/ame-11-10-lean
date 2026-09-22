import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch03
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_775 : Certificate {0, 1, 2, 8, 9} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 2, 8, 9} =
      !![1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 1, 1, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_779 : Certificate {0, 1, 3, 8, 9} := by
  refine ⟨!![0, 0, 1, 0, 0, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 3, 8, 9} =
      !![0, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_781 : Certificate {0, 2, 3, 8, 9} := by
  refine ⟨!![0, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 3, 8, 9} =
      !![0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_782 : Certificate {1, 2, 3, 8, 9} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 3, 8, 9} =
      !![0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_787 : Certificate {0, 1, 4, 8, 9} := by
  refine ⟨!![1, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 4, 8, 9} =
      !![0, 0, 0, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_789 : Certificate {0, 2, 4, 8, 9} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 4, 8, 9} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_790 : Certificate {1, 2, 4, 8, 9} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 4, 8, 9} =
      !![0, 0, 0, 0, 1;
      0, 0, 0, 1, 1;
      0, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_793 : Certificate {0, 3, 4, 8, 9} := by
  refine ⟨!![1, 1, 0, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 4, 8, 9} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_794 : Certificate {1, 3, 4, 8, 9} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 4, 8, 9} =
      !![0, 1, 0, 0, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_796 : Certificate {2, 3, 4, 8, 9} := by
  refine ⟨!![0, 1, 0, 0, 0, 0, 1;
      0, 0, 1, 0, 0, 1, 1;
      0, 0, 1, 0, 0, 0, 1;
      0, 1, 1, 0, 0, 0, 1;
      1, 0, 1, 0, 0, 1, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 4, 8, 9} =
      !![0, 1, 0, 0, 1;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_803 : Certificate {0, 1, 5, 8, 9} := by
  refine ⟨!![0, 0, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 5, 8, 9} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 1, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_805 : Certificate {0, 2, 5, 8, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 5, 8, 9} =
      !![0, 0, 0, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_806 : Certificate {1, 2, 5, 8, 9} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      0, 1, 1, 0, 1, 0, 1;
      1, 0, 1, 0, 1, 0, 1;
      1, 1, 1, 0, 1, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 5, 8, 9} =
      !![0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 0, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_809 : Certificate {0, 3, 5, 8, 9} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 5, 8, 9} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_810 : Certificate {1, 3, 5, 8, 9} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 5, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_812 : Certificate {2, 3, 5, 8, 9} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 5, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_817 : Certificate {0, 4, 5, 8, 9} := by
  refine ⟨!![1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 5, 8, 9} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_818 : Certificate {1, 4, 5, 8, 9} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 5, 8, 9} =
      !![0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_820 : Certificate {2, 4, 5, 8, 9} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 5, 8, 9} =
      !![0, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 0, 0;
      0, 1, 1, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_824 : Certificate {3, 4, 5, 8, 9} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 5, 8, 9} =
      !![1, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 0, 0;
      1, 1, 1, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_835 : Certificate {0, 1, 6, 8, 9} := by
  refine ⟨!![1, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 6, 8, 9} =
      !![0, 0, 0, 1, 1;
      1, 0, 1, 1, 1;
      0, 1, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_837 : Certificate {0, 2, 6, 8, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 6, 8, 9} =
      !![0, 0, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 0, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_838 : Certificate {1, 2, 6, 8, 9} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 6, 8, 9} =
      !![0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      0, 1, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 0, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_841 : Certificate {0, 3, 6, 8, 9} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 6, 8, 9} =
      !![0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_842 : Certificate {1, 3, 6, 8, 9} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 6, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_844 : Certificate {2, 3, 6, 8, 9} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 6, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 0, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 0, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_849 : Certificate {0, 4, 6, 8, 9} := by
  refine ⟨!![1, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 6, 8, 9} =
      !![0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_850 : Certificate {1, 4, 6, 8, 9} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 1;
      1, 1, 0, 0, 0, 0, 1;
      0, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 6, 8, 9} =
      !![0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_852 : Certificate {2, 4, 6, 8, 9} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 6, 8, 9} =
      !![0, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_856 : Certificate {3, 4, 6, 8, 9} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 6, 8, 9} =
      !![1, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      0, 1, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_865 : Certificate {0, 5, 6, 8, 9} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 6, 8, 9} =
      !![0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      1, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_866 : Certificate {1, 5, 6, 8, 9} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 6, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_868 : Certificate {2, 5, 6, 8, 9} := by
  refine ⟨!![0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 6, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 0, 1;
      1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_872 : Certificate {3, 5, 6, 8, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 6, 8, 9} =
      !![1, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 0, 0, 1;
      0, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      0, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_880 : Certificate {4, 5, 6, 8, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 6, 8, 9} =
      !![0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 1, 1;
      1, 0, 0, 0, 0;
      1, 1, 0, 0, 0;
      1, 1, 1, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_899 : Certificate {0, 1, 7, 8, 9} := by
  refine ⟨!![0, 0, 0, 1, 0, 0, 1;
      1, 0, 1, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 7, 8, 9} =
      !![0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 1, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_901 : Certificate {0, 2, 7, 8, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 7, 8, 9} =
      !![0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_902 : Certificate {1, 2, 7, 8, 9} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 7, 8, 9} =
      !![0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_905 : Certificate {0, 3, 7, 8, 9} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 7, 8, 9} =
      !![0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_906 : Certificate {1, 3, 7, 8, 9} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 7, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_908 : Certificate {2, 3, 7, 8, 9} := by
  refine ⟨!![1, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 7, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_913 : Certificate {0, 4, 7, 8, 9} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 7, 8, 9} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_914 : Certificate {1, 4, 7, 8, 9} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 1, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 7, 8, 9} =
      !![0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_916 : Certificate {2, 4, 7, 8, 9} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 7, 8, 9} =
      !![0, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_920 : Certificate {3, 4, 7, 8, 9} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 7, 8, 9} =
      !![1, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_929 : Certificate {0, 5, 7, 8, 9} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 7, 8, 9} =
      !![0, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_930 : Certificate {1, 5, 7, 8, 9} := by
  refine ⟨!![1, 1, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 7, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_932 : Certificate {2, 5, 7, 8, 9} := by
  refine ⟨!![1, 1, 0, 0, 1, 0, 1;
      1, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 7, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 1;
      0, 1, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_936 : Certificate {3, 5, 7, 8, 9} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 7, 8, 9} =
      !![1, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_944 : Certificate {4, 5, 7, 8, 9} := by
  refine ⟨!![0, 0, 1, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 1, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 7, 8, 9} =
      !![0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_961 : Certificate {0, 6, 7, 8, 9} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 6, 7, 8, 9} =
      !![0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_962 : Certificate {1, 6, 7, 8, 9} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 6, 7, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_964 : Certificate {2, 6, 7, 8, 9} := by
  refine ⟨!![1, 0, 1, 0, 1, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 6, 7, 8, 9} =
      !![0, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 0, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_968 : Certificate {3, 6, 7, 8, 9} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 1;
      0, 0, 1, 1, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 6, 7, 8, 9} =
      !![1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      0, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_976 : Certificate {4, 6, 7, 8, 9} := by
  refine ⟨!![0, 1, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 6, 7, 8, 9} =
      !![0, 1, 1, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_992 : Certificate {5, 6, 7, 8, 9} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      0, 0, 1, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 6, 7, 8, 9} =
      !![1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 1, 0, 0;
      1, 1, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 852 then
    if mask < 810 then
      if mask < 793 then
        if mask < 782 then
          if mask < 779 then
            ⟨{0, 1, 2, 8, 9}, certificate_775⟩
          else
            if mask < 781 then
              ⟨{0, 1, 3, 8, 9}, certificate_779⟩
            else
              ⟨{0, 2, 3, 8, 9}, certificate_781⟩
        else
          if mask < 789 then
            if mask < 787 then
              ⟨{1, 2, 3, 8, 9}, certificate_782⟩
            else
              ⟨{0, 1, 4, 8, 9}, certificate_787⟩
          else
            if mask < 790 then
              ⟨{0, 2, 4, 8, 9}, certificate_789⟩
            else
              ⟨{1, 2, 4, 8, 9}, certificate_790⟩
      else
        if mask < 803 then
          if mask < 794 then
            ⟨{0, 3, 4, 8, 9}, certificate_793⟩
          else
            if mask < 796 then
              ⟨{1, 3, 4, 8, 9}, certificate_794⟩
            else
              ⟨{2, 3, 4, 8, 9}, certificate_796⟩
        else
          if mask < 806 then
            if mask < 805 then
              ⟨{0, 1, 5, 8, 9}, certificate_803⟩
            else
              ⟨{0, 2, 5, 8, 9}, certificate_805⟩
          else
            if mask < 809 then
              ⟨{1, 2, 5, 8, 9}, certificate_806⟩
            else
              ⟨{0, 3, 5, 8, 9}, certificate_809⟩
    else
      if mask < 837 then
        if mask < 818 then
          if mask < 812 then
            ⟨{1, 3, 5, 8, 9}, certificate_810⟩
          else
            if mask < 817 then
              ⟨{2, 3, 5, 8, 9}, certificate_812⟩
            else
              ⟨{0, 4, 5, 8, 9}, certificate_817⟩
        else
          if mask < 824 then
            if mask < 820 then
              ⟨{1, 4, 5, 8, 9}, certificate_818⟩
            else
              ⟨{2, 4, 5, 8, 9}, certificate_820⟩
          else
            if mask < 835 then
              ⟨{3, 4, 5, 8, 9}, certificate_824⟩
            else
              ⟨{0, 1, 6, 8, 9}, certificate_835⟩
      else
        if mask < 842 then
          if mask < 838 then
            ⟨{0, 2, 6, 8, 9}, certificate_837⟩
          else
            if mask < 841 then
              ⟨{1, 2, 6, 8, 9}, certificate_838⟩
            else
              ⟨{0, 3, 6, 8, 9}, certificate_841⟩
        else
          if mask < 849 then
            if mask < 844 then
              ⟨{1, 3, 6, 8, 9}, certificate_842⟩
            else
              ⟨{2, 3, 6, 8, 9}, certificate_844⟩
          else
            if mask < 850 then
              ⟨{0, 4, 6, 8, 9}, certificate_849⟩
            else
              ⟨{1, 4, 6, 8, 9}, certificate_850⟩
  else
    if mask < 914 then
      if mask < 899 then
        if mask < 866 then
          if mask < 856 then
            ⟨{2, 4, 6, 8, 9}, certificate_852⟩
          else
            if mask < 865 then
              ⟨{3, 4, 6, 8, 9}, certificate_856⟩
            else
              ⟨{0, 5, 6, 8, 9}, certificate_865⟩
        else
          if mask < 872 then
            if mask < 868 then
              ⟨{1, 5, 6, 8, 9}, certificate_866⟩
            else
              ⟨{2, 5, 6, 8, 9}, certificate_868⟩
          else
            if mask < 880 then
              ⟨{3, 5, 6, 8, 9}, certificate_872⟩
            else
              ⟨{4, 5, 6, 8, 9}, certificate_880⟩
      else
        if mask < 905 then
          if mask < 901 then
            ⟨{0, 1, 7, 8, 9}, certificate_899⟩
          else
            if mask < 902 then
              ⟨{0, 2, 7, 8, 9}, certificate_901⟩
            else
              ⟨{1, 2, 7, 8, 9}, certificate_902⟩
        else
          if mask < 908 then
            if mask < 906 then
              ⟨{0, 3, 7, 8, 9}, certificate_905⟩
            else
              ⟨{1, 3, 7, 8, 9}, certificate_906⟩
          else
            if mask < 913 then
              ⟨{2, 3, 7, 8, 9}, certificate_908⟩
            else
              ⟨{0, 4, 7, 8, 9}, certificate_913⟩
    else
      if mask < 944 then
        if mask < 929 then
          if mask < 916 then
            ⟨{1, 4, 7, 8, 9}, certificate_914⟩
          else
            if mask < 920 then
              ⟨{2, 4, 7, 8, 9}, certificate_916⟩
            else
              ⟨{3, 4, 7, 8, 9}, certificate_920⟩
        else
          if mask < 932 then
            if mask < 930 then
              ⟨{0, 5, 7, 8, 9}, certificate_929⟩
            else
              ⟨{1, 5, 7, 8, 9}, certificate_930⟩
          else
            if mask < 936 then
              ⟨{2, 5, 7, 8, 9}, certificate_932⟩
            else
              ⟨{3, 5, 7, 8, 9}, certificate_936⟩
      else
        if mask < 964 then
          if mask < 961 then
            ⟨{4, 5, 7, 8, 9}, certificate_944⟩
          else
            if mask < 962 then
              ⟨{0, 6, 7, 8, 9}, certificate_961⟩
            else
              ⟨{1, 6, 7, 8, 9}, certificate_962⟩
        else
          if mask < 976 then
            if mask < 968 then
              ⟨{2, 6, 7, 8, 9}, certificate_964⟩
            else
              ⟨{3, 6, 7, 8, 9}, certificate_968⟩
          else
            if mask < 992 then
              ⟨{4, 6, 7, 8, 9}, certificate_976⟩
            else
              ⟨{5, 6, 7, 8, 9}, certificate_992⟩
end AMEProbe.BinaryDirect.Batch03
#print axioms AMEProbe.BinaryDirect.Batch03.lookup
