import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch07
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_1795 : Certificate {0, 1, 8, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 1, 0, 0, 0, 1, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 1, 8, 9, 10} =
      !![0, 0, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1797 : Certificate {0, 2, 8, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 1, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 2, 8, 9, 10} =
      !![0, 0, 1, 0, 1;
      1, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 1, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1798 : Certificate {1, 2, 8, 9, 10} := by
  refine ⟨!![1, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 2, 8, 9, 10} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 1, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1801 : Certificate {0, 3, 8, 9, 10} := by
  refine ⟨!![1, 0, 0, 1, 0, 0, 0;
      1, 1, 0, 0, 1, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 3, 8, 9, 10} =
      !![0, 0, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1802 : Certificate {1, 3, 8, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 3, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 0;
      1, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1804 : Certificate {2, 3, 8, 9, 10} := by
  refine ⟨!![0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 1, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 3, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 1, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1809 : Certificate {0, 4, 8, 9, 10} := by
  refine ⟨!![0, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 4, 8, 9, 10} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      1, 0, 1, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1810 : Certificate {1, 4, 8, 9, 10} := by
  refine ⟨!![1, 0, 0, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 1, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 4, 8, 9, 10} =
      !![0, 0, 0, 1, 0;
      0, 0, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1812 : Certificate {2, 4, 8, 9, 10} := by
  refine ⟨!![1, 0, 1, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 4, 8, 9, 10} =
      !![0, 0, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 1, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1816 : Certificate {3, 4, 8, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 1, 0;
      0, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 4, 8, 9, 10} =
      !![1, 0, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 1, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1825 : Certificate {0, 5, 8, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 5, 8, 9, 10} =
      !![0, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1826 : Certificate {1, 5, 8, 9, 10} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 1, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      0, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 5, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1828 : Certificate {2, 5, 8, 9, 10} := by
  refine ⟨!![0, 1, 1, 1, 0, 1, 0;
      1, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 5, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1832 : Certificate {3, 5, 8, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 5, 8, 9, 10} =
      !![1, 1, 0, 1, 0;
      0, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 0, 1, 1;
      1, 0, 0, 1, 0;
      0, 0, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1840 : Certificate {4, 5, 8, 9, 10} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      1, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      1, 0, 1, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 5, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      1, 0, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1857 : Certificate {0, 6, 8, 9, 10} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 1, 1, 1, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 6, 8, 9, 10} =
      !![0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      1, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1858 : Certificate {1, 6, 8, 9, 10} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 1, 1, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 6, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      0, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      1, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1860 : Certificate {2, 6, 8, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 6, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1864 : Certificate {3, 6, 8, 9, 10} := by
  refine ⟨!![1, 1, 1, 0, 0, 1, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 6, 8, 9, 10} =
      !![1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 0, 0, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 0, 1;
      0, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1872 : Certificate {4, 6, 8, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      1, 1, 1, 1, 0, 0, 1;
      0, 1, 0, 0, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 6, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1888 : Certificate {5, 6, 8, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 1;
      1, 1, 0, 1, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 6, 8, 9, 10} =
      !![1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 0, 1, 1, 0;
      0, 1, 1, 1, 1;
      0, 0, 0, 1, 1;
      0, 0, 0, 0, 1;
      1, 1, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1921 : Certificate {0, 7, 8, 9, 10} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 7, 8, 9, 10} =
      !![0, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1922 : Certificate {1, 7, 8, 9, 10} := by
  refine ⟨!![0, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 7, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1924 : Certificate {2, 7, 8, 9, 10} := by
  refine ⟨!![1, 1, 0, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 1, 0;
      1, 0, 0, 1, 0, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 7, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1928 : Certificate {3, 7, 8, 9, 10} := by
  refine ⟨!![1, 0, 1, 0, 0, 0, 1;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 1, 0, 0, 1;
      0, 0, 1, 1, 0, 0, 1], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 7, 8, 9, 10} =
      !![1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0;
      0, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1936 : Certificate {4, 7, 8, 9, 10} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 7, 8, 9, 10} =
      !![0, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1952 : Certificate {5, 7, 8, 9, 10} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 7, 8, 9, 10} =
      !![1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 0;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_1984 : Certificate {6, 7, 8, 9, 10} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 1, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      1, 1, 1, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {6, 7, 8, 9, 10} =
      !![1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 1, 0, 0] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 1840 then
    if mask < 1810 then
      if mask < 1801 then
        if mask < 1797 then
          ⟨{0, 1, 8, 9, 10}, certificate_1795⟩
        else
          if mask < 1798 then
            ⟨{0, 2, 8, 9, 10}, certificate_1797⟩
          else
            ⟨{1, 2, 8, 9, 10}, certificate_1798⟩
      else
        if mask < 1804 then
          if mask < 1802 then
            ⟨{0, 3, 8, 9, 10}, certificate_1801⟩
          else
            ⟨{1, 3, 8, 9, 10}, certificate_1802⟩
        else
          if mask < 1809 then
            ⟨{2, 3, 8, 9, 10}, certificate_1804⟩
          else
            ⟨{0, 4, 8, 9, 10}, certificate_1809⟩
    else
      if mask < 1825 then
        if mask < 1812 then
          ⟨{1, 4, 8, 9, 10}, certificate_1810⟩
        else
          if mask < 1816 then
            ⟨{2, 4, 8, 9, 10}, certificate_1812⟩
          else
            ⟨{3, 4, 8, 9, 10}, certificate_1816⟩
      else
        if mask < 1828 then
          if mask < 1826 then
            ⟨{0, 5, 8, 9, 10}, certificate_1825⟩
          else
            ⟨{1, 5, 8, 9, 10}, certificate_1826⟩
        else
          if mask < 1832 then
            ⟨{2, 5, 8, 9, 10}, certificate_1828⟩
          else
            ⟨{3, 5, 8, 9, 10}, certificate_1832⟩
  else
    if mask < 1921 then
      if mask < 1860 then
        if mask < 1857 then
          ⟨{4, 5, 8, 9, 10}, certificate_1840⟩
        else
          if mask < 1858 then
            ⟨{0, 6, 8, 9, 10}, certificate_1857⟩
          else
            ⟨{1, 6, 8, 9, 10}, certificate_1858⟩
      else
        if mask < 1872 then
          if mask < 1864 then
            ⟨{2, 6, 8, 9, 10}, certificate_1860⟩
          else
            ⟨{3, 6, 8, 9, 10}, certificate_1864⟩
        else
          if mask < 1888 then
            ⟨{4, 6, 8, 9, 10}, certificate_1872⟩
          else
            ⟨{5, 6, 8, 9, 10}, certificate_1888⟩
    else
      if mask < 1928 then
        if mask < 1922 then
          ⟨{0, 7, 8, 9, 10}, certificate_1921⟩
        else
          if mask < 1924 then
            ⟨{1, 7, 8, 9, 10}, certificate_1922⟩
          else
            ⟨{2, 7, 8, 9, 10}, certificate_1924⟩
      else
        if mask < 1952 then
          if mask < 1936 then
            ⟨{3, 7, 8, 9, 10}, certificate_1928⟩
          else
            ⟨{4, 7, 8, 9, 10}, certificate_1936⟩
        else
          if mask < 1984 then
            ⟨{5, 7, 8, 9, 10}, certificate_1952⟩
          else
            ⟨{6, 7, 8, 9, 10}, certificate_1984⟩
end AMEProbe.BinaryDirect.Batch07
#print axioms AMEProbe.BinaryDirect.Batch07.lookup
