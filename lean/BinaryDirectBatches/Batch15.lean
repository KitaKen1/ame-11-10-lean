import BinaryDirectBase

/-! Explicit binary left-inverse witnesses. Graph and products are kernel checked. -/
namespace AMEProbe.BinaryDirect.Batch15
open GraphState BinaryGraph AMEProbe.BinaryDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem certificate_3841 : Certificate {0, 8, 9, 10, 11} := by
  refine ⟨!![0, 0, 1, 0, 1, 1, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 1, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {0, 8, 9, 10, 11} =
      !![0, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3842 : Certificate {1, 8, 9, 10, 11} := by
  refine ⟨!![1, 1, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0;
      1, 0, 1, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {1, 8, 9, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      1, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3844 : Certificate {2, 8, 9, 10, 11} := by
  refine ⟨!![1, 1, 0, 0, 1, 1, 0;
      0, 1, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0;
      1, 0, 0, 0, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {2, 8, 9, 10, 11} =
      !![0, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      1, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3848 : Certificate {3, 8, 9, 10, 11} := by
  refine ⟨!![1, 0, 1, 0, 1, 0, 1;
      0, 1, 0, 0, 0, 0, 1;
      0, 0, 1, 0, 1, 0, 1;
      0, 0, 0, 0, 0, 0, 1;
      0, 1, 0, 0, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {3, 8, 9, 10, 11} =
      !![1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      1, 0, 1, 0, 1;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3856 : Certificate {4, 8, 9, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 1, 0, 0;
      1, 0, 0, 1, 1, 0, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {4, 8, 9, 10, 11} =
      !![0, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1;
      1, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3872 : Certificate {5, 8, 9, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0;
      0, 1, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {5, 8, 9, 10, 11} =
      !![1, 0, 1, 0, 0;
      0, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 0, 1, 0, 1;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3904 : Certificate {6, 8, 9, 10, 11} := by
  refine ⟨!![1, 1, 0, 1, 0, 0, 0;
      1, 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 1, 0;
      1, 0, 0, 1, 0, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {6, 8, 9, 10, 11} =
      !![1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      0, 1, 1, 0, 1;
      1, 1, 1, 1, 0;
      0, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 0, 1, 0] := by decide +kernel
  rw [hc]
  decide +kernel

theorem certificate_3968 : Certificate {7, 8, 9, 10, 11} := by
  refine ⟨!![0, 1, 1, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 1, 0;
      1, 1, 1, 0, 1, 0, 0;
      1, 0, 1, 0, 0, 1, 0;
      0, 0, 1, 0, 1, 1, 0], ?_⟩
  have hc : executableCutMatrix (k := 5) (t := 7) graph {7, 8, 9, 10, 11} =
      !![1, 0, 1, 0, 0;
      1, 1, 0, 1, 0;
      1, 1, 1, 0, 1;
      0, 1, 1, 1, 0;
      1, 0, 1, 1, 1;
      0, 1, 0, 1, 1;
      0, 0, 1, 0, 1] := by decide +kernel
  rw [hc]
  decide +kernel

def lookup (mask : ℕ) : {A : Finset (Fin 12) // Certificate A} :=
  if mask < 3856 then
    if mask < 3844 then
      if mask < 3842 then
        ⟨{0, 8, 9, 10, 11}, certificate_3841⟩
      else
        ⟨{1, 8, 9, 10, 11}, certificate_3842⟩
    else
      if mask < 3848 then
        ⟨{2, 8, 9, 10, 11}, certificate_3844⟩
      else
        ⟨{3, 8, 9, 10, 11}, certificate_3848⟩
  else
    if mask < 3904 then
      if mask < 3872 then
        ⟨{4, 8, 9, 10, 11}, certificate_3856⟩
      else
        ⟨{5, 8, 9, 10, 11}, certificate_3872⟩
    else
      if mask < 3968 then
        ⟨{6, 8, 9, 10, 11}, certificate_3904⟩
      else
        ⟨{7, 8, 9, 10, 11}, certificate_3968⟩
end AMEProbe.BinaryDirect.Batch15
#print axioms AMEProbe.BinaryDirect.Batch15.lookup
