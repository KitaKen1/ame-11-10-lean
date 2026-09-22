import BinaryCoverageBatches.Batch00
import BinaryCoverageBatches.Batch01
import BinaryCoverageBatches.Batch02
import BinaryCoverageBatches.Batch03
import BinaryCoverageBatches.Batch04
import BinaryCoverageBatches.Batch05
import BinaryCoverageBatches.Batch06
import BinaryCoverageBatches.Batch07
import BinaryCoverageBatches.Batch08
import BinaryCoverageBatches.Batch09
import BinaryCoverageBatches.Batch10
import BinaryCoverageBatches.Batch11
import BinaryCoverageBatches.Batch12
import BinaryCoverageBatches.Batch13
import BinaryCoverageBatches.Batch14
import BinaryCoverageBatches.Batch15

/-! Complete binary cut coverage assembled from numeric mask checks. -/
namespace AMEProbe.BinaryDirect
open AMEProbe.MaskEncoding

private theorem certificate_of_lookup (A : Finset (Fin 12)) (hA : A.card = 5)
    (b : ℕ) (lookup : ℕ → {A : Finset (Fin 12) // Certificate A})
    (hdiv : mask A / 256 = b)
    (hmask : ∀ r : Fin 256, (256 * b + r.val).bitIndices.length = 5 →
      mask (lookup (256 * b + r.val)).val = 256 * b + r.val) : Certificate A := by
  let r : Fin 256 := ⟨mask A % 256, Nat.mod_lt _ (by omega)⟩
  have hdecomp : 256 * b + r.val = mask A := by
    dsimp [r]
    have hm := Nat.mod_add_div (mask A) 256
    rw [hdiv] at hm
    omega
  have hbits : (mask A).bitIndices.length = 5 := by
    change (finMask A).bitIndices.length = 5
    simpa only [hA] using bitIndices_length_finMask A
  have hm := hmask r (by simpa only [hdecomp] using hbits)
  have hset : (lookup (mask A)).val = A := by
    apply finMask_injective
    change mask (lookup (mask A)).val = mask A
    simpa only [hdecomp] using hm
  have hcert := (lookup (mask A)).property
  rw [hset] at hcert
  exact hcert

theorem all_certified (A : Finset (Fin 12)) (hA : A.card = 5) : Certificate A := by
  obtain ⟨b, hb⟩ := batch_coverage A hA
  fin_cases b
  · apply certificate_of_lookup A hA 0 Batch00.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch00Coverage.mask_correct
  · apply certificate_of_lookup A hA 1 Batch01.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch01Coverage.mask_correct
  · apply certificate_of_lookup A hA 2 Batch02.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch02Coverage.mask_correct
  · apply certificate_of_lookup A hA 3 Batch03.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch03Coverage.mask_correct
  · apply certificate_of_lookup A hA 4 Batch04.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch04Coverage.mask_correct
  · apply certificate_of_lookup A hA 5 Batch05.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch05Coverage.mask_correct
  · apply certificate_of_lookup A hA 6 Batch06.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch06Coverage.mask_correct
  · apply certificate_of_lookup A hA 7 Batch07.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch07Coverage.mask_correct
  · apply certificate_of_lookup A hA 8 Batch08.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch08Coverage.mask_correct
  · apply certificate_of_lookup A hA 9 Batch09.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch09Coverage.mask_correct
  · apply certificate_of_lookup A hA 10 Batch10.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch10Coverage.mask_correct
  · apply certificate_of_lookup A hA 11 Batch11.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch11Coverage.mask_correct
  · apply certificate_of_lookup A hA 12 Batch12.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch12Coverage.mask_correct
  · apply certificate_of_lookup A hA 13 Batch13.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch13Coverage.mask_correct
  · apply certificate_of_lookup A hA 14 Batch14.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch14Coverage.mask_correct
  · apply certificate_of_lookup A hA 15 Batch15.lookup
    · have hb' := hb
      simp only [batch, Finset.mem_filter] at hb'
      exact hb'.2
    · exact Batch15Coverage.mask_correct

end AMEProbe.BinaryDirect
#print axioms AMEProbe.BinaryDirect.all_certified
