import BinaryDirectBase

/-! Complete coverage of all binary five-subsets by sixteen mask batches. -/
open scoped BigOperators
namespace AMEProbe.BinaryDirect

def mask (A : Finset (Fin 12)) : ℕ := ∑ i ∈ A, 2 ^ i.val

def allCuts : Finset (Finset (Fin 12)) := Finset.univ.powersetCard 5

def batch (b : ℕ) : Finset (Finset (Fin 12)) :=
  allCuts.filter (fun A => mask A / 256 = b)

lemma mask_lt (A : Finset (Fin 12)) : mask A < 4096 := by
  have h : mask A ≤ ∑ i : Fin 12, 2 ^ i.val :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ A)
  have hu : (∑ i : Fin 12, 2 ^ i.val) = 4095 := by decide +kernel
  rw [hu] at h
  omega

lemma batch_coverage (A : Finset (Fin 12)) (hA : A.card = 5) :
    ∃ b : Fin 16, A ∈ batch b.val := by
  have hm := mask_lt A
  refine ⟨⟨mask A / 256, by omega⟩, ?_⟩
  simp [batch, allCuts, hA]

end AMEProbe.BinaryDirect
#print axioms AMEProbe.BinaryDirect.batch_coverage
