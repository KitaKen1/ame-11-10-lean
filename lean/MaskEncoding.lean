import Mathlib.Combinatorics.Colex

/-! Injective binary-mask encoding for finite subsets of `Fin n`. -/
open scoped BigOperators
namespace AMEProbe.MaskEncoding

def finMask {n : ℕ} (A : Finset (Fin n)) : ℕ :=
  ∑ i ∈ A, 2 ^ i.val

def natImage {n : ℕ} (A : Finset (Fin n)) : Finset ℕ :=
  A.map ⟨Fin.val, Fin.val_injective⟩

lemma finMask_eq_geom {n : ℕ} (A : Finset (Fin n)) :
    finMask A = ∑ i ∈ natImage A, 2 ^ i := by
  simp [finMask, natImage]

theorem finMask_injective {n : ℕ} :
    Function.Injective (finMask : Finset (Fin n) → ℕ) := by
  intro A B h
  have hgeom : natImage A = natImage B := by
    apply Finset.geomSum_injective (n := 2) (by omega)
    simpa only [← finMask_eq_geom] using h
  exact Finset.map_injective ⟨Fin.val, Fin.val_injective⟩ hgeom

@[simp] theorem bitIndices_finMask {n : ℕ} (A : Finset (Fin n)) :
    (finMask A).bitIndices.toFinset = natImage A := by
  rw [finMask_eq_geom]
  exact Finset.toFinset_bitIndices_sum_two_pow (natImage A)

theorem bitIndices_length_finMask {n : ℕ} (A : Finset (Fin n)) :
    (finMask A).bitIndices.length = A.card := by
  calc
    (finMask A).bitIndices.length =
        (finMask A).bitIndices.toFinset.card :=
      (List.toFinset_card_of_nodup Nat.bitIndices_sorted.nodup).symm
    _ = (natImage A).card := congrArg Finset.card (bitIndices_finMask A)
    _ = A.card := by simp [natImage]

end AMEProbe.MaskEncoding

#print axioms AMEProbe.MaskEncoding.finMask_injective
#print axioms AMEProbe.MaskEncoding.bitIndices_length_finMask
