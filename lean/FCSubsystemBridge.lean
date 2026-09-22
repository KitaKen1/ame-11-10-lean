import FCBridge
import GraphState

/-!
# Coordinate transport for the Formal Conjectures interface

Independent implementation of the coordinate reindexing needed to transport
an arbitrary-subsystem reduction formula to the ordered reduction used by the
Formal Conjectures definition.
-/
open scoped BigOperators
open OpenQuantumProblem35
namespace AMEProbe.FCSubsystemBridge
open GraphCharacter

private def chosenSites {n : ℕ} (m : ℕ) (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (π i).val < m)

@[simp] private lemma mem_chosenSites {n m : ℕ} (π : Equiv.Perm (Fin n))
    (i : Fin n) : i ∈ chosenSites m π ↔ (π i).val < m := by
  simp [chosenSites]

private def chosenIndex {n m : ℕ} (hm : m ≤ n) (π : Equiv.Perm (Fin n)) :
    chosenSites m π ≃ Fin m where
  toFun i := ⟨(π i).val, (mem_chosenSites π i.val).mp i.property⟩
  invFun k := ⟨π.symm ⟨k, by omega⟩, by simp⟩
  left_inv i := by
    apply Subtype.ext
    exact π.injective (by simp)
  right_inv k := by
    apply Fin.ext
    simp

private def omittedIndex {n m : ℕ} (hm : m ≤ n) (π : Equiv.Perm (Fin n)) :
    {i : Fin n // i ∉ chosenSites m π} ≃ Fin (n - m) where
  toFun i := ⟨(π i).val - m, by
    have hlo : m ≤ (π i).val := Nat.le_of_not_gt (by simpa using i.property)
    have hhi : (π i).val < n := (π i).isLt
    omega⟩
  invFun k := ⟨π.symm ⟨k.val + m, by omega⟩, by
    simp only [mem_chosenSites, Equiv.apply_symm_apply]
    omega⟩
  left_inv i := by
    apply Subtype.ext
    apply π.injective
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    have hlo : m ≤ (π i).val := Nat.le_of_not_gt (by simpa using i.property)
    omega
  right_inv k := by
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    omega

private lemma card_chosenSites {n m : ℕ} (hm : m ≤ n)
    (π : Equiv.Perm (Fin n)) : (chosenSites m π).card = m := by
  calc
    (chosenSites m π).card = Fintype.card (chosenSites m π) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (Fin m) := Fintype.card_congr (chosenIndex hm π)
    _ = m := Fintype.card_fin m

private lemma permuted_join {n m d : ℕ} (hm : m ≤ n)
    (π : Equiv.Perm (Fin n))
    (x : Config m d) (z : Config (n-m) d) :
    permuteConfig π (combineFirst m hm x z) =
      pasteOn (chosenSites m π) (fun i => x (chosenIndex hm π i))
        (fun i => z (omittedIndex hm π i)) := by
  funext i
  by_cases hi : i ∈ chosenSites m π
  · rw [show pasteOn (chosenSites m π) (fun i => x (chosenIndex hm π i))
        (fun i => z (omittedIndex hm π i)) i =
        x (chosenIndex hm π ⟨i, hi⟩) by simp [pasteOn, hi]]
    simp only [permuteConfig, combineFirst]
    rw [dif_pos ((mem_chosenSites π i).mp hi)]
    rfl
  · rw [show pasteOn (chosenSites m π) (fun i => x (chosenIndex hm π i))
        (fun i => z (omittedIndex hm π i)) i =
        z (omittedIndex hm π ⟨i, hi⟩) by simp [pasteOn, hi]]
    simp only [permuteConfig, combineFirst]
    rw [dif_neg (by simpa using hi)]
    rfl

private lemma normalized_of_squared_amplitudes {n d : ℕ} (f : Config n d → ℂ)
    (h : (∑ w, f w * star (f w)) = 1) : IsNormalized (mkStateVector f) := by
  have hsquares : (∑ w, ‖f w‖ ^ 2) = 1 := by
    apply Complex.ofReal_injective
    push_cast
    simp_rw [show ∀ z : ℂ, (↑‖z‖ : ℂ) ^ 2 = z * star z from
      fun z => (RCLike.mul_conj z).symm]
    exact h
  simp only [IsNormalized, EuclideanSpace.norm_eq]
  change Real.sqrt (∑ w, ‖f w‖ ^ 2) = 1
  simp [hsquares]

/-- A semantic bridge: all hypotheses refer to explicit finite amplitude sums. -/
theorem existsAME_of_subsystem_reductions {n d : ℕ} (f : Config n d → ℂ)
    (hnorm : (∑ w, f w * star (f w)) = 1)
    (hred : ∀ (A : Finset (Fin n)), A.card = n/2 → ∀ x y : A → Fin d,
      (∑ z : {i : Fin n // i ∉ A} → Fin d,
        f (pasteOn A x z) * star (f (pasteOn A y z))) =
          if x = y then ((d : ℂ) ^ (n/2))⁻¹ else 0) : ExistsAME n d := by
  refine ⟨mkStateVector f, normalized_of_squared_amplitudes f hnorm, ?_⟩
  intro π
  unfold HasMaximallyMixedFirstReduction
  ext x y
  change (∑ z : Config (n - n/2) d,
    f (permuteConfig π (combineFirst (n/2) (Nat.div_le_self n 2) x z)) *
      star (f (permuteConfig π (combineFirst (n/2) (Nat.div_le_self n 2) y z)))) = _
  simp_rw [permuted_join]
  let hm := Nat.div_le_self n 2
  let A := chosenSites (n / 2) π
  let xb : A → Fin d := fun i => x (chosenIndex hm π i)
  let yb : A → Fin d := fun i => y (chosenIndex hm π i)
  let reindex : Config (n - n/2) d ≃ ({i : Fin n // i ∉ A} → Fin d) :=
    Equiv.arrowCongr (omittedIndex hm π).symm (Equiv.refl (Fin d))
  change (∑ z : Config (n - n/2) d,
    f (pasteOn A xb (reindex z)) * star (f (pasteOn A yb (reindex z)))) = _
  calc
    _ = ∑ z : {i : Fin n // i ∉ A} → Fin d,
        f (pasteOn A xb z) * star (f (pasteOn A yb z)) :=
      reindex.sum_comp (fun z => f (pasteOn A xb z) * star (f (pasteOn A yb z)))
    _ = if xb = yb then ((d : ℂ) ^ (n/2))⁻¹ else 0 :=
      hred A (card_chosenSites hm π) xb yb
    _ = _ := by
      have hxy : xb = yb ↔ x = y := by
        constructor
        · intro h
          funext k
          obtain ⟨i, rfl⟩ := (chosenIndex hm π).surjective k
          exact congrFun h i
        · rintro rfl
          rfl
      simp only [hxy, maximallyMixed_apply, card_config, Nat.cast_pow]

end AMEProbe.FCSubsystemBridge
#print axioms AMEProbe.FCSubsystemBridge.existsAME_of_subsystem_reductions
