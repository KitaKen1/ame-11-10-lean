import FCSubsystemBridge

/-! Reindex finite local values without changing amplitudes, norms, or reductions. -/
open scoped BigOperators
open OpenQuantumProblem35
namespace AMEProbe.FCValueBridge
open GraphCharacter FCSubsystemBridge

lemma map_paste {n : ℕ} {R T : Type*} (f : R → T) (A : Finset (Fin n))
    (x : A → R) (z : {i : Fin n // i ∉ A} → R) :
    (fun i => f (pasteOn A x z i)) =
      pasteOn A (fun i => f (x i)) (fun i => f (z i)) := by
  funext i
  by_cases hi : i ∈ A <;> simp [pasteOn, hi]

/-- In particular, this transfers `ZMod d` coordinates into FC's `Fin d` coordinates. -/
theorem existsAME_of_reindexed {n d : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (e : Fin d ≃ R) (f : (Fin n → R) → ℂ)
    (hnorm : (∑ w, f w * star (f w)) = 1)
    (hred : ∀ (A : Finset (Fin n)), A.card = n/2 → ∀ x y : A → R,
      (∑ z : {i : Fin n // i ∉ A} → R,
        f (pasteOn A x z) * star (f (pasteOn A y z))) =
          if x = y then ((d : ℂ) ^ (n/2))⁻¹ else 0) : ExistsAME n d := by
  apply existsAME_of_subsystem_reductions (fun x => f (fun i => e (x i)))
  · let ef : Config n d ≃ (Fin n → R) :=
      Equiv.arrowCongr (Equiv.refl (Fin n)) e
    calc
      _ = ∑ w : Fin n → R, f w * star (f w) :=
        ef.sum_comp (fun w => f w * star (f w))
      _ = 1 := hnorm
  · intro A hA x y
    simp_rw [map_paste]
    let xr : A → R := fun i => e (x i)
    let yr : A → R := fun i => e (y i)
    let ez : ({i : Fin n // i ∉ A} → Fin d) ≃ ({i : Fin n // i ∉ A} → R) :=
      Equiv.arrowCongr (Equiv.refl _) e
    change (∑ z : {i : Fin n // i ∉ A} → Fin d,
      f (pasteOn A xr (ez z)) * star (f (pasteOn A yr (ez z)))) = _
    calc
      _ = ∑ z : {i : Fin n // i ∉ A} → R,
          f (pasteOn A xr z) * star (f (pasteOn A yr z)) :=
        ez.sum_comp (fun z => f (pasteOn A xr z) * star (f (pasteOn A yr z)))
      _ = if xr = yr then ((d : ℂ) ^ (n/2))⁻¹ else 0 := hred A hA xr yr
      _ = _ := by
        have hxy : xr = yr ↔ x = y := by
          constructor
          · intro h
            funext i
            exact e.injective (congrFun h i)
          · rintro rfl
            rfl
        simp only [hxy]

end AMEProbe.FCValueBridge
#print axioms AMEProbe.FCValueBridge.existsAME_of_reindexed
