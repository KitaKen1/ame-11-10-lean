import CoupledState

/-! The normalized eleven-site local-dimension-ten state. -/
open scoped BigOperators
namespace AMEProbe.FinalState
open GraphCharacter CoupledState

noncomputable def scale : ℂ := (Real.sqrt 5 : ℂ) / 1000000

noncomputable def amplitude (x : Fin 11 → Local) : ℂ :=
  scale * rawAmplitude x

lemma scale_identity : scale * star scale * (2000000 : ℂ) = 1 / 100000 := by
  have hs : Real.sqrt (5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs' : Real.sqrt (5 : ℝ) * Real.sqrt (5 : ℝ) = 5 := by
    simpa [pow_two] using hs
  have hsC : (Real.sqrt (5 : ℝ) : ℂ) * (Real.sqrt (5 : ℝ) : ℂ) = 5 := by
    exact_mod_cast hs'
  have hstar : (starRingEnd ℂ) (Real.sqrt (5 : ℝ) : ℂ) =
      (Real.sqrt (5 : ℝ) : ℂ) := Complex.conj_ofReal _
  have hden : (starRingEnd ℂ) (1000000 : ℂ) = 1000000 := by
    apply Complex.ext <;> norm_num
  change ((Real.sqrt (5 : ℝ) : ℂ) / 1000000) *
    (starRingEnd ℂ) ((Real.sqrt (5 : ℝ) : ℂ) / 1000000) * 2000000 = 1 / 100000
  rw [map_div₀, hstar, hden]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (Real.sqrt (5 : ℝ) : ℂ) * (1000000 : ℂ)⁻¹ *
        ((Real.sqrt (5 : ℝ) : ℂ) * (1000000 : ℂ)⁻¹) * 2000000 =
      ((Real.sqrt (5 : ℝ) : ℂ) * (Real.sqrt (5 : ℝ) : ℂ)) *
        ((1000000 : ℂ)⁻¹ * (1000000 : ℂ)⁻¹ * 2000000) := by ring
    _ = 1 / 100000 := by rw [hsC]; norm_num

lemma reduction_scale {X U : Type*} [Fintype U]
    (c : ℂ) (f : X → U → ℂ) (x y : X) :
    reduction (fun x z => c * f x z) (fun x z => c * f x z) x y =
      c * star c * reduction f f x y := by
  unfold reduction
  simp only [star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem reduction_formula (A : Finset (Fin 11)) (hA : A.card = 5)
    (x y : A → Local) :
    reduction (fun x z => amplitude (pasteOn A x z))
      (fun x z => amplitude (pasteOn A x z)) x y =
        if x = y then (1 / 100000 : ℂ) else 0 := by
  change reduction (fun x z => scale * rawAmplitude (pasteOn A x z))
    (fun x z => scale * rawAmplitude (pasteOn A x z)) x y = _
  rw [reduction_scale]
  rw [raw_reduction A hA]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy, scale_identity]
  · rw [if_neg hxy, if_neg hxy]
    ring

def splitOnEquiv {ι R : Type*} [DecidableEq ι] (A : Finset ι) :
    ((A → R) × ({i : ι // i ∉ A} → R)) ≃ (ι → R) where
  toFun p := pasteOn A p.1 p.2
  invFun f := (fun i => f i.1, fun i => f i.1)
  left_inv p := by
    apply Prod.ext <;> funext i
    · exact pasteOn_mem A p.1 p.2 i
    · exact pasteOn_not_mem A p.1 p.2 i
  right_inv f := by
    funext i
    by_cases hi : i ∈ A <;> simp [pasteOn, hi]

def normSet : Finset (Fin 11) := Finset.univ.filter (fun i => i.val < 5)

theorem normSet_card : normSet.card = 5 := by decide +kernel

theorem normalized :
    (∑ w : Fin 11 → Local, amplitude w * star (amplitude w)) = 1 := by
  rw [← (splitOnEquiv (R := Local) normSet).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ x : normSet → Local,
    ∑ z : {i : Fin 11 // i ∉ normSet} → Local,
      amplitude (pasteOn normSet x z) * star (amplitude (pasteOn normSet x z))) = 1
  have hx (x : normSet → Local) :
      (∑ z : {i : Fin 11 // i ∉ normSet} → Local,
        amplitude (pasteOn normSet x z) * star (amplitude (pasteOn normSet x z))) =
          (1 / 100000 : ℂ) := by
    have h := reduction_formula normSet normSet_card x x
    rw [if_pos rfl] at h
    exact h
  simp_rw [hx]
  simp [Fintype.card_fun, Fintype.card_coe, normSet_card, ZMod.card]

end AMEProbe.FinalState

#print axioms AMEProbe.FinalState.reduction_formula
#print axioms AMEProbe.FinalState.normalized
