import GraphState

/-! Normalization of the explicit twelve-site graph amplitudes. -/
open scoped BigOperators
namespace AMEProbe.GraphNormalization
open GraphCharacter GraphState

lemma amplitude_mul_star {n p : ℕ} [NeZero p] (c : ℂ)
    (G : Fin n → Fin n → ZMod p) (x : Fin n → ZMod p) :
    amplitude c G x * star (amplitude c G x) = c * star c := by
  have h := stdAddChar_mul_star (graphPhase G x) (graphPhase G x)
  simp only [sub_self, AddChar.map_zero_eq_one] at h
  unfold amplitude
  rw [star_mul]
  calc
    _ = (c * star c) * (ZMod.stdAddChar (graphPhase G x) *
        star (ZMod.stdAddChar (graphPhase G x))) := by ring
    _ = _ := by rw [h, mul_one]

/-- The squared norm is one; no cut hypotheses are required for normalization. -/
theorem normalized12 {p : ℕ} [NeZero p]
    (G : Fin 12 → Fin 12 → ZMod p) :
    (∑ x : Fin 12 → ZMod p, amplitude12 G x * star (amplitude12 G x)) = 1 := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hc : star (((p : ℂ) ^ 6)⁻¹) = ((p : ℂ) ^ 6)⁻¹ := by
    change (starRingEnd ℂ) (((p : ℂ) ^ 6)⁻¹) = _
    simp only [map_inv₀, map_pow, map_natCast]
  simp only [amplitude12, amplitude_mul_star]
  rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, ZMod.card, nsmul_eq_mul, Nat.cast_pow]
  have hpow : (p : ℂ) ^ 12 = (p : ℂ) ^ 6 * (p : ℂ) ^ 6 := by ring
  rw [hpow]
  field_simp

end AMEProbe.GraphNormalization
#print axioms AMEProbe.GraphNormalization.normalized12
