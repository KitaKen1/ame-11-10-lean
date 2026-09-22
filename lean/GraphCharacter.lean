import AMEProbe
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# Graph-state cut criterion

This is an independent implementation of the standard character-orthogonality
proof for graph states. Earlier AME formalizations helped identify the useful
proof strategy; the argument here is developed for arbitrary finite cuts and
arbitrary symmetric graph matrices.

Concrete cut-injectivity certificates are separate checked obligations.
-/
open scoped BigOperators
namespace AMEProbe.GraphCharacter

private lemma one_coordinate_sum {N : ℕ} [NeZero N] (a : ZMod N) :
    (∑ x : ZMod N, ZMod.stdAddChar (a * x)) =
      if a = 0 then (N : ℂ) else 0 := by
  by_cases ha : a = 0
  · simp [ha, ZMod.card]
  · simpa [ha] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ha))

private lemma character_linear_form {N : ℕ} [NeZero N] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (c z : ι → ZMod N) :
    ZMod.stdAddChar (∑ i, c i * z i) =
      ∏ i, ZMod.stdAddChar (c i * z i) := by
  classical
  have h (s : Finset ι) :
      ZMod.stdAddChar (∑ i ∈ s, c i * z i) =
        ∏ i ∈ s, ZMod.stdAddChar (c i * z i) := by
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, Finset.prod_insert hi]
        rw [AddChar.map_add_eq_mul, ih]
  simpa using h Finset.univ

lemma sum_stdAddChar_dot {N : ℕ} [NeZero N] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (c : ι → ZMod N) :
    (∑ z : ι → ZMod N, ZMod.stdAddChar (∑ i, c i * z i)) =
      if c = 0 then (N ^ Fintype.card ι : ℂ) else 0 := by
  classical
  rw [show (∑ z : ι → ZMod N, ZMod.stdAddChar (∑ i, c i * z i)) =
      ∑ z : ι → ZMod N, ∏ i, ZMod.stdAddChar (c i * z i) by
        apply Finset.sum_congr rfl
        intro z _
        exact character_linear_form c z]
  calc
    (∑ z : ι → ZMod N, ∏ i, ZMod.stdAddChar (c i * z i)) =
        ∏ i, ∑ x : ZMod N, ZMod.stdAddChar (c i * x) :=
      (@Fintype.prod_sum ι ℂ _ _ _ (fun _ => ZMod N) _
        (fun i x => ZMod.stdAddChar (c i * x))).symm
    _ = _ := by
      simp_rw [one_coordinate_sum]
      by_cases hc : c = 0
      · subst c
        simp
      · rw [if_neg hc]
        obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
          simpa [funext_iff] using hc
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma stdAddChar_mul_star {N : ℕ} [NeZero N] (a b : ZMod N) :
    ZMod.stdAddChar a * star (ZMod.stdAddChar b) = ZMod.stdAddChar (a - b) := by
  change ZMod.stdAddChar a * (starRingEnd ℂ) (ZMod.stdAddChar b) = _
  rw [← AddChar.map_neg_eq_conj]
  simpa [sub_eq_add_neg] using (AddChar.map_add_eq_mul ZMod.stdAddChar a (-b)).symm

lemma norm_stdAddChar {N : ℕ} [NeZero N] (a : ZMod N) :
    ‖ZMod.stdAddChar a‖ = 1 := by
  change ‖(↑(ZMod.toCircle a) : ℂ)‖ = 1
  exact Circle.norm_coe _

def graphPhase {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (x : Fin n → ZMod p) : ZMod p :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, G i j * x i * x j

private lemma graphPhase_translate {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (x d : Fin n → ZMod p) :
    graphPhase G (x + d) = graphPhase G x + graphPhase G d +
      ∑ i, ∑ j ∈ Finset.Ioi i,
        G i j * (x i * d j + d i * x j) := by
  have expand (i j : Fin n) :
      G i j * (x i + d i) * (x j + d j) =
        G i j * x i * x j + G i j * d i * d j +
          G i j * (x i * d j + d i * x j) := by ring
  simp only [graphPhase, Pi.add_apply]
  simp_rw [expand, Finset.sum_add_distrib]

private lemma upper_triangle_cross {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 0)
    (x d : Fin n → ZMod p) :
    (∑ i, ∑ j ∈ Finset.Ioi i,
      G i j * (x i * d j + d i * x j)) =
      ∑ i, x i * ∑ j, G i j * d j := by
  let term := fun i j : Fin n => x i * (G i j * d j)
  have hupper :
      (∑ i, ∑ j ∈ Finset.Ioi i,
        G i j * (x i * d j + d i * x j)) =
        ∑ i, ∑ j ∈ Finset.Ioi i, (term i j + term j i) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [term]
    rw [← hsym i j]
    ring
  rw [hupper, Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  change (∑ j ∈ ({i}ᶜ : Finset (Fin n)), term i j) = ∑ j, term i j
  have herase : Finset.univ.erase i = ({i}ᶜ : Finset (Fin n)) := by
    ext j
    simp [eq_comm]
  rw [← herase]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp [term, hdiag]

private lemma graphPhase_difference {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 0)
    (x y : Fin n → ZMod p) :
    graphPhase G x - graphPhase G y = graphPhase G (x - y) +
      ∑ i, y i * ∑ j, G i j * (x j - y j) := by
  have hexpand := graphPhase_translate G y (x - y)
  rw [show y + (x - y) = x by abel] at hexpand
  rw [hexpand, upper_triangle_cross G hsym hdiag]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

private lemma sum_affine_character {N : ℕ} [NeZero N] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : ZMod N) (c : ι → ZMod N) :
    (∑ z : ι → ZMod N, ZMod.stdAddChar (b + ∑ i, c i * z i)) =
      ZMod.stdAddChar b * (if c = 0 then (N ^ Fintype.card ι : ℂ) else 0) := by
  calc
    _ = ∑ z : ι → ZMod N,
        ZMod.stdAddChar b * ZMod.stdAddChar (∑ i, c i * z i) := by
          apply Finset.sum_congr rfl
          intro z _
          exact AddChar.map_add_eq_mul ZMod.stdAddChar b _
    _ = ZMod.stdAddChar b *
        ∑ z : ι → ZMod N, ZMod.stdAddChar (∑ i, c i * z i) := by
          rw [Finset.mul_sum]
    _ = _ := by rw [sum_stdAddChar_dot]

def pasteOn {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) : ι → R :=
  fun i => dite (i ∈ A)
    (fun hi => x ⟨i, hi⟩)
    (fun hi => z ⟨i, hi⟩)

@[simp] lemma pasteOn_mem {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) (i : A) :
    pasteOn A x z i.1 = x i := by
  unfold pasteOn
  exact dif_pos i.property

@[simp] lemma pasteOn_not_mem {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) (i : {i : ι // i ∉ A}) :
    pasteOn A x z i.1 = z i := by
  unfold pasteOn
  exact dif_neg i.property

/-- The complement-by-subsystem cut matrix is injective on column vectors. -/
def CutInjective {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (A : Finset (Fin n)) : Prop :=
  Function.Injective (fun x : A → ZMod p =>
    fun j : {j : Fin n // j ∉ A} => ∑ i : A, G j.1 i.1 * x i)

private lemma supported_kernel_eq_zero {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (A : Finset (Fin n)) (hcut : CutInjective G A)
    (d : Fin n → ZMod p) (hsupp : ∀ i, i ∉ A → d i = 0)
    (hcoeff : ∀ j, j ∉ A → (∑ i, G j i * d i) = 0) : d = 0 := by
  have hrestricted : (fun j : {j : Fin n // j ∉ A} =>
        ∑ i : A, G j.1 i.1 * d i.1) = (fun _ => 0) := by
    funext j
    rw [← hcoeff j.1 j.2]
    calc
      (∑ i : A, G j.1 i.1 * d i.1) = ∑ i ∈ A, G j.1 i * d i := by
        simpa only [] using (Finset.sum_coe_sort A (fun i : Fin n => G j.1 i * d i))
      _ = ∑ i, G j.1 i * d i := by
        apply Finset.sum_subset (Finset.subset_univ A)
        intro i _ hi
        rw [hsupp i hi, mul_zero]
  have hdA : (fun i : A => d i.1) = 0 :=
    hcut (by simpa using hrestricted)
  funext i
  by_cases hi : i ∈ A
  · exact congrFun hdA ⟨i, hi⟩
  · exact hsupp i hi

private lemma pasted_phase_difference {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 0)
    (A : Finset (Fin n))
    (x y : A → ZMod p) (z : {i : Fin n // i ∉ A} → ZMod p) :
    let d := pasteOn A x 0 - pasteOn A y 0
    graphPhase G (pasteOn A x z) - graphPhase G (pasteOn A y z) =
      (graphPhase G d +
        ∑ i ∈ A.attach, y i * ∑ j, G i.1 j * d j) +
        ∑ i : {i : Fin n // i ∉ A},
          z i * (∑ j, G i.1 j * d j) := by
  dsimp only
  have hd : pasteOn A x z - pasteOn A y z =
      pasteOn A x 0 - pasteOn A y 0 := by
    ext i
    by_cases hi : i ∈ A <;> simp [pasteOn, hi]
  rw [graphPhase_difference G hsym hdiag, hd]
  have hdj (j : Fin n) : pasteOn A x z j - pasteOn A y z j =
      (pasteOn A x 0 - pasteOn A y 0) j := congrFun hd j
  simp_rw [hdj]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i ∈ A)
    (fun i => pasteOn A y z i *
      ∑ j, G i j * (pasteOn A x 0 - pasteOn A y 0) j)]
  simp only [pasteOn_mem, pasteOn_not_mem]
  rw [add_assoc]
  congr 2
  have hu : (@Finset.univ {i : Fin n // i ∈ A} (Subtype.fintype _)) =
      (@Finset.univ (↥A) (Finset.Subtype.fintype A)) := by
    ext i
    simp
  rw [hu]
  exact (Finset.sum_coe_sort_eq_attach A
    (fun i : A => y i * ∑ j, G i.1 j *
      (pasteOn A x 0 - pasteOn A y 0) j))

/-- Orthogonality of graph-state rows follows from injectivity of the cut matrix. -/
theorem phase_paste_sum {n p : ℕ} [NeZero p]
    (G : Fin n → Fin n → ZMod p)
    (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 0)
    (A : Finset (Fin n)) (hcut : CutInjective G A)
    (x y : A → ZMod p) :
    (∑ z : {i : Fin n // i ∉ A} → ZMod p,
      ZMod.stdAddChar (graphPhase G (pasteOn A x z)) *
        star (ZMod.stdAddChar (graphPhase G (pasteOn A y z)))) =
      if x = y then ((p : ℂ) ^ Fintype.card {i : Fin n // i ∉ A}) else 0 := by
  let d : Fin n → ZMod p := pasteOn A x 0 - pasteOn A y 0
  let c : {i : Fin n // i ∉ A} → ZMod p :=
    fun i => ∑ j, G i.1 j * d j
  let b : ZMod p := graphPhase G d +
    ∑ i ∈ A.attach, y i * ∑ j, G i.1 j * d j
  have hform (z : {i : Fin n // i ∉ A} → ZMod p) :
      graphPhase G (pasteOn A x z) - graphPhase G (pasteOn A y z) =
        b + ∑ i, c i * z i := by
    rw [pasted_phase_difference G hsym hdiag]
    dsimp [b, c, d]
    congr 2
    funext i
    ac_rfl
  simp_rw [stdAddChar_mul_star, hform]
  rw [sum_affine_character]
  have hc : c = 0 ↔ x = y := by
    apply Iff.intro
    · intro hzero
      have kernel_zero : d = 0 := supported_kernel_eq_zero G A hcut d
        (by
          intro k hk
          simp [d, pasteOn, hk])
        (by
          intro k hk
          simpa [c] using congrFun hzero ⟨k, hk⟩)
      apply funext
      intro i
      have hi : d i.1 = 0 := congrFun kernel_zero i.1
      dsimp [d] at hi
      exact sub_eq_zero.mp (by simpa using hi)
    · rintro rfl
      apply funext
      intro i
      simp [c, d]
  by_cases hxy : x = y
  · subst y
    have hzero := hc.mpr rfl
    simp [hzero, d, b, graphPhase]
  · have hnonzero : c ≠ 0 := fun hzero => hxy (hc.mp hzero)
    simp [hnonzero, hxy]

end AMEProbe.GraphCharacter

#print axioms AMEProbe.GraphCharacter.phase_paste_sum
