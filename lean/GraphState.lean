import GraphCharacter
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Matrix.Mul

/-! Graph amplitudes and exact matrix certificates for the cut criterion. -/
open scoped BigOperators
namespace AMEProbe.GraphState
open GraphCharacter

noncomputable def amplitude {n p : ℕ} [NeZero p]
    (c : ℂ) (G : Fin n → Fin n → ZMod p) (x : Fin n → ZMod p) : ℂ :=
  c * ZMod.stdAddChar (graphPhase G x)

/-- The normalization factor is separated from character orthogonality. -/
theorem reduction_amplitude {n p : ℕ} [NeZero p]
    (c : ℂ) (G : Fin n → Fin n → ZMod p)
    (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 0)
    (A : Finset (Fin n)) (hcut : CutInjective G A) (x y : A → ZMod p) :
    reduction (fun x z => amplitude c G (pasteOn A x z))
      (fun x z => amplitude c G (pasteOn A x z)) x y =
        c * star c * (if x = y then
          (p : ℂ) ^ Fintype.card {i : Fin n // i ∉ A} else 0) := by
  unfold reduction amplitude
  simp only [star_mul]
  have hterm (z : {i : Fin n // i ∉ A} → ZMod p) :
      c * ZMod.stdAddChar (graphPhase G (pasteOn A x z)) *
        (star (ZMod.stdAddChar (graphPhase G (pasteOn A y z))) * star c) =
      (c * star c) * (ZMod.stdAddChar (graphPhase G (pasteOn A x z)) *
        star (ZMod.stdAddChar (graphPhase G (pasteOn A y z)))) := by ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, phase_paste_sum G hsym hdiag A hcut]

/-- A 12-vertex graph uses the scalar p^(-6), so no square root is needed. -/
noncomputable def amplitude12 {p : ℕ} [NeZero p]
    (G : Fin 12 → Fin 12 → ZMod p) : (Fin 12 → ZMod p) → ℂ :=
  amplitude ((p : ℂ) ^ 6)⁻¹ G

lemma card_complement {n : ℕ} (A : Finset (Fin n)) :
    Fintype.card {i : Fin n // i ∉ A} = n - A.card := by
  rw [Fintype.card_subtype_compl]
  simp

theorem binary_reduction (G : Fin 12 → Fin 12 → ZMod 2)
    (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 0)
    (A : Finset (Fin 12)) (hA : A.card = 5) (hcut : CutInjective G A)
    (x y : A → ZMod 2) :
    reduction (fun x z => amplitude12 G (pasteOn A x z))
      (fun x z => amplitude12 G (pasteOn A x z)) x y =
        if x = y then (1 / 2 ^ 5 : ℂ) else 0 := by
  rw [amplitude12, reduction_amplitude _ G hsym hdiag A hcut, card_complement, hA]
  split_ifs <;> norm_num

theorem quinary_reduction (G : Fin 12 → Fin 12 → ZMod 5)
    (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 0)
    (A : Finset (Fin 12)) (hA : A.card = 6) (hcut : CutInjective G A)
    (x y : A → ZMod 5) :
    reduction (fun x z => amplitude12 G (pasteOn A x z))
      (fun x z => amplitude12 G (pasteOn A x z)) x y =
        if x = y then (1 / 5 ^ 6 : ℂ) else 0 := by
  rw [amplitude12, reduction_amplitude _ G hsym hdiag A hcut, card_complement, hA]
  split_ifs <;> norm_num

/-- Rows index the complement, columns the selected subsystem. -/
def cutMatrix {n p k t : ℕ} (G : Fin n → Fin n → ZMod p)
    (A : Finset (Fin n)) (hA : A.card = k) (hAc : Aᶜ.card = t) :
    Matrix (Fin t) (Fin k) (ZMod p) :=
  fun i j => G ((Aᶜ.orderIsoOfFin hAc) i).1 ((A.orderIsoOfFin hA) j).1

/-- Filtering a fixed ordered list is kernel-computable, unlike merge-sort recursion. -/
def enumerateCut {n : ℕ} (A : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun i => decide (i ∈ A))

lemma enumerateCut_eq_sort {n : ℕ} (A : Finset (Fin n)) : enumerateCut A = A.sort := by
  have hfin : (enumerateCut A).toFinset = A := by ext i; simp [enumerateCut]
  have hnd : (enumerateCut A).Nodup := (List.nodup_finRange n).filter _
  have hsort : (enumerateCut A).Pairwise (· ≤ ·) :=
    (List.sortedLT_finRange n).sortedLE.pairwise.filter _
  have hh := ((List.toFinset_sort (r := (· ≤ ·)) hnd).mpr hsort).symm
  simpa only [hfin] using hh

/-- A computational form, without the noncomputable order isomorphism. -/
def executableCutMatrix {n p k t : ℕ} [NeZero n]
    (G : Fin n → Fin n → ZMod p) (A : Finset (Fin n)) :
    Matrix (Fin t) (Fin k) (ZMod p) :=
  fun i j => G ((enumerateCut Aᶜ)[i.val]?.getD 0) ((enumerateCut A)[j.val]?.getD 0)

lemma executableCutMatrix_eq {n p k t : ℕ} [NeZero n]
    (G : Fin n → Fin n → ZMod p) (A : Finset (Fin n))
    (hA : A.card = k) (hAc : Aᶜ.card = t) :
    executableCutMatrix G A = cutMatrix G A hA hAc := by
  funext i j
  simp only [cutMatrix, Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  dsimp only [executableCutMatrix]
  rw [enumerateCut_eq_sort, enumerateCut_eq_sort]
  rw [List.getElem?_eq_getElem (by simpa [hAc] using i.isLt),
    List.getElem?_eq_getElem (by simpa [hA] using j.isLt)]
  rfl

/-- A checked left inverse is a complete certificate of cut injectivity. -/
theorem cutInjective_of_leftInverse {n p k t : ℕ}
    (G : Fin n → Fin n → ZMod p) (A : Finset (Fin n))
    (hA : A.card = k) (hAc : Aᶜ.card = t)
    (L : Matrix (Fin k) (Fin t) (ZMod p))
    (hL : L * cutMatrix G A hA hAc = 1) : CutInjective G A := by
  intro x y hxy
  let eA := A.orderIsoOfFin hA
  let eC := Aᶜ.orderIsoOfFin hAc
  have hvout : (cutMatrix G A hA hAc).mulVec (x ∘ eA) =
      (cutMatrix G A hA hAc).mulVec (y ∘ eA) := by
    funext r
    have her : (eC r).1 ∉ A := by
      simpa only [Finset.mem_compl] using (eC r).2
    have hr := congrFun hxy ⟨(eC r).1, her⟩
    change (∑ j : Fin k, G (eC r).1 (eA j).1 * x (eA j)) =
      ∑ j : Fin k, G (eC r).1 (eA j).1 * y (eA j)
    calc
      _ = ∑ i : A, G (eC r).1 i.1 * x i :=
        eA.toEquiv.sum_comp (fun i : A => G (eC r).1 i.1 * x i)
      _ = ∑ i : A, G (eC r).1 i.1 * y i := hr
      _ = _ := (eA.toEquiv.sum_comp (fun i : A => G (eC r).1 i.1 * y i)).symm
  have hv := congrArg (L.mulVec) hvout
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hL] at hv
  simp only [Matrix.one_mulVec] at hv
  funext i
  obtain ⟨r, rfl⟩ := eA.surjective i
  exact congrFun hv r

end AMEProbe.GraphState
#print axioms AMEProbe.GraphState.quinary_reduction
#print axioms AMEProbe.GraphState.cutInjective_of_leftInverse
