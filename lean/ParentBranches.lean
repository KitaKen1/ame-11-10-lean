import BinaryParent
import QuinaryParent
import LiftedCuts

/-!
# Branch reductions inherited from the two twelve-site parents

Coordinate zero is exposed as a branch label.  The binary parent supplies the
sum of the two diagonal blocks; the quinary parent supplies diagonal blocks and
vanishing cross blocks.
-/
open scoped BigOperators
namespace AMEProbe.ParentBranches
open GraphCharacter GraphState LiftedCuts

noncomputable def binaryRaw (a : ZMod 2) (x : Fin 11 → ZMod 2) : ℂ :=
  ZMod.stdAddChar (graphPhase BinaryGraph.graph (parentWord a x))

noncomputable def quinaryRaw (a : ZMod 5) (x : Fin 11 → ZMod 5) : ℂ :=
  ZMod.stdAddChar (graphPhase QuinaryGraph.graph (parentWord a x))

lemma sum_zmod_two (f : ZMod 2 → ℂ) :
    (∑ a : ZMod 2, f a) = f 0 + f 1 := by
  rw [← (ZMod.finEquiv 2).toEquiv.sum_comp]
  rw [Fin.sum_univ_two]
  rfl

theorem binary_diagonal_sum (A : Finset (Fin 11)) (hA : A.card = 5)
    (x y : A → ZMod 2) :
    (∑ a : ZMod 2, ∑ z : {i : Fin 11 // i ∉ A} → ZMod 2,
      binaryRaw a (pasteOn A x z) * star (binaryRaw a (pasteOn A y z))) =
        if x = y then (2 ^ 7 : ℂ) else 0 := by
  have hcut := BinaryParent.every_cut_injective (physicalSet A) (by simpa using hA)
  have hp := phase_paste_sum BinaryGraph.graph BinaryGraph.symmetric BinaryGraph.diagonal
    (physicalSet A) hcut (physicalRow A x) (physicalRow A y)
  rw [← (physicalComplementEquiv (R := ZMod 2) A).sum_comp] at hp
  rw [Fintype.sum_prod_type] at hp
  simp_rw [← parentWord_paste_physical] at hp
  change (∑ a : ZMod 2, ∑ z : {i : Fin 11 // i ∉ A} → ZMod 2,
    binaryRaw a (pasteOn A x z) * star (binaryRaw a (pasteOn A y z))) = _ at hp
  have hcard : Fintype.card {i : Fin 12 // i ∉ physicalSet A} = 7 := by
    rw [card_complement, physicalSet_card, hA]
  rw [hcard] at hp
  by_cases hxy : x = y
  · subst y
    simpa using hp
  · have hrow : physicalRow A x ≠ physicalRow A y := by
      intro h
      exact hxy ((physicalRow_injective (R := ZMod 2) A) h)
    simpa [hxy, hrow] using hp

theorem binary_two_diagonal_blocks (A : Finset (Fin 11)) (hA : A.card = 5)
    (x y : A → ZMod 2) :
    reduction (fun x z => binaryRaw 0 (pasteOn A x z))
        (fun x z => binaryRaw 0 (pasteOn A x z)) x y +
      reduction (fun x z => binaryRaw 1 (pasteOn A x z))
        (fun x z => binaryRaw 1 (pasteOn A x z)) x y =
        if x = y then (2 ^ 7 : ℂ) else 0 := by
  have h := binary_diagonal_sum A hA x y
  rw [sum_zmod_two] at h
  simpa only [reduction] using h

theorem quinary_cross_block (A : Finset (Fin 11)) (hA : A.card = 5)
    (a b : ZMod 5) (x y : A → ZMod 5) :
    (∑ z : {i : Fin 11 // i ∉ A} → ZMod 5,
      quinaryRaw a (pasteOn A x z) * star (quinaryRaw b (pasteOn A y z))) =
        if a = b ∧ x = y then (5 ^ 6 : ℂ) else 0 := by
  have haug : (augmentedSet A).card = 6 := by simpa [hA]
  have hcut := QuinaryParent.every_cut_injective (augmentedSet A) haug
  have hp := phase_paste_sum QuinaryGraph.graph QuinaryGraph.symmetric QuinaryGraph.diagonal
    (augmentedSet A) hcut (augmentedRow A a x) (augmentedRow A b y)
  rw [← (augmentedComplementEquiv (R := ZMod 5) A).sum_comp] at hp
  simp_rw [← parentWord_paste_augmented] at hp
  change (∑ z : {i : Fin 11 // i ∉ A} → ZMod 5,
    quinaryRaw a (pasteOn A x z) * star (quinaryRaw b (pasteOn A y z))) = _ at hp
  have hcard : Fintype.card {i : Fin 12 // i ∉ augmentedSet A} = 6 := by
    rw [card_complement, augmentedSet_card, hA]
  rw [hcard] at hp
  by_cases hab : a = b ∧ x = y
  · obtain ⟨rfl, rfl⟩ := hab
    simpa using hp
  · have hrow : augmentedRow A a x ≠ augmentedRow A b y := by
      intro h
      exact hab ((augmentedRow_eq_iff A a b x y).mp h)
    simpa [hab, hrow] using hp

theorem quinary_reduction_block (A : Finset (Fin 11)) (hA : A.card = 5)
    (a b : ZMod 5) (x y : A → ZMod 5) :
    reduction (fun x z => quinaryRaw a (pasteOn A x z))
      (fun x z => quinaryRaw b (pasteOn A x z)) x y =
        if a = b ∧ x = y then (5 ^ 6 : ℂ) else 0 := by
  simpa only [reduction] using quinary_cross_block A hA a b x y

end AMEProbe.ParentBranches

#print axioms AMEProbe.ParentBranches.binary_two_diagonal_blocks
#print axioms AMEProbe.ParentBranches.quinary_reduction_block
