import GraphCharacter

/-!
# Lifting an eleven-site cut to a twelve-site parent

The extra coordinate `0` is the branch label.  Physical coordinates are shifted
by `Fin.succ`.  These definitions are shared by the binary and quinary parents.
-/
namespace AMEProbe.LiftedCuts
open GraphCharacter

def physicalSet (A : Finset (Fin 11)) : Finset (Fin 12) :=
  A.map ⟨Fin.succ, Fin.succ_injective 11⟩

@[simp] theorem physicalSet_card (A : Finset (Fin 11)) :
    (physicalSet A).card = A.card := by
  simp [physicalSet]

@[simp] theorem physicalSet_zero (A : Finset (Fin 11)) :
    (0 : Fin 12) ∉ physicalSet A := by
  simp [physicalSet]

@[simp] theorem physicalSet_succ (A : Finset (Fin 11)) (i : Fin 11) :
    Fin.succ i ∈ physicalSet A ↔ i ∈ A := by
  simp [physicalSet]

def augmentedSet (A : Finset (Fin 11)) : Finset (Fin 12) :=
  insert 0 (physicalSet A)

@[simp] theorem augmentedSet_card (A : Finset (Fin 11)) :
    (augmentedSet A).card = A.card + 1 := by
  simp [augmentedSet]

@[simp] theorem augmentedSet_zero (A : Finset (Fin 11)) :
    (0 : Fin 12) ∈ augmentedSet A := by
  simp [augmentedSet]

@[simp] theorem augmentedSet_succ (A : Finset (Fin 11)) (i : Fin 11) :
    Fin.succ i ∈ augmentedSet A ↔ i ∈ A := by
  simp [augmentedSet]

/-- Put the branch label at coordinate zero and the physical word after it. -/
def parentWord {R : Type*} (a : R) (x : Fin 11 → R) : Fin 12 → R :=
  Fin.cases a x

@[simp] theorem parentWord_zero {R : Type*} (a : R) (x : Fin 11 → R) :
    parentWord a x 0 = a := rfl

@[simp] theorem parentWord_succ {R : Type*} (a : R) (x : Fin 11 → R)
    (i : Fin 11) : parentWord a x (Fin.succ i) = x i := rfl

def physicalRow {R : Type*} [Zero R] (A : Finset (Fin 11)) (x : A → R) :
    physicalSet A → R :=
  fun i => parentWord 0 (fun j => if hj : j ∈ A then x ⟨j, hj⟩ else 0) i.1

def augmentedRow {R : Type*} [Zero R] (A : Finset (Fin 11))
    (a : R) (x : A → R) : augmentedSet A → R :=
  fun i => parentWord a (fun j => if hj : j ∈ A then x ⟨j, hj⟩ else 0) i.1

@[simp] theorem physicalRow_succ {R : Type*} [Zero R] (A : Finset (Fin 11))
    (x : A → R) (i : A) :
    physicalRow A x ⟨Fin.succ i.1, by simp⟩ = x i := by
  simp [physicalRow]

@[simp] theorem augmentedRow_zero {R : Type*} [Zero R] (A : Finset (Fin 11))
    (a : R) (x : A → R) :
    augmentedRow A a x ⟨0, by simp⟩ = a := rfl

@[simp] theorem augmentedRow_succ {R : Type*} [Zero R] (A : Finset (Fin 11))
    (a : R) (x : A → R) (i : A) :
    augmentedRow A a x ⟨Fin.succ i.1, by simp⟩ = x i := by
  simp [augmentedRow]

/-- The complement of a physical cut is coordinate zero or a shifted physical
complement coordinate. -/
def physicalComplementIndexEquiv (A : Finset (Fin 11)) :
    {i : Fin 12 // i ∉ physicalSet A} ≃ Option {i : Fin 11 // i ∉ A} where
  toFun i := if hi : i.1 = 0 then none else
    some ⟨i.1.pred hi, by
      intro hmem
      apply i.2
      have hs : Fin.succ (i.1.pred hi) = i.1 := Fin.succ_pred i.1 hi
      rw [← hs]
      exact (physicalSet_succ A _).2 hmem⟩
  invFun
    | none => ⟨0, by simp⟩
    | some j => ⟨Fin.succ j.1, by simpa using j.2⟩
  left_inv i := by
    apply Subtype.ext
    by_cases hi : i.1 = 0
    · simp [hi]
    · simp [hi, Fin.succ_pred]
  right_inv o := by
    cases o with
    | none => simp
    | some j => simp

/-- The complement of a physical cut consists of the branch coordinate and the
complementary physical coordinates. -/
def physicalComplementEquiv {R : Type*} (A : Finset (Fin 11)) :
    (R × ({i : Fin 11 // i ∉ A} → R)) ≃
      ({i : Fin 12 // i ∉ physicalSet A} → R) :=
  ((Equiv.arrowCongr (physicalComplementIndexEquiv A) (Equiv.refl R)).trans
    Equiv.piOptionEquivProd).symm

/-- An augmented-complement coordinate is uniquely a successor coordinate. -/
def augmentedComplementIndexEquiv (A : Finset (Fin 11)) :
    {i : Fin 12 // i ∉ augmentedSet A} ≃ {i : Fin 11 // i ∉ A} where
  toFun i := by
    have hi : i.1 ≠ 0 := by
      intro h
      apply i.2
      simpa [h]
    refine ⟨i.1.pred hi, ?_⟩
    intro hmem
    apply i.2
    have hs : Fin.succ (i.1.pred hi) = i.1 := Fin.succ_pred i.1 hi
    rw [← hs]
    exact (augmentedSet_succ A _).2 hmem
  invFun j := ⟨Fin.succ j.1, by simpa using j.2⟩
  left_inv i := by
    apply Subtype.ext
    dsimp
    exact Fin.succ_pred i.1 _
  right_inv j := by
    apply Subtype.ext
    simp

/-- Removing coordinate zero identifies the complement of an augmented cut with
the complement of the original eleven-site cut. -/
def augmentedComplementEquiv {R : Type*} (A : Finset (Fin 11)) :
    ({i : Fin 11 // i ∉ A} → R) ≃
      ({i : Fin 12 // i ∉ augmentedSet A} → R) :=
  Equiv.arrowCongr (augmentedComplementIndexEquiv A).symm (Equiv.refl R)

theorem parentWord_paste_physical {R : Type*} [Zero R]
    (A : Finset (Fin 11)) (a : R) (x : A → R)
    (z : {i : Fin 11 // i ∉ A} → R) :
    parentWord a (pasteOn A x z) =
      pasteOn (physicalSet A) (physicalRow A x)
        (physicalComplementEquiv A (a, z)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pasteOn, physicalComplementEquiv, physicalComplementIndexEquiv,
      Equiv.piOptionEquivProd]
  · by_cases hj : j ∈ A
    · simp only [parentWord_succ, pasteOn, hj, dite_true,
        physicalSet_succ]
      simp [physicalRow, hj]
    · simp [pasteOn, hj, physicalComplementEquiv,
        physicalComplementIndexEquiv, Equiv.piOptionEquivProd]

theorem parentWord_paste_augmented {R : Type*} [Zero R]
    (A : Finset (Fin 11)) (a : R) (x : A → R)
    (z : {i : Fin 11 // i ∉ A} → R) :
    parentWord a (pasteOn A x z) =
      pasteOn (augmentedSet A) (augmentedRow A a x)
        (augmentedComplementEquiv A z) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pasteOn]
  · by_cases hj : j ∈ A
    · simp only [parentWord_succ, pasteOn, hj, dite_true,
        augmentedSet_succ]
      simp [augmentedRow, hj]
    · simp [pasteOn, hj, augmentedComplementEquiv,
        augmentedComplementIndexEquiv]

theorem physicalRow_injective {R : Type*} [Zero R] (A : Finset (Fin 11)) :
    Function.Injective (physicalRow (R := R) A) := by
  intro x y h
  funext i
  simpa only [physicalRow_succ] using congrFun h ⟨Fin.succ i.1, by simp⟩

theorem augmentedRow_eq_iff {R : Type*} [Zero R] (A : Finset (Fin 11))
    (a b : R) (x y : A → R) :
    augmentedRow A a x = augmentedRow A b y ↔ a = b ∧ x = y := by
  constructor
  · intro h
    constructor
    · exact congrFun h ⟨0, by simp⟩
    · funext i
      simpa only [augmentedRow_succ] using congrFun h ⟨Fin.succ i.1, by simp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end AMEProbe.LiftedCuts
