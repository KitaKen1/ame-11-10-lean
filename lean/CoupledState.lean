import ParentBranches
import FCValueBridge

/-! The unscaled eleven-site state obtained by coupling the two parent branches. -/
open scoped BigOperators
namespace AMEProbe.CoupledState
open GraphCharacter ParentBranches

abbrev Local := ZMod 2 × ZMod 5

def bitPart {ι : Type*} (x : ι → Local) : ι → ZMod 2 := fun i => (x i).1
def quintPart {ι : Type*} (x : ι → Local) : ι → ZMod 5 := fun i => (x i).2

def splitFunctionsEquiv (ι : Type*) :
    (ι → Local) ≃ ((ι → ZMod 2) × (ι → ZMod 5)) where
  toFun x := (bitPart x, quintPart x)
  invFun x i := (x.1 i, x.2 i)
  left_inv x := by funext i; exact Prod.ext rfl rfl
  right_inv x := by exact Prod.ext rfl rfl

@[simp] lemma bitPart_split_symm {ι : Type*} (x : ι → ZMod 2) (y : ι → ZMod 5) :
    bitPart ((splitFunctionsEquiv ι).symm (x, y)) = x := rfl

@[simp] lemma quintPart_split_symm {ι : Type*} (x : ι → ZMod 2) (y : ι → ZMod 5) :
    quintPart ((splitFunctionsEquiv ι).symm (x, y)) = y := rfl

lemma bitPart_paste (A : Finset (Fin 11)) (x : A → Local)
    (z : {i : Fin 11 // i ∉ A} → Local) :
    bitPart (pasteOn A x z) = pasteOn A (bitPart x) (bitPart z) :=
  FCValueBridge.map_paste (fun q : Local => q.1) A x z

lemma quintPart_paste (A : Finset (Fin 11)) (x : A → Local)
    (z : {i : Fin 11 // i ∉ A} → Local) :
    quintPart (pasteOn A x z) = pasteOn A (quintPart x) (quintPart z) :=
  FCValueBridge.map_paste (fun q : Local => q.2) A x z

noncomputable def rawAmplitude (x : Fin 11 → Local) : ℂ :=
  binaryRaw 0 (bitPart x) * quinaryRaw 0 (quintPart x) +
    binaryRaw 1 (bitPart x) * quinaryRaw 1 (quintPart x)

lemma rawAmplitude_paste_split (A : Finset (Fin 11)) (x : A → Local)
    (z : {i : Fin 11 // i ∉ A} → Local) :
    rawAmplitude (pasteOn A x z) =
      couple
        (fun x z => binaryRaw 0 (pasteOn A x z))
        (fun x z => binaryRaw 1 (pasteOn A x z))
        (fun x z => quinaryRaw 0 (pasteOn A x z))
        (fun x z => quinaryRaw 1 (pasteOn A x z))
        (bitPart x, quintPart x) (bitPart z, quintPart z) := by
  simp only [rawAmplitude, couple, bitPart_paste, quintPart_paste]

theorem coupled_raw_reduction (A : Finset (Fin 11)) (hA : A.card = 5)
    (xb yb : A → ZMod 2) (xq yq : A → ZMod 5) :
    reduction
      (couple
        (fun x z => binaryRaw 0 (pasteOn A x z))
        (fun x z => binaryRaw 1 (pasteOn A x z))
        (fun x z => quinaryRaw 0 (pasteOn A x z))
        (fun x z => quinaryRaw 1 (pasteOn A x z)))
      (couple
        (fun x z => binaryRaw 0 (pasteOn A x z))
        (fun x z => binaryRaw 1 (pasteOn A x z))
        (fun x z => quinaryRaw 0 (pasteOn A x z))
        (fun x z => quinaryRaw 1 (pasteOn A x z)))
      (xb, xq) (yb, yq) =
        if xb = yb ∧ xq = yq then (2000000 : ℂ) else 0 := by
  let u0 := fun x z => binaryRaw 0 (pasteOn A x z)
  let u1 := fun x z => binaryRaw 1 (pasteOn A x z)
  let v0 := fun x z => quinaryRaw 0 (pasteOn A x z)
  let v1 := fun x z => quinaryRaw 1 (pasteOn A x z)
  let M : (A → ZMod 2) → (A → ZMod 2) → ℂ :=
    fun x y => if x = y then 64 else 0
  let N : (A → ZMod 5) → (A → ZMod 5) → ℂ :=
    fun x y => if x = y then 15625 else 0
  have hu : ∀ x y, reduction u0 u0 x y + reduction u1 u1 x y = 2 * M x y := by
    intro x y
    dsimp only [u0, u1, M]
    rw [binary_two_diagonal_blocks A hA x y]
    by_cases h : x = y <;> simp [h] <;> norm_num
  have h0 : ∀ x y, reduction v0 v0 x y = N x y := by
    intro x y
    dsimp only [v0, N]
    rw [quinary_reduction_block A hA]
    by_cases h : x = y <;> simp [h] <;> norm_num
  have h1 : ∀ x y, reduction v1 v1 x y = N x y := by
    intro x y
    dsimp only [v1, N]
    rw [quinary_reduction_block A hA]
    by_cases h : x = y <;> simp [h] <;> norm_num
  have h01 : ∀ x y, reduction v0 v1 x y = 0 := by
    intro x y
    dsimp only [v0, v1]
    rw [quinary_reduction_block A hA]
    rw [if_neg]
    intro h
    exact (by decide : (0 : ZMod 5) ≠ 1) h.1
  have h10 : ∀ x y, reduction v1 v0 x y = 0 := by
    intro x y
    dsimp only [v0, v1]
    rw [quinary_reduction_block A hA]
    rw [if_neg]
    intro h
    exact (by decide : (1 : ZMod 5) ≠ 0) h.1
  have hc := couple_reduction_of_blocks u0 u1 v0 v1 M N hu h0 h1 h01 h10
    (xb, xq) (yb, yq)
  change reduction (couple u0 u1 v0 v1) (couple u0 u1 v0 v1)
    (xb, xq) (yb, yq) = _
  calc
    _ = 2 * ((1 / 2 : ℂ) * reduction (couple u0 u1 v0 v1)
        (couple u0 u1 v0 v1) (xb, xq) (yb, yq)) := by ring
    _ = 2 * (M xb yb * N xq yq) := by rw [hc]
    _ = _ := by
      dsimp only [M, N]
      by_cases hb : xb = yb <;> by_cases hq : xq = yq <;>
        simp [hb, hq] <;> norm_num

theorem raw_reduction (A : Finset (Fin 11)) (hA : A.card = 5)
    (x y : A → Local) :
    reduction (fun x z => rawAmplitude (pasteOn A x z))
      (fun x z => rawAmplitude (pasteOn A x z)) x y =
        if x = y then (2000000 : ℂ) else 0 := by
  have hparts : x = y ↔ bitPart x = bitPart y ∧ quintPart x = quintPart y := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨hb, hq⟩
      funext i
      exact Prod.ext (congrFun hb i) (congrFun hq i)
  unfold reduction
  rw [← (splitFunctionsEquiv {i : Fin 11 // i ∉ A}).symm.sum_comp]
  simp_rw [rawAmplitude_paste_split]
  change reduction
    (couple
      (fun x z => binaryRaw 0 (pasteOn A x z))
      (fun x z => binaryRaw 1 (pasteOn A x z))
      (fun x z => quinaryRaw 0 (pasteOn A x z))
      (fun x z => quinaryRaw 1 (pasteOn A x z)))
    (couple
      (fun x z => binaryRaw 0 (pasteOn A x z))
      (fun x z => binaryRaw 1 (pasteOn A x z))
      (fun x z => quinaryRaw 0 (pasteOn A x z))
      (fun x z => quinaryRaw 1 (pasteOn A x z)))
    (bitPart x, quintPart x) (bitPart y, quintPart y) = _
  rw [coupled_raw_reduction A hA]
  by_cases hxy : x = y
  · simp [hxy]
  · have hp : ¬(bitPart x = bitPart y ∧ quintPart x = quintPart y) :=
      fun h => hxy (hparts.mpr h)
    simp [hxy, hp]

end AMEProbe.CoupledState

#print axioms AMEProbe.CoupledState.raw_reduction
