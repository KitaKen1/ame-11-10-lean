import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# AME(11,10): a bounded implementation probe

This file proves the finite-sum algebra of the branch construction.
The parent-state hypotheses are explicit; this is NOT an existence proof of AME(11,10).
-/

open scoped BigOperators

namespace AMEProbe

/-- A matrix entry of a reduced cross operator, in amplitude coordinates. -/
noncomputable def reduction {X U : Type*} [Fintype U]
    (u v : X → U → ℂ) (x y : X) : ℂ :=
  ∑ z, u x z * star (v y z)

/-- An unscaled coherent sum of two product branches. -/
noncomputable def couple {X Y U V : Type*}
    (u₀ u₁ : X → U → ℂ) (v₀ v₁ : Y → V → ℂ)
    (x : X × Y) (z : U × V) : ℂ :=
  u₀ x.1 z.1 * v₀ x.2 z.2 + u₁ x.1 z.1 * v₁ x.2 z.2

/-- Partial trace factorizes for a tensor product, including cross terms. -/
theorem reduction_product {X Y U V : Type*} [Fintype U] [Fintype V]
    (u u' : X → U → ℂ) (v v' : Y → V → ℂ) (x y : X × Y) :
    reduction (fun (a : X × Y) (z : U × V) => u a.1 z.1 * v a.2 z.2)
      (fun (a : X × Y) (z : U × V) => u' a.1 z.1 * v' a.2 z.2) x y =
      reduction u u' x.1 y.1 * reduction v v' x.2 y.2 := by
  simp only [reduction, Fintype.sum_prod_type, star_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- Expanding a reduced cross operator is bilinear (conjugate-linear on the right). -/
theorem reduction_add_add {X U : Type*} [Fintype U]
    (a b c d : X → U → ℂ) (x y : X) :
    reduction (fun x z => a x z + b x z) (fun x z => c x z + d x z) x y =
      reduction a c x y + reduction a d x y +
      reduction b c x y + reduction b d x y := by
  simp only [reduction, star_add, add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- The four terms in the branch construction's reduced density matrix. -/
theorem couple_reduction {X Y U V : Type*} [Fintype U] [Fintype V]
    (u₀ u₁ : X → U → ℂ) (v₀ v₁ : Y → V → ℂ) (x y : X × Y) :
    reduction (couple u₀ u₁ v₀ v₁) (couple u₀ u₁ v₀ v₁) x y =
      reduction u₀ u₀ x.1 y.1 * reduction v₀ v₀ x.2 y.2 +
      reduction u₀ u₁ x.1 y.1 * reduction v₀ v₁ x.2 y.2 +
      reduction u₁ u₀ x.1 y.1 * reduction v₁ v₀ x.2 y.2 +
      reduction u₁ u₁ x.1 y.1 * reduction v₁ v₁ x.2 y.2 := by
  unfold couple
  rw [reduction_add_add]
  simp only [reduction_product]

/-- If the quinary cross blocks vanish, only the binary average remains. -/
theorem couple_reduction_of_blocks {X Y U V : Type*} [Fintype U] [Fintype V]
    (u₀ u₁ : X → U → ℂ) (v₀ v₁ : Y → V → ℂ)
    (M : X → X → ℂ) (N : Y → Y → ℂ)
    (hu : ∀ x y, reduction u₀ u₀ x y + reduction u₁ u₁ x y = 2 * M x y)
    (h₀ : ∀ x y, reduction v₀ v₀ x y = N x y)
    (h₁ : ∀ x y, reduction v₁ v₁ x y = N x y)
    (h₀₁ : ∀ x y, reduction v₀ v₁ x y = 0)
    (h₁₀ : ∀ x y, reduction v₁ v₀ x y = 0)
    (x y : X × Y) :
    (1 / 2 : ℂ) * reduction (couple u₀ u₁ v₀ v₁) (couple u₀ u₁ v₀ v₁) x y =
      M x.1 y.1 * N x.2 y.2 := by
  rw [couple_reduction, h₀, h₁, h₀₁, h₁₀]
  simp only [mul_zero, add_zero]
  rw [← add_mul, hu]
  ring

/-- Coordinate reindexing of local 2 × 5 dimensions. -/
def localTenEquiv : Fin 2 × Fin 5 ≃ Fin 10 := finProdFinEquiv

/-- The two maximally mixed scalar factors have the required normalization. -/
theorem mixed_scalar :
    (1 / (2 ^ 5) : ℂ) * (1 / (5 ^ 5)) = 1 / (10 ^ 5) := by
  norm_num

end AMEProbe

#print axioms AMEProbe.reduction_product
#print axioms AMEProbe.couple_reduction_of_blocks
#print axioms AMEProbe.mixed_scalar
