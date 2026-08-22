import Descent.Core.Context
import Descent.Core.Field
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Order.Hom.Lattice
import Mathlib.Tactic.Abel

/-!
# The pairwise defect

The ideal law is the valuation identity `K a + K b = K (a ⊓ b) + K (a ⊔ b)`.
`defect K a b` is the exact correction term:

    D_K (a, b) = K a + K b - K (a ⊓ b) - K (a ⊔ b)

The sign convention is fixed here once and used mechanically everywhere else.

`defect` is not an error measure. It is the first observable the theory
defines, and the results below say what it can do: it is symmetric, it
annihilates comparable pairs, it is additive in `K`, and it is natural in the
context system.
-/

namespace Descent

variable {R A : Type*} [Lattice R] [AddCommGroup A]

/-- The pairwise defect of `K` on the comparison square spanned by `a` and `b`:
the failure of `K` to satisfy the valuation identity there. -/
def defect (K : ContextField R A) (a b : R) : A :=
  K a + K b - K (a ⊓ b) - K (a ⊔ b)

theorem defect_def (K : ContextField R A) (a b : R) :
    defect K a b = K a + K b - K (a ⊓ b) - K (a ⊔ b) :=
  rfl

/-! ### Algebra in the context arguments -/

theorem defect_comm (K : ContextField R A) (a b : R) : defect K a b = defect K b a := by
  simp only [defect, inf_comm a b, sup_comm a b]
  abel

@[simp]
theorem defect_self (K : ContextField R A) (a : R) : defect K a a = 0 := by
  simp only [defect, inf_idem, sup_idem]
  abel

/-- The defect vanishes on a degenerate comparison square. -/
theorem defect_of_le (K : ContextField R A) {a b : R} (h : a ≤ b) : defect K a b = 0 := by
  simp only [defect, inf_of_le_left h, sup_of_le_right h]
  abel

theorem defect_of_ge (K : ContextField R A) {a b : R} (h : b ≤ a) : defect K a b = 0 := by
  rw [defect_comm]
  exact defect_of_le K h

theorem Comparable.defect_eq_zero (K : ContextField R A) {a b : R} (h : Comparable a b) :
    defect K a b = 0 := by
  rcases h with h | h
  · exact defect_of_le K h
  · exact defect_of_ge K h

/-! ### Algebra in the field -/

@[simp]
theorem defect_zero : defect (0 : ContextField R A) = 0 := by
  funext a b
  simp [defect]

@[simp]
theorem defect_const (c : A) : defect (ContextField.const R c) = 0 := by
  funext a b
  simp only [defect, ContextField.const_apply, Pi.zero_apply]
  abel

theorem defect_add (K K' : ContextField R A) (a b : R) :
    defect (K + K') a b = defect K a b + defect K' a b := by
  simp only [defect, Pi.add_apply]
  abel

theorem defect_neg (K : ContextField R A) (a b : R) :
    defect (-K) a b = -defect K a b := by
  simp only [defect, Pi.neg_apply]
  abel

theorem defect_sub (K K' : ContextField R A) (a b : R) :
    defect (K - K') a b = defect K a b - defect K' a b := by
  simp only [defect, Pi.sub_apply]
  abel

theorem defect_smul {S : Type*} [Monoid S] [DistribMulAction S A]
    (s : S) (K : ContextField R A) (a b : R) :
    defect (s • K) a b = s • defect K a b := by
  simp only [defect, Pi.smul_apply, smul_sub, smul_add]

/-- The defect operator, packaged as an additive homomorphism. Its kernel is
the gauge freedom of `Descent.Core.Gauge`. -/
def defectHom : ContextField R A →+ (R → R → A) where
  toFun := defect
  map_zero' := defect_zero
  map_add' K K' := by
    funext a b
    exact defect_add K K' a b

@[simp]
theorem defectHom_apply (K : ContextField R A) : defectHom K = defect K :=
  rfl

/-! ### Naturality -/

/-- Pulling contexts back along a lattice homomorphism pulls the defect back
with them. The defect is a property of the square, not of its labelling. -/
theorem defect_comp {R' : Type*} [Lattice R'] (f : LatticeHom R R')
    (K : ContextField R' A) (a b : R) :
    defect (K ∘ f) a b = defect K (f a) (f b) := by
  simp [defect, Function.comp_apply, map_inf, map_sup]

end Descent
