import Mathlib.Algebra.Group.Pi.Basic

/-!
# Context fields

A *context field* attaches a value to each context. The target is additive and
nothing more: no order, no norm, no positivity. Whatever a realization computes
--- a log-partition function, a rank, a dimension, a count --- reaches the
defect calculus only through this interface.

Fields inherit their additive structure pointwise from the target, which is
what makes the defect operator of `Descent.Core.Defect` a homomorphism and its
kernel a subgroup.
-/

namespace Descent

/-- A field on the context system `R` valued in the additive target `A`. -/
abbrev ContextField (R A : Type*) := R → A

variable {R A : Type*}

/-- The field constant at `c`. Every ideal composition law holds for it. -/
def ContextField.const (R : Type*) (c : A) : ContextField R A := fun _ => c

@[simp]
theorem ContextField.const_apply (c : A) (a : R) : ContextField.const R c a = c :=
  rfl

@[simp]
theorem ContextField.const_zero [Zero A] : ContextField.const R (0 : A) = 0 :=
  rfl

end Descent
