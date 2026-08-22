import Descent.Core.Cube
import Descent.Core.Gauge
import Mathlib.Order.Fin.Basic

/-!
# Chain contexts

On a linearly ordered context system every comparison square is degenerate, so
the pairwise calculus collapses: every field is a valuation, any two fields
are defect-equivalent, and the observable quotient is a point.

Mixed differences along a raw direction list do not descend through that
collapse. On the three-element chain the height field and the zero field are
defect-equivalent, yet their mixed differences along `[1, 2]` differ. This is
not higher interaction: the `[1, 2]` cube is degenerate --- its directions
are comparable --- so by `mixedDiff_cons_cons_of_le` its order-2 mixed
difference is a signed first-order difference, and first-order differences
see fields the pairwise defect cannot.

The structural content is that the raw hierarchy is not order-separated:
degenerate cubes retain lower-order data. A claim that a higher mixed defect
carries irreducible higher interaction must therefore consume a nondegeneracy
condition on its directions, never a raw list.
-/

namespace Descent

variable {R A : Type*} [LinearOrder R] [AddCommGroup A]

/-- Every field on a chain is a valuation. -/
theorem isValuation_of_linearOrder (K : ContextField R A) : IsValuation K :=
  fun a b => Comparable.defect_eq_zero K (le_total a b)

/-- On a chain the pairwise defect distinguishes nothing. -/
theorem defectEquiv_of_linearOrder (K K' : ContextField R A) : DefectEquiv K K' :=
  (isValuation_iff_defect_eq_zero.mp (isValuation_of_linearOrder K)).trans
    (isValuation_iff_defect_eq_zero.mp (isValuation_of_linearOrder K')).symm

/-- On a chain the observable quotient is a point. -/
instance : Subsingleton (Observable R A) :=
  ⟨fun x y =>
    Quotient.inductionOn₂ x y fun K K' =>
      Observable.mk_eq_mk.mpr (defectEquiv_of_linearOrder K K')⟩

namespace Chain

/-- The height field on the three-element chain. -/
def height : ContextField (Fin 3) ℤ := fun i => ((i : ℕ) : ℤ)

/-- The height field carries no pairwise defect data. -/
theorem defectEquiv_height_zero : DefectEquiv height 0 :=
  defectEquiv_of_linearOrder height 0

/-- The `[1, 2]` cube is degenerate --- its directions are comparable --- so
its order-2 mixed difference is a retained signed first-order difference,
not higher interaction. -/
theorem mixedDiff_height_pair : mixedDiff [1, 2] height = -supDiff 1 height :=
  mixedDiff_cons_cons_of_le (by decide) [] height

/-- Mixed differences along the raw list `[1, 2]` do not descend through the
pairwise gauge: they separate the defect-equivalent fields `height` and `0`,
by the first-order data the degenerate cube retains. -/
theorem mixedDiff_height_ne :
    mixedDiff [1, 2] height ≠ mixedDiff [1, 2] (0 : ContextField (Fin 3) ℤ) := by
  intro h
  have h0 := congrFun h 0
  rw [mixedDiff_zero, mixedDiff_pair_apply] at h0
  revert h0
  decide

end Chain

end Descent
