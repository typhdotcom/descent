import Descent.Core.Cube
import Descent.Core.Gauge
import Mathlib.Order.Fin.Basic

/-!
# Chain contexts

On a linearly ordered context system every comparison square is degenerate, so
the pairwise calculus collapses: every field is a valuation, any two fields
are defect-equivalent, and the observable quotient is a point.

Mixed differences do not collapse with it. `exists_defectEquiv_mixedDiff_ne`
exhibits two defect-equivalent fields on the three-element chain whose order-2
mixed differences differ, so the cube hierarchy is not a function of pairwise
defect data: higher mixed differences are new observables, not derived ones.
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

/-- Pairwise defect data does not determine mixed differences: on the
three-element chain the height field and the zero field are defect-equivalent,
yet their order-2 mixed differences differ. The cube hierarchy is a strictly
finer observable than `Observable R A`. -/
theorem exists_defectEquiv_mixedDiff_ne :
    ∃ K K' : ContextField (Fin 3) ℤ, ∃ l : List (Fin 3),
      DefectEquiv K K' ∧ mixedDiff l K ≠ mixedDiff l K' := by
  refine ⟨fun i => ((i : ℕ) : ℤ), 0, [1, 2],
    defectEquiv_of_linearOrder _ _, fun h => ?_⟩
  have h0 := congrFun h 0
  rw [mixedDiff_zero, mixedDiff_pair_apply] at h0
  revert h0
  decide

end Descent
