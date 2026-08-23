import Descent.Core.Cube
import Descent.Core.Gauge
import Descent.Core.Higher
import Descent.Reconstruction.Normalization
import Descent.Reconstruction.Restricted
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

/-- On a chain the order-3 defect vanishes identically: unlike the raw
mixed difference, it retains no lower-order data on degenerate cubes. -/
theorem defect3_eq_zero_of_linearOrder (K : ContextField R A) (a b c : R) :
    defect3 K a b c = 0 := by
  rcases le_total a b with h | h
  · rw [defect3_of_le K h c]
    exact isValuation_of_linearOrder K b c
  · rw [defect3_comm_left, defect3_of_le K h c]
    exact isValuation_of_linearOrder K a c

/-- On a chain the order-4 defect vanishes identically as well. -/
theorem defect4_eq_zero_of_linearOrder (K : ContextField R A) (a b c d : R) :
    defect4 K a b c d = 0 :=
  defect4_eq_zero_of_defect3_eq_zero (defect3_eq_zero_of_linearOrder K)
    (Or.inl (le_total a b))

/-- On a chain the gauge is everything. -/
theorem gauge_eq_top_of_linearOrder : gauge R A = ⊤ :=
  eq_top_iff.mpr fun K _ => mem_gauge_iff.mpr (isValuation_of_linearOrder K)

/-- On a chain every family of comparison squares --- including `∅` --- is
observationally complete: completeness is relative to the gauge, and the
chain gauge forgets everything. -/
theorem observationallyComplete_of_linearOrder (S : Set (R × R)) :
    ObservationallyComplete S A := by
  rw [ObservationallyComplete, gauge_eq_top_of_linearOrder, eq_top_iff]
  exact fun K _ => mem_gaugeOn_iff.mpr fun p _ =>
    isValuation_of_linearOrder K p.1 p.2

/-- On a chain no proper value restriction is adequate: the class carries no
information, so normalization must supply the whole field. -/
theorem adequateOn_iff_of_linearOrder [Nontrivial A] {T : Set R} :
    AdequateOn T A ↔ T = Set.univ := by
  constructor
  · intro h
    by_contra hT
    obtain ⟨t, ht⟩ := (Set.ne_univ_iff_exists_notMem T).mp hT
    obtain ⟨e, he⟩ := exists_ne (0 : A)
    classical
    refine he ?_
    have h0 := adequateOn_iff_eq_zero.mp h (Pi.single t e)
      (isValuation_of_linearOrder _) ?_
    · simpa using congrFun h0 t
    · funext s
      have hne : s.val ≠ t := fun hst => ht (hst ▸ s.property)
      show (Pi.single t e : ContextField R A) s.val = 0
      exact Pi.single_eq_of_ne (M := fun _ => A) hne e
  · rintro rfl
    exact adequateOn_univ

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

/-- The order-3 defect does not repeat the failure: it identifies the
defect-equivalent fields the raw mixed difference separates. -/
theorem defect3_height_eq :
    defect3 height = defect3 (0 : ContextField (Fin 3) ℤ) :=
  funext fun a => funext fun b => funext fun c => by
    rw [defect3_eq_zero_of_linearOrder, defect3_eq_zero_of_linearOrder]

end Chain

end Descent
