import Descent.Core.Higher
import Mathlib.Data.Fintype.Pi

/-!
# The diamond

`M₃`: bottom, three incomparable atoms, top. The smallest modular
non-distributive lattice, and the sharpness witness for order separation:
the height field is a pairwise valuation --- its defect observable
vanishes identically, so it is defect-equivalent to zero --- yet its
order-3 defect at the atom triple is `1`. Off distributivity the order-3
defect does not descend through the pairwise gauge, and third-order
information is genuinely new: the surviving equivalence is joint
pairwise-and-triple defect equality, not pairwise alone.
-/

namespace Descent

/-- The five-element modular non-distributive lattice `M₃`. -/
inductive Diamond : Type
  | bot | x | y | z | top
deriving DecidableEq

namespace Diamond

instance : Fintype Diamond :=
  ⟨{bot, x, y, z, top}, fun a => by cases a <;> decide⟩

/-- Meet: distinct middle elements meet at the bottom. -/
def infD : Diamond → Diamond → Diamond
  | bot, _ => bot
  | _, bot => bot
  | top, q => q
  | p, top => p
  | p, q => if p = q then p else bot

/-- Join: distinct middle elements join at the top. -/
def supD : Diamond → Diamond → Diamond
  | top, _ => top
  | _, top => top
  | bot, q => q
  | p, bot => p
  | p, q => if p = q then p else top

instance : Lattice Diamond where
  le p q := infD p q = p
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  inf := infD
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  sup := supD
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : DecidableLE Diamond := fun p q =>
  inferInstanceAs (Decidable (infD p q = p))

/-- The atom triple is nondegenerate: pairwise incomparable. -/
theorem not_comparable_x_y : ¬Comparable x y := by decide

theorem not_comparable_x_z : ¬Comparable x z := by decide

theorem not_comparable_y_z : ¬Comparable y z := by decide

/-- The height field on the diamond. -/
def height : ContextField Diamond ℤ
  | bot => 0
  | top => 2
  | _ => 1

/-- The height field is a pairwise valuation: its defect observable
vanishes identically. -/
theorem isValuation_height : IsValuation height := by
  show ∀ a b : Diamond, defect height a b = 0
  decide

/-- The diamond is not distributive, and the order-3 defect knows: the
height field is a pairwise valuation with order-3 defect `1` at the atom
triple. -/
theorem defect3_height : defect3 height x y z = 1 := by decide

/-- The height field is defect-equivalent to zero. -/
theorem defectEquiv_height_zero :
    DefectEquiv height (0 : ContextField Diamond ℤ) := by
  show defect height = defect (0 : ContextField Diamond ℤ)
  decide

/-- Off distributivity the order-3 defect does not descend through the
pairwise gauge: two defect-equivalent fields with different order-3
defects. -/
theorem exists_defectEquiv_defect3_ne :
    ∃ K K' : ContextField Diamond ℤ,
      DefectEquiv K K' ∧ defect3 K ≠ defect3 K' := by
  refine ⟨height, 0, defectEquiv_height_zero, ?_⟩
  intro h
  have h0 := congrFun (congrFun (congrFun h x) y) z
  rw [defect3_height] at h0
  simp [defect3_zero] at h0

/-- On the diamond the order-≤3 gauge is strictly below the pairwise
gauge: the height valuation is invisible to pairwise observation and
visible to cumulative observation. -/
theorem gauge3_lt_gauge : gauge3 Diamond ℤ < gauge Diamond ℤ := by
  rw [SetLike.lt_iff_le_and_exists]
  refine ⟨inf_le_left, height, mem_gauge_iff.mpr isValuation_height, fun h => ?_⟩
  have h3 := (mem_gauge3_iff.mp h).2 x y z
  rw [defect3_height] at h3
  exact one_ne_zero h3

/-- Observation through order 3 is strictly finer on the diamond: the
height field and zero share the pairwise observable. -/
theorem observable_mk_height_eq :
    Observable.mk height = Observable.mk (0 : ContextField Diamond ℤ) :=
  Observable.mk_eq_mk.mpr defectEquiv_height_zero

/-- ... and the cumulative observable separates them. -/
theorem observable3_mk_height_ne :
    Observable3.mk height ≠ Observable3.mk (0 : ContextField Diamond ℤ) := by
  rw [Ne, Observable3.mk_eq_mk]
  rintro ⟨-, h3⟩
  have h0 := congrFun (congrFun (congrFun h3 x) y) z
  rw [defect3_height] at h0
  simp [defect3_zero] at h0

/-- The diamond has no 4-antichain: every quadruple contains a comparable
pair. -/
theorem four_comparable :
    ∀ a b c d : Diamond,
      Comparable a b ∨ Comparable a c ∨ Comparable a d ∨ Comparable b c ∨
        Comparable b d ∨ Comparable c d := by
  decide

/-- The diamond stabilizes at order 3: with no 4-antichain, the order-≤4
gauge is the order-≤3 gauge. -/
theorem gauge4_eq_gauge3 : gauge4 Diamond ℤ = gauge3 Diamond ℤ := by
  refine le_antisymm inf_le_left fun K hK => ?_
  rw [gauge4, AddSubgroup.mem_inf]
  refine ⟨hK, ?_⟩
  rw [AddMonoidHom.mem_ker]
  funext a b c d
  exact defect4_eq_zero_of_defect3_eq_zero (mem_gauge3_iff.mp hK).2
    (four_comparable a b c d)

end Diamond

end Descent
