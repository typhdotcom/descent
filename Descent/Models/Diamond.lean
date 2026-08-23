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

/-- Off distributivity the order-3 defect does not descend through the
pairwise gauge: two defect-equivalent fields with different order-3
defects. -/
theorem exists_defectEquiv_defect3_ne :
    ∃ K K' : ContextField Diamond ℤ,
      DefectEquiv K K' ∧ defect3 K ≠ defect3 K' := by
  refine ⟨height, 0, ?_, ?_⟩
  · show defect height = defect (0 : ContextField Diamond ℤ)
    decide
  · intro h
    have h0 := congrFun (congrFun (congrFun h x) y) z
    rw [defect3_height] at h0
    simp [defect3_zero] at h0

end Diamond

end Descent
