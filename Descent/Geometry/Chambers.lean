import Descent.Models.Square
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Sign chambers of the defect

The defect of a field has no universal sign. The two sign conditions are
named by their literal mathematical content --- submodularity and
supermodularity --- and they cut the space of fields into chambers:

* each chamber is a convex cone, and negation exchanges them;
* the chamber wall is exact: the chambers meet precisely in the gauge
  (`submodular_and_supermodular_iff`);
* on the square the chamber map is one coordinate --- the single defect
  value --- so the two chambers cover every field
  (`Square.submodular_or_supermodular`);
* on a product of the square with a chain they do not: an explicit field
  has defects of both signs (`exists_not_submodular_not_supermodular`).
  No universal sign may be assumed.
-/

namespace Descent

variable {R A : Type*} [Lattice R] [AddCommGroup A] [PartialOrder A]

/-- A field is submodular when its defect is nonnegative on every
comparison square. -/
def Submodular (K : ContextField R A) : Prop :=
  ∀ a b, 0 ≤ defect K a b

/-- A field is supermodular when its defect is nonpositive on every
comparison square. -/
def Supermodular (K : ContextField R A) : Prop :=
  ∀ a b, defect K a b ≤ 0

/-- Negation exchanges the chambers. -/
theorem submodular_neg_iff [AddLeftMono A] {K : ContextField R A} :
    Submodular (-K) ↔ Supermodular K :=
  forall₂_congr fun a b => by rw [defect_neg, neg_nonneg]

theorem supermodular_neg_iff [AddLeftMono A] {K : ContextField R A} :
    Supermodular (-K) ↔ Submodular K :=
  forall₂_congr fun a b => by rw [defect_neg, neg_nonpos]

/-- The chamber wall is exact: the sign chambers meet precisely in the
gauge. -/
theorem submodular_and_supermodular_iff {K : ContextField R A} :
    Submodular K ∧ Supermodular K ↔ IsValuation K := by
  constructor
  · rintro ⟨hs, hS⟩ a b
    exact le_antisymm (hS a b) (hs a b)
  · exact fun h => ⟨fun a b => (h a b).ge, fun a b => (h a b).le⟩

/-- The submodular chamber is closed under addition. -/
theorem Submodular.add [IsOrderedAddMonoid A] {K K' : ContextField R A}
    (h : Submodular K) (h' : Submodular K') : Submodular (K + K') := fun a b => by
  rw [defect_add]
  exact add_nonneg (h a b) (h' a b)

theorem Supermodular.add [IsOrderedAddMonoid A] {K K' : ContextField R A}
    (h : Supermodular K) (h' : Supermodular K') : Supermodular (K + K') := fun a b => by
  rw [defect_add]
  exact add_nonpos (h a b) (h' a b)

/-- The submodular chamber is a cone. -/
theorem Submodular.smul {K : ContextField R ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : Submodular K) : Submodular (c • K) := fun a b => by
  rw [defect_smul, smul_eq_mul]
  exact mul_nonneg hc (h a b)

theorem Supermodular.smul {K : ContextField R ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : Supermodular K) : Supermodular (c • K) := fun a b => by
  rw [defect_smul, smul_eq_mul]
  nlinarith [h a b, hc]

namespace Square

variable {K : ContextField Square A}

/-- On the square the chamber map is one coordinate: submodularity is the
sign of the single defect value. -/
theorem submodular_iff : Submodular K ↔ 0 ≤ defect K left right := by
  constructor
  · exact fun h => h left right
  · intro hd a b
    rw [defect_eq_defectData K]
    show 0 ≤ defectData _ a b
    unfold defectData
    split
    · exact hd
    · exact le_rfl

theorem supermodular_iff : Supermodular K ↔ defect K left right ≤ 0 := by
  constructor
  · exact fun h => h left right
  · intro hd a b
    rw [defect_eq_defectData K]
    show defectData _ a b ≤ 0
    unfold defectData
    split
    · exact hd
    · exact le_rfl

/-- On the square the two chambers cover every field. -/
theorem submodular_or_supermodular {A : Type*} [AddCommGroup A] [LinearOrder A]
    (K : ContextField Square A) : Submodular K ∨ Supermodular K :=
  (le_total 0 (defect K left right)).imp submodular_iff.mpr supermodular_iff.mpr

end Square

/-- No universal sign: on the product of the square with a chain, an
explicit field has defects of both signs, so the chambers do not cover
richer context systems. -/
theorem exists_not_submodular_not_supermodular :
    ∃ K : ContextField (Bool × Square) ℝ, ¬Submodular K ∧ ¬Supermodular K := by
  classical
  refine ⟨Pi.single (true, (⊥ : Square)) 1, fun h => ?_, fun h => ?_⟩
  · have h2 := h (true, Square.left) (true, Square.right)
    rw [defect_def,
      show ((true, Square.left) ⊓ (true, Square.right) : Bool × Square)
        = (true, ⊥) from by decide,
      show ((true, Square.left) ⊔ (true, Square.right) : Bool × Square)
        = (true, ⊤) from by decide] at h2
    norm_num [Pi.single_apply,
      show ((true, Square.left) : Bool × Square) ≠ (true, ⊥) from by decide,
      show ((true, Square.right) : Bool × Square) ≠ (true, ⊥) from by decide,
      show ((true, ⊤) : Bool × Square) ≠ (true, ⊥) from by decide] at h2
  · have h2 := h (true, (⊥ : Square)) (false, Square.left)
    rw [defect_def,
      show ((true, (⊥ : Square)) ⊓ (false, Square.left) : Bool × Square)
        = (false, ⊥) from by decide,
      show ((true, (⊥ : Square)) ⊔ (false, Square.left) : Bool × Square)
        = (true, Square.left) from by decide] at h2
    norm_num [Pi.single_apply,
      show ((false, Square.left) : Bool × Square) ≠ (true, ⊥) from by decide,
      show ((false, (⊥ : Square)) : Bool × Square) ≠ (true, ⊥) from by decide,
      show ((true, Square.left) : Bool × Square) ≠ (true, ⊥) from by decide] at h2

end Descent
