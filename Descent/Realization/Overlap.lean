import Descent.Models.Square
import Descent.Realization.FiniteGibbs

/-!
# The overlap realization

Strict witnesses for the finite Gibbs laws on the square.

The overlap realization is counting measure on state spaces sharing one
ground state, with `left` and `right` each adding a private state. Like
every realization its partition function is in the gauge, but its state
spaces at the nondegenerate square are not nested, so the sharp vanishing
law puts its log-partition defect strictly above zero: it is exactly
`log (4 / 3)`, the logarithm of the multiplicativity ratio `(2 · 2) / (1 · 3)`.

In the other direction, an explicit field on the square is the log-partition
of no realization over any state carrier: its defect at the nondegenerate
square is negative, and log-partition defects are nonnegative.
-/

namespace Descent

namespace Square

open FiniteGibbs

/-- State spaces of the overlap realization: a shared ground state `0`, one
private state for `left` and one for `right`. -/
def overlapStates : Square → Finset (Fin 3)
  | (false, false) => {0}
  | (true, false) => {0, 1}
  | (false, true) => {0, 2}
  | (true, true) => {0, 1, 2}

/-- The overlap realization on the square: counting measure on
`overlapStates`. -/
noncomputable def overlap : FiniteGibbs Square (Fin 3) :=
  counting overlapStates (by decide) (by decide) (by decide)

private theorem partition_overlap (p : Square) :
    overlap.partition p = ((overlapStates p).card : ℝ) := by
  simp only [overlap, partition_counting]

/-- At the nondegenerate square the partition function of the overlap
realization fails to multiply by the ratio `4 / 3`, and the defect of the
log-partition is exactly its logarithm. -/
theorem defect_logPartition_overlap :
    defect overlap.logPartition left right = Real.log (4 / 3) := by
  rw [overlap.defect_logPartition left right,
    show left ⊓ right = (⊥ : Square) from by decide,
    show left ⊔ right = (⊤ : Square) from by decide,
    partition_overlap, partition_overlap, partition_overlap, partition_overlap,
    show (overlapStates left).card = 2 from by decide,
    show (overlapStates right).card = 2 from by decide,
    show (overlapStates ⊥).card = 1 from by decide,
    show (overlapStates ⊤).card = 3 from by decide]
  norm_num

/-- The universal sign is strict: the overlap realization achieves a
positive defect. -/
theorem defect_logPartition_overlap_pos :
    0 < defect overlap.logPartition left right := by
  rw [defect_logPartition_overlap]
  exact Real.log_pos (by norm_num)

/-- The log-partition of the overlap realization is not a valuation: its
state spaces at the nondegenerate square are not nested. -/
theorem not_isValuation_logPartition_overlap :
    ¬IsValuation overlap.logPartition := fun h =>
  defect_logPartition_overlap_pos.ne' (h left right)

/-- An explicit field on the square that is the log-partition of no
realization over any state carrier: its defect at the nondegenerate square
is negative, and log-partition defects are nonnegative. -/
theorem exists_not_logPartition :
    ∃ K : ContextField Square ℝ,
      ∀ {Ω : Type*} [DecidableEq Ω] (X : FiniteGibbs Square Ω),
        X.logPartition ≠ K := by
  refine ⟨fun p => if p = ⊤ then 1 else 0, fun {Ω} _ X h => ?_⟩
  have h0 := X.defect_logPartition_nonneg left right
  rw [h, defect_left_right] at h0
  norm_num [show left ≠ (⊤ : Square) from by decide,
    show right ≠ (⊤ : Square) from by decide,
    show (⊥ : Square) ≠ (⊤ : Square) from by decide] at h0

end Square

end Descent
