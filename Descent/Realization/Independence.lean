import Descent.Models.Chain
import Descent.Models.Square
import Descent.Realization.FiniteGibbs

/-!
# Independence and correlation on the square

Product realizations over chain factors have valuation log-partition: the
defect observable of an independent juxtaposition vanishes identically
(`isValuation_logPartition_prod_of_linearOrder`). The square `Bool × Bool` is
such a product of chains, so any product realization on it is invisible to
the pairwise defect.

The overlap realization is the strict witness on the other side: counting
measure on nested state spaces sharing one ground state. Its partition
function is a valuation --- the state map turns meet and join into
intersection and union, so the additive reading is exact --- but its
log-partition has defect `log (4 / 3)` at the nondegenerate square: the
partition function does not multiply across it. The defect of the
log-partition observes exactly this multiplicativity failure, and it
separates the overlap realization from every product realization over the
square's chain factors (`not_defectEquiv_logPartition_overlap_prod`).
-/

namespace Descent

namespace FiniteGibbs

/-- Over chain factors every product realization has valuation log-partition:
independent systems produce zero defect. -/
theorem isValuation_logPartition_prod_of_linearOrder
    {R S Ω Ψ : Type*} [LinearOrder R] [LinearOrder S]
    (X : FiniteGibbs R Ω) (Y : FiniteGibbs S Ψ) :
    IsValuation (X.prod Y).logPartition :=
  X.isValuation_logPartition_prod Y (isValuation_of_linearOrder _)
    (isValuation_of_linearOrder _)

end FiniteGibbs

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
def overlap : FiniteGibbs Square (Fin 3) :=
  counting overlapStates (by decide)

private theorem partition_overlap (p : Square) :
    overlap.partition p = ((overlapStates p).card : ℝ) := by
  simp only [overlap, partition_counting]

/-- The overlap state map turns meet and join into intersection and union,
so the partition function of the overlap realization is a valuation: the
additive reading is exact. -/
theorem isValuation_partition_overlap : IsValuation overlap.partition :=
  overlap.isValuation_partition (by decide) (by decide)

theorem partition_overlap_mem_gauge : overlap.partition ∈ gauge Square ℝ :=
  mem_gauge_iff.mpr isValuation_partition_overlap

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

/-- The log-partition of the overlap realization is not a valuation: the
same realization whose additive reading is exact has a correlated
logarithmic reading. -/
theorem not_isValuation_logPartition_overlap :
    ¬IsValuation overlap.logPartition := by
  intro h
  have h0 := h left right
  rw [defect_logPartition_overlap] at h0
  exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num) h0

/-- The overlap realization is not defect-equivalent to any product
realization over the square's chain factors: its correlation is visible in
the pairwise defect alone. -/
theorem not_defectEquiv_logPartition_overlap_prod
    {Ω' Ψ' : Type*} (X : FiniteGibbs Bool Ω') (Y : FiniteGibbs Bool Ψ') :
    ¬DefectEquiv overlap.logPartition (X.prod Y).logPartition := by
  intro h
  have h0 : defect overlap.logPartition left right = 0 := by
    rw [congrFun (congrFun
      (h : Descent.defect overlap.logPartition = Descent.defect (X.prod Y).logPartition)
      left) right]
    exact isValuation_logPartition_prod_of_linearOrder X Y left right
  rw [defect_logPartition_overlap] at h0
  exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num) h0

end Square

end Descent
