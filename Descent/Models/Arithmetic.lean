import Descent.Geometry.Kernels
import Descent.Realization.Realizable
import Mathlib.Data.PNat.Prime
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The arithmetic carrier

Positive naturals ordered by divisibility: meet is `gcd`, join is `lcm`,
and the divisor sets are the natural state system. The carrier earns its
place with theorems the abstract level cannot see:

* the divisor system is exact on the meet side --- divisors of the gcd are
  the shared divisors --- while the join side fails by a measured
  arithmetic amount: the lcm itself witnesses `divisors (lcm) ⊋ union`
  exactly off comparability;
* hence the divisor-count field is supermodular with the chamber wall hit
  exactly at comparability, and the canonical M6 metric of its chamber is
  the divisor symmetric-difference distance;
* multiplicatively the same field is exact --- `d(gcd)·d(lcm) = d·d` ---
  so its logarithm is a monotone valuation, a field in the gauge. Its
  exponential, the divisor count, is not an additive valuation, so M5's
  algebraic compatibility obstruction applies concretely: the log divisor
  count is the log-partition of no realization over any state carrier,
  exposed by exact factorization on the divisor counts of `4`, `6`, and
  their gcd. The new feature is that the offending field carries
  identically vanishing defect data: it is defect-equivalent to the zero
  field, which is realizable. No defect-only observation decides
  realizability.
-/

namespace Descent

/-- The arithmetic context system: positive naturals under divisibility. -/
def Arith : Type := ℕ+

namespace Arith

/-- Interpret a positive natural as an arithmetic context. -/
def of (n : ℕ+) : Arith := n

/-- The positive natural carried by an arithmetic context. -/
def num (a : Arith) : ℕ+ := a

instance : DecidableEq Arith := fun a b =>
  inferInstanceAs (Decidable (num a = num b))

instance : Lattice Arith where
  le a b := num a ∣ num b
  le_refl a := dvd_refl (num a)
  le_trans _ _ _ hab hbc := hab.trans hbc
  le_antisymm _ _ hab hba := PNat.dvd_antisymm hab hba
  inf a b := of ((num a).gcd (num b))
  inf_le_left a b := PNat.gcd_dvd_left (num a) (num b)
  inf_le_right a b := PNat.gcd_dvd_right (num a) (num b)
  le_inf _ _ _ hab hac := PNat.dvd_gcd hab hac
  sup a b := of ((num a).lcm (num b))
  le_sup_left a b := PNat.dvd_lcm_left (num a) (num b)
  le_sup_right a b := PNat.dvd_lcm_right (num a) (num b)
  sup_le _ _ _ hac hbc := PNat.lcm_dvd hac hbc

theorem le_iff_dvd {a b : Arith} : a ≤ b ↔ (num a : ℕ) ∣ (num b : ℕ) :=
  PNat.dvd_iff

theorem num_inf (a b : Arith) : (num (a ⊓ b) : ℕ) = (num a : ℕ).gcd (num b : ℕ) :=
  PNat.gcd_coe _ _

theorem num_sup (a b : Arith) : (num (a ⊔ b) : ℕ) = (num a : ℕ).lcm (num b : ℕ) :=
  PNat.lcm_coe _ _

theorem num_ne_zero (a : Arith) : (num a : ℕ) ≠ 0 :=
  PNat.ne_zero (num a)

/-! ### The divisor system -/

/-- The divisor system: the finite set of divisors of a context. -/
def divisorSet (a : Arith) : Finset ℕ :=
  (num a : ℕ).divisors

theorem mem_divisorSet {x : ℕ} {a : Arith} :
    x ∈ divisorSet a ↔ x ∣ (num a : ℕ) := by
  rw [divisorSet, Nat.mem_divisors, and_iff_left (num_ne_zero a)]

theorem divisorSet_nonempty (a : Arith) : (divisorSet a).Nonempty :=
  ⟨1, mem_divisorSet.mpr (one_dvd _)⟩

/-- The meet side of the divisor system is exact: divisors of the gcd are
the shared divisors. -/
theorem divisorSet_inf (a b : Arith) :
    divisorSet (a ⊓ b) = divisorSet a ∩ divisorSet b := by
  ext x
  simp only [Finset.mem_inter, mem_divisorSet, num_inf, Nat.dvd_gcd_iff]

theorem divisorSet_mono {a b : Arith} (h : a ≤ b) :
    divisorSet a ⊆ divisorSet b :=
  Nat.divisors_subset_of_dvd (num_ne_zero b) (le_iff_dvd.mp h)

/-- The join side is one-sided: the union of the divisor sets sits inside
the divisors of the lcm. -/
theorem divisorSet_union_subset (a b : Arith) :
    divisorSet a ∪ divisorSet b ⊆ divisorSet (a ⊔ b) :=
  Finset.union_subset (divisorSet_mono le_sup_left) (divisorSet_mono le_sup_right)

/-- Off comparability the join side fails, and the lcm itself is the
witness: it divides neither factor. -/
theorem num_sup_notMem {a b : Arith} (h : ¬Comparable a b) :
    ((num (a ⊔ b) : ℕ)) ∉ divisorSet a ∪ divisorSet b := by
  intro hmem
  rcases Finset.mem_union.mp hmem with hx | hx
  · refine h (Or.inr ?_)
    have hle : a ≤ a ⊔ b := le_sup_left
    have heq : a ⊔ b = a :=
      PNat.coe_injective (Nat.dvd_antisymm (mem_divisorSet.mp hx) (le_iff_dvd.mp hle))
    rw [← heq]
    exact le_sup_right
  · refine h (Or.inl ?_)
    have hle : b ≤ a ⊔ b := le_sup_right
    have heq : a ⊔ b = b :=
      PNat.coe_injective (Nat.dvd_antisymm (mem_divisorSet.mp hx) (le_iff_dvd.mp hle))
    rw [← heq]
    exact le_sup_left

theorem divisorSet_sup_ssubset {a b : Arith} (h : ¬Comparable a b) :
    divisorSet a ∪ divisorSet b ⊂ divisorSet (a ⊔ b) :=
  (Finset.ssubset_iff_of_subset (divisorSet_union_subset a b)).mpr
    ⟨num (a ⊔ b), mem_divisorSet.mpr dvd_rfl, num_sup_notMem h⟩

/-! ### The divisor-count field: the additive reading -/

/-- The divisor-count field. -/
noncomputable def divisorCount : ContextField Arith ℝ := fun a =>
  ((divisorSet a).card : ℝ)

theorem divisorCount_pos (a : Arith) : 0 < divisorCount a := by
  simp only [divisorCount]
  exact_mod_cast Finset.card_pos.mpr (divisorSet_nonempty a)

theorem monotone_divisorCount : Monotone divisorCount := fun _ _ h =>
  Nat.cast_le.mpr (Finset.card_le_card (divisorSet_mono h))

/-- The defect of the divisor count is the failure of the join side of the
divisor system, with its arithmetic sign. -/
theorem defect_divisorCount (a b : Arith) :
    defect divisorCount a b
      = ((divisorSet a ∪ divisorSet b).card : ℝ) - ((divisorSet (a ⊔ b)).card : ℝ) := by
  have h := congrArg (Nat.cast : ℕ → ℝ)
    (Finset.card_union_add_card_inter (divisorSet a) (divisorSet b))
  push_cast at h
  rw [defect_def]
  simp only [divisorCount, divisorSet_inf]
  linarith

/-- The divisor count lies in the supermodular chamber. -/
theorem supermodular_divisorCount : Supermodular divisorCount := fun a b => by
  rw [defect_divisorCount]
  have h := Nat.cast_le (α := ℝ).mpr
    (Finset.card_le_card (divisorSet_union_subset a b))
  linarith

/-- The chamber wall is hit exactly at comparability. -/
theorem defect_divisorCount_eq_zero_iff {a b : Arith} :
    defect divisorCount a b = 0 ↔ Comparable a b := by
  constructor
  · intro h
    by_contra hc
    have hlt := Nat.cast_lt (α := ℝ).mpr
      (Finset.card_lt_card (divisorSet_sup_ssubset hc))
    rw [defect_divisorCount] at h
    linarith
  · exact fun h => h.defect_eq_zero divisorCount

/-- Strict supermodularity off comparability. -/
theorem defect_divisorCount_neg_iff {a b : Arith} :
    defect divisorCount a b < 0 ↔ ¬Comparable a b := by
  constructor
  · intro hlt hc
    rw [hc.defect_eq_zero divisorCount] at hlt
    exact lt_irrefl 0 hlt
  · intro hc
    rcases lt_or_eq_of_le (supermodular_divisorCount a b) with h | h
    · exact h
    · exact absurd (defect_divisorCount_eq_zero_iff.mp h) hc

/-! ### The divisor metric -/

open scoped symmDiff in
/-- The M6 kernel of the supermodular chamber is the divisor
symmetric-difference distance. -/
theorem meetKernel_divisorCount (a b : Arith) :
    meetKernel divisorCount a b = ((divisorSet a ∆ divisorSet b).card : ℝ) := by
  have hsplit : (divisorSet a ∆ divisorSet b).card
      = (divisorSet a \ divisorSet b).card + (divisorSet b \ divisorSet a).card := by
    rw [symmDiff_def, Finset.sup_eq_union]
    exact Finset.card_union_of_disjoint disjoint_sdiff_sdiff
  have ha := congrArg (Nat.cast : ℕ → ℝ)
    (Finset.card_sdiff_add_card_inter (divisorSet a) (divisorSet b))
  have hb := congrArg (Nat.cast : ℕ → ℝ)
    (Finset.card_sdiff_add_card_inter (divisorSet b) (divisorSet a))
  rw [Finset.inter_comm] at hb
  push_cast at ha hb
  rw [hsplit]
  simp only [meetKernel, divisorCount, divisorSet_inf]
  push_cast
  linarith

/-- Divisor sets separate contexts: a positive natural is the largest of
its divisors. -/
theorem divisorSet_injective : Function.Injective divisorSet := by
  intro a b h
  have hab : (num a : ℕ) ∣ (num b : ℕ) :=
    mem_divisorSet.mp (h ▸ mem_divisorSet.mpr (dvd_refl _))
  have hba : (num b : ℕ) ∣ (num a : ℕ) :=
    mem_divisorSet.mp (h.symm ▸ mem_divisorSet.mpr (dvd_refl _))
  exact PNat.coe_injective (Nat.dvd_antisymm hab hba)

/-- Separation: zero symmetric-difference distance forces equal
contexts. -/
theorem eq_of_meetKernel_divisorCount_eq_zero {a b : Arith}
    (h : meetKernel divisorCount a b = 0) : a = b := by
  rw [meetKernel_divisorCount] at h
  have hcard : (symmDiff (divisorSet a) (divisorSet b)).card = 0 := by
    exact_mod_cast h
  have hbot := Finset.card_eq_zero.mp hcard
  rw [← Finset.bot_eq_empty] at hbot
  exact divisorSet_injective (symmDiff_eq_bot.mp hbot)

/-- The divisibility lattice carries the divisor metric: the chamber
machinery instantiated on the arithmetic carrier, promoted to a genuine
metric by separation. -/
@[instance_reducible]
noncomputable def divisorMetric : MetricSpace Arith where
  toPseudoMetricSpace := supermodular_divisorCount.pseudoMetricSpace monotone_divisorCount
  eq_of_dist_eq_zero := fun {_ _} h => eq_of_meetKernel_divisorCount_eq_zero h

theorem dist_divisorMetric :
    divisorMetric.toPseudoMetricSpace.toDist.dist = meetKernel divisorCount :=
  rfl

/-! ### The multiplicative reading: exactness, gauge, and the invisible
obstruction -/

/-- Multiplicative exactness: divisor counts factor exactly through
gcd and lcm. -/
theorem divisorCount_inf_mul_sup (a b : Arith) :
    divisorCount (a ⊓ b) * divisorCount (a ⊔ b) = divisorCount a * divisorCount b := by
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 0)).lcm_apply_mul_gcd_apply
    (x := (num a : ℕ)) (y := (num b : ℕ))
  simp only [ArithmeticFunction.sigma_zero_apply] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  simp only [divisorCount, divisorSet, num_inf, num_sup]
  linarith [h']

/-- The logarithmic divisor-count field. -/
noncomputable def logDivisorCount : ContextField Arith ℝ := fun a =>
  Real.log (divisorCount a)

theorem monotone_logDivisorCount : Monotone logDivisorCount := fun a _ h =>
  Real.log_le_log (divisorCount_pos a) (monotone_divisorCount h)

/-- The log divisor count is a valuation: its defect observable vanishes
identically. -/
theorem isValuation_logDivisorCount : IsValuation logDivisorCount := by
  intro a b
  have hm := divisorCount_inf_mul_sup a b
  have h1 : Real.log (divisorCount (a ⊓ b)) + Real.log (divisorCount (a ⊔ b))
      = Real.log (divisorCount a) + Real.log (divisorCount b) := by
    rw [← Real.log_mul (divisorCount_pos _).ne' (divisorCount_pos _).ne',
      ← Real.log_mul (divisorCount_pos _).ne' (divisorCount_pos _).ne', hm]
  rw [defect_def]
  simp only [logDivisorCount]
  linarith

theorem logDivisorCount_mem_gauge : logDivisorCount ∈ gauge Arith ℝ :=
  mem_gauge_iff.mpr isValuation_logDivisorCount

/-- The obstruction no defect datum can certify: the log divisor count is
a monotone valuation --- gauge, defect-invisible --- yet it is the
log-partition of no finite Gibbs realization over any state carrier.
Exact factorization forces the degenerate alternative, and the divisor
counts of `4`, `6`, and their gcd `2` refuse it. -/
theorem not_logPartition_logDivisorCount {Ω : Type*} [DecidableEq Ω]
    (X : FiniteGibbs Arith Ω) : X.logPartition ≠ logDivisorCount := by
  intro h
  have h0 : defect X.logPartition (of 4) (of 6) = 0 := by
    rw [h]
    exact isValuation_logDivisorCount (of 4) (of 6)
  have hp := X.partition_inf_eq_of_defect_eq_zero h0
  have hval : ∀ r : Arith, X.partition r = divisorCount r := fun r => by
    rw [← X.exp_logPartition r, congrFun h r]
    exact Real.exp_log (divisorCount_pos r)
  rw [hval, hval, hval, show of 4 ⊓ of 6 = of 2 from by decide] at hp
  have h2 : divisorCount (of 2) = 2 := by
    simp only [divisorCount]
    norm_num [show (divisorSet (of 2)).card = 2 from by decide]
  have h4 : divisorCount (of 4) = 3 := by
    simp only [divisorCount]
    norm_num [show (divisorSet (of 4)).card = 3 from by decide]
  have h6 : divisorCount (of 6) = 4 := by
    simp only [divisorCount]
    norm_num [show (divisorSet (of 6)).card = 4 from by decide]
  rw [h2, h4, h6] at hp
  rcases hp with hp | hp <;> norm_num at hp

/-- The log divisor count is not realizable. -/
theorem not_realizable_logDivisorCount : ¬Realizable logDivisorCount := by
  rintro ⟨Ω, _, X, hX⟩
  exact not_logPartition_logDivisorCount X hX

/-- The log divisor count carries the same defect data as the zero
field. -/
theorem defectEquiv_zero_logDivisorCount :
    DefectEquiv (0 : ContextField Arith ℝ) logDivisorCount := by
  show defect (0 : ContextField Arith ℝ) = defect logDivisorCount
  rw [defect_zero]
  exact (isValuation_iff_defect_eq_zero.mp isValuation_logDivisorCount).symm

/-- No defect-only observation decides realizability: two fields with
identical defect data, one realizable, one not. -/
theorem exists_defectEquiv_realizable_not_realizable :
    ∃ K K' : ContextField Arith ℝ,
      DefectEquiv K K' ∧ Realizable K ∧ ¬Realizable K' :=
  ⟨0, logDivisorCount, defectEquiv_zero_logDivisorCount, realizable_zero,
    not_realizable_logDivisorCount⟩

end Arith

end Descent
