import Descent.Realization.Restriction
import Mathlib.Data.Fintype.BigOperators

/-!
# The pairwise recognition theorem

When is a `logCard` defect a pure gluing obstruction? For every finite
restriction system over a lattice the defect of the logarithmic
cardinality field decomposes exactly:

    D_logCard (a, b) = log (|Compat (a,b)| / |X (a⊔b)|)
                     + log (|X a|·|X b| / (|X (a⊓b)|·|Compat (a,b)|))

The first summand is the comparison-cardinality term; the second is the
fiber-balance residue --- the exact obstruction to reading an arbitrary
`logCard` defect as a gluing measurement.

Under an injective comparison the compatible pairs are exactly the
embedded global states together with the missed ones, so the comparison
term is `log (1 + |Missed (a,b)| / |X (a⊔b)|)`: nonnegative, and zero
exactly when the comparison is surjective. The residue vanishes exactly
under the cardinal balance `|Compat (a,b)|·|X (a⊓b)| = |X a|·|X b|`;
compatible pairs fiber over the meet as products of the two restriction
legs' fibers, so constant fiber cardinality of either leg forces the
balance.
-/

namespace Descent

private theorem card_eq_sum_card_fiber {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) :
    Fintype.card α = ∑ t : β, Fintype.card { s : α // f s = t } := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm

namespace FiniteRestriction

variable {R : Type*} [Lattice R] (F : FiniteRestriction R)

/-- The missed compatible states: the compatible pairs the canonical
comparison does not reach. -/
def Missed (a b : R) : Type :=
  { p : F.Compat a b // ∀ s, F.compare a b s ≠ p }

instance (a b : R) : Fintype (F.Missed a b) :=
  inferInstanceAs (Fintype { p : F.Compat a b // ∀ s, F.compare a b s ≠ p })

instance (a b : R) : DecidableEq (F.Missed a b) :=
  inferInstanceAs (DecidableEq { p : F.Compat a b // ∀ s, F.compare a b s ≠ p })

/-- The comparison-cardinality term: the logarithmic ratio of the
compatible pairs to the global states. -/
noncomputable def comparisonTerm (a b : R) : ℝ :=
  Real.log ((Fintype.card (F.Compat a b) : ℝ)
    / (Fintype.card (F.states (a ⊔ b)) : ℝ))

/-- The fiber-balance residue: the exact remainder separating the
`logCard` defect from the comparison-cardinality term. -/
noncomputable def residue (a b : R) : ℝ :=
  Real.log (((Fintype.card (F.states a) : ℝ) * (Fintype.card (F.states b) : ℝ))
    / ((Fintype.card (F.states (a ⊓ b)) : ℝ) * (Fintype.card (F.Compat a b) : ℝ)))

/-- The recognition decomposition: every `logCard` defect is the
comparison-cardinality term plus the fiber-balance residue, exactly. -/
theorem defect_logCard (a b : R) :
    defect F.logCard a b = F.comparisonTerm a b + F.residue a b := by
  have hC : ((Fintype.card (F.Compat a b) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hj : ((Fintype.card (F.states (a ⊔ b)) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm : ((Fintype.card (F.states (a ⊓ b)) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have ha : ((Fintype.card (F.states a) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hb : ((Fintype.card (F.states b) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [comparisonTerm, residue, defect_def, logCard]
  rw [Real.log_div hC hj, Real.log_div (mul_ne_zero ha hb) (mul_ne_zero hm hC),
    Real.log_mul ha hb, Real.log_mul hm hC]
  ring

/-! ### The comparison term under an injective comparison -/

/-- Under an injective comparison the compatible pairs are exactly the
embedded global states together with the missed ones. -/
theorem card_compat_of_injective {a b : R}
    (h : Function.Injective (F.compare a b)) :
    Fintype.card (F.Compat a b)
      = Fintype.card (F.states (a ⊔ b)) + Fintype.card (F.Missed a b) := by
  have hrange : Fintype.card { p : F.Compat a b // ∃ s, F.compare a b s = p }
      = Fintype.card (F.states (a ⊔ b)) :=
    (Fintype.card_congr
      (Equiv.ofBijective (fun s => ⟨F.compare a b s, s, rfl⟩)
        ⟨fun s t hst => h (congrArg Subtype.val hst),
          fun p => p.2.elim fun s hs => ⟨s, Subtype.ext hs⟩⟩)).symm
  have hmissed : Fintype.card (F.Missed a b)
      = Fintype.card { p : F.Compat a b // ¬∃ s, F.compare a b s = p } :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun p => by
      simp only [not_exists, ne_eq])
  have hsplit : Fintype.card { p : F.Compat a b // ¬∃ s, F.compare a b s = p }
      = Fintype.card (F.Compat a b)
        - Fintype.card { p : F.Compat a b // ∃ s, F.compare a b s = p } :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card { p : F.Compat a b // ∃ s, F.compare a b s = p }
      ≤ Fintype.card (F.Compat a b) :=
    Fintype.card_subtype_le _
  omega

/-- Under an injective comparison the comparison-cardinality term counts
the missed compatible states against the global states. -/
theorem comparisonTerm_eq_of_injective {a b : R}
    (h : Function.Injective (F.compare a b)) :
    F.comparisonTerm a b
      = Real.log (1 + (Fintype.card (F.Missed a b) : ℝ)
          / (Fintype.card (F.states (a ⊔ b)) : ℝ)) := by
  have hj : (0 : ℝ) < (Fintype.card (F.states (a ⊔ b)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  simp only [comparisonTerm]
  rw [F.card_compat_of_injective h]
  push_cast
  rw [add_div, div_self hj.ne']

/-- Under an injective comparison the comparison-cardinality term is
nonnegative. -/
theorem comparisonTerm_nonneg {a b : R}
    (h : Function.Injective (F.compare a b)) :
    0 ≤ F.comparisonTerm a b := by
  have hj : (0 : ℝ) < (Fintype.card (F.states (a ⊔ b)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  simp only [comparisonTerm]
  refine Real.log_nonneg ((one_le_div hj).mpr ?_)
  exact_mod_cast Fintype.card_le_of_injective _ h

/-- The sharp zero law of the comparison term: under an injective
comparison it vanishes exactly when the comparison is surjective. -/
theorem comparisonTerm_eq_zero_iff {a b : R}
    (h : Function.Injective (F.compare a b)) :
    F.comparisonTerm a b = 0 ↔ Function.Surjective (F.compare a b) := by
  have hS : (0 : ℝ) < (Fintype.card (F.states (a ⊔ b)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hC : (0 : ℝ) < (Fintype.card (F.Compat a b) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  simp only [comparisonTerm]
  constructor
  · intro h0
    rcases Real.log_eq_zero.mp h0 with hz | hz | hz
    · exact absurd hz (div_pos hC hS).ne'
    · have hcards : Fintype.card (F.Compat a b)
          = Fintype.card (F.states (a ⊔ b)) := by
        exact_mod_cast (div_eq_one_iff_eq hS.ne').mp hz
      exact ((Fintype.bijective_iff_injective_and_card
        (F.compare a b)).mpr ⟨h, hcards.symm⟩).surjective
    · exfalso
      linarith [div_pos hC hS]
  · intro hs
    have hcards : Fintype.card (F.states (a ⊔ b))
        = Fintype.card (F.Compat a b) :=
      Fintype.card_of_bijective ⟨h, hs⟩
    rw [hcards, div_self hC.ne']
    exact Real.log_one

/-! ### The residue and the cardinal balance -/

/-- The sharp zero law of the residue: it vanishes exactly under the
cardinal balance. -/
theorem residue_eq_zero_iff (a b : R) :
    F.residue a b = 0
      ↔ Fintype.card (F.Compat a b) * Fintype.card (F.states (a ⊓ b))
          = Fintype.card (F.states a) * Fintype.card (F.states b) := by
  have hnum : (0 : ℝ)
      < (Fintype.card (F.states a) : ℝ) * (Fintype.card (F.states b) : ℝ) :=
    mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)
  have hden : (0 : ℝ)
      < (Fintype.card (F.states (a ⊓ b)) : ℝ)
          * (Fintype.card (F.Compat a b) : ℝ) :=
    mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)
  simp only [residue]
  constructor
  · intro h0
    rcases Real.log_eq_zero.mp h0 with hz | hz | hz
    · exact absurd hz (div_pos hnum hden).ne'
    · have hnat : Fintype.card (F.states a) * Fintype.card (F.states b)
          = Fintype.card (F.states (a ⊓ b)) * Fintype.card (F.Compat a b) := by
        exact_mod_cast (div_eq_one_iff_eq hden.ne').mp hz
      rw [hnat]
      exact mul_comm _ _
    · exfalso
      linarith [div_pos hnum hden]
  · intro hbal
    have hnat : Fintype.card (F.states a) * Fintype.card (F.states b)
        = Fintype.card (F.states (a ⊓ b)) * Fintype.card (F.Compat a b) := by
      rw [← hbal]
      exact mul_comm _ _
    have hcast : (Fintype.card (F.states a) : ℝ) * (Fintype.card (F.states b) : ℝ)
        = (Fintype.card (F.states (a ⊓ b)) : ℝ)
            * (Fintype.card (F.Compat a b) : ℝ) := by
      exact_mod_cast hnat
    rw [(div_eq_one_iff_eq hden.ne').mpr hcast]
    exact Real.log_one

/-- Under the cardinal balance the `logCard` defect is the comparison
term alone: a pure gluing measurement. -/
theorem defect_logCard_of_balance {a b : R}
    (h : Fintype.card (F.Compat a b) * Fintype.card (F.states (a ⊓ b))
      = Fintype.card (F.states a) * Fintype.card (F.states b)) :
    defect F.logCard a b = F.comparisonTerm a b := by
  rw [F.defect_logCard a b, (F.residue_eq_zero_iff a b).mpr h, add_zero]

/-! ### Fibering over the meet -/

/-- Compatible pairs fiber over the meet: `Compat a b` is the disjoint
union, over the states of the meet, of the products of the two
restriction legs' fibers. -/
def compatSigmaEquiv (a b : R) :
    F.Compat a b
      ≃ Σ t : F.states (a ⊓ b),
          { s : F.states a // F.restrict inf_le_left s = t }
            × { u : F.states b // F.restrict inf_le_right u = t } where
  toFun p := ⟨F.restrict inf_le_left p.1.1, ⟨p.1.1, rfl⟩, ⟨p.1.2, p.2.symm⟩⟩
  invFun q := ⟨(q.2.1.1, q.2.2.1), q.2.1.2.trans q.2.2.2.symm⟩
  left_inv p := rfl
  right_inv := by rintro ⟨t, ⟨s, rfl⟩, ⟨u, hu⟩⟩; rfl

/-- The compatible-pair count is the sum, over the states of the meet,
of the products of the two legs' fiber counts. -/
theorem card_compat_eq_sum (a b : R) :
    Fintype.card (F.Compat a b)
      = ∑ t : F.states (a ⊓ b),
          Fintype.card { s : F.states a // F.restrict inf_le_left s = t }
            * Fintype.card { u : F.states b // F.restrict inf_le_right u = t } := by
  rw [Fintype.card_congr (F.compatSigmaEquiv a b), Fintype.card_sigma]
  simp only [Fintype.card_prod]

/-- Constant fiber cardinality of the left restriction leg to the meet
forces the cardinal balance. -/
theorem balance_of_const_fiber_left (a b : R) (n : ℕ)
    (h : ∀ t : F.states (a ⊓ b),
      Fintype.card { s : F.states a // F.restrict inf_le_left s = t } = n) :
    Fintype.card (F.Compat a b) * Fintype.card (F.states (a ⊓ b))
      = Fintype.card (F.states a) * Fintype.card (F.states b) := by
  have hC : Fintype.card (F.Compat a b) = n * Fintype.card (F.states b) := by
    rw [F.card_compat_eq_sum a b,
      card_eq_sum_card_fiber (F.restrict (inf_le_right : a ⊓ b ≤ b)),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [h t]
  have hA : Fintype.card (F.states a)
      = Fintype.card (F.states (a ⊓ b)) * n := by
    rw [card_eq_sum_card_fiber (F.restrict (inf_le_left : a ⊓ b ≤ a))]
    simp [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hC, hA]
  ring

/-- Constant fiber cardinality of the right restriction leg to the meet
forces the cardinal balance. -/
theorem balance_of_const_fiber_right (a b : R) (n : ℕ)
    (h : ∀ t : F.states (a ⊓ b),
      Fintype.card { u : F.states b // F.restrict inf_le_right u = t } = n) :
    Fintype.card (F.Compat a b) * Fintype.card (F.states (a ⊓ b))
      = Fintype.card (F.states a) * Fintype.card (F.states b) := by
  have hC : Fintype.card (F.Compat a b) = Fintype.card (F.states a) * n := by
    rw [F.card_compat_eq_sum a b,
      card_eq_sum_card_fiber (F.restrict (inf_le_left : a ⊓ b ≤ a)),
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by rw [h t]
  have hB : Fintype.card (F.states b)
      = Fintype.card (F.states (a ⊓ b)) * n := by
    rw [card_eq_sum_card_fiber (F.restrict (inf_le_right : a ⊓ b ≤ b))]
    simp [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hC, hB]
  ring

end FiniteRestriction

end Descent
