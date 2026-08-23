import Descent.Core.Gauge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Finite restriction systems

Restriction data, made observable. A finite restriction system over a
preorder assigns to each context a nonempty finite state type and to
each comparison `a ≤ b` a restriction map from finer to coarser states,
functorially.

Lattice structure enters only for the local-to-global construction:
compatible states at `a, b` form the fiber product of `states a` and
`states b` over `states (a ⊓ b)`, and a global state over the join
restricts to a compatible pair --- the canonical comparison, the
structural local-to-global map. The logarithmic cardinality field is
the candidate field of the system; for an arbitrary system its defect
need not measure the comparison --- fiber cardinalities need not be
uniform and the comparison need not be injective --- so the
identification of defect coordinates with comparison losses is
established per model, as in `Descent.Models.DiamondCode`.
-/

namespace Descent

/-- A finite restriction system over a preorder: nonempty finite state
types with functorial restriction toward coarser contexts. -/
structure FiniteRestriction (R : Type*) [Preorder R] where
  states : R → Type
  fintype : ∀ r, Fintype (states r)
  nonempty : ∀ r, Nonempty (states r)
  decEq : ∀ r, DecidableEq (states r)
  restrict : ∀ {a b : R}, a ≤ b → states b → states a
  restrict_rfl : ∀ (r : R) (s : states r), restrict le_rfl s = s
  restrict_restrict :
    ∀ {a b c : R} (hab : a ≤ b) (hbc : b ≤ c) (s : states c),
      restrict hab (restrict hbc s) = restrict (hab.trans hbc) s

namespace FiniteRestriction

variable {R : Type*}

section Preorder

variable [Preorder R] (F : FiniteRestriction R)

instance (r : R) : Fintype (F.states r) := F.fintype r

instance (r : R) : Nonempty (F.states r) := F.nonempty r

instance (r : R) : DecidableEq (F.states r) := F.decEq r

/-- The logarithmic cardinality field of a restriction system. -/
noncomputable def logCard : ContextField R ℝ := fun r =>
  Real.log (Fintype.card (F.states r))

end Preorder

section Lattice

variable [Lattice R] (F : FiniteRestriction R)

/-- Compatible states at `a, b`: the fiber product of the two state
types over the states of the meet. -/
def Compat (a b : R) : Type :=
  { p : F.states a × F.states b //
    F.restrict inf_le_left p.1 = F.restrict inf_le_right p.2 }

instance (a b : R) : Fintype (F.Compat a b) :=
  inferInstanceAs (Fintype { p : F.states a × F.states b //
    F.restrict inf_le_left p.1 = F.restrict inf_le_right p.2 })

instance (a b : R) : DecidableEq (F.Compat a b) :=
  inferInstanceAs (DecidableEq { p : F.states a × F.states b //
    F.restrict inf_le_left p.1 = F.restrict inf_le_right p.2 })

/-- The canonical comparison: a global state over the join restricts to
a compatible pair. -/
def compare (a b : R) (s : F.states (a ⊔ b)) : F.Compat a b :=
  ⟨(F.restrict le_sup_left s, F.restrict le_sup_right s), by
    rw [F.restrict_restrict, F.restrict_restrict]⟩

instance (a b : R) : Nonempty (F.Compat a b) :=
  (F.nonempty (a ⊔ b)).map (F.compare a b)

/-- Compatible triples: pairwise fiber products over the meets. -/
def Compat3 (a b c : R) : Type :=
  { t : F.states a × F.states b × F.states c //
    F.restrict (inf_le_left : a ⊓ b ≤ a) t.1
        = F.restrict inf_le_right t.2.1 ∧
      F.restrict (inf_le_left : a ⊓ c ≤ a) t.1
        = F.restrict inf_le_right t.2.2 ∧
      F.restrict (inf_le_left : b ⊓ c ≤ b) t.2.1
        = F.restrict inf_le_right t.2.2 }

instance (a b c : R) : Fintype (F.Compat3 a b c) :=
  inferInstanceAs (Fintype { t : F.states a × F.states b × F.states c //
    F.restrict (inf_le_left : a ⊓ b ≤ a) t.1
        = F.restrict inf_le_right t.2.1 ∧
      F.restrict (inf_le_left : a ⊓ c ≤ a) t.1
        = F.restrict inf_le_right t.2.2 ∧
      F.restrict (inf_le_left : b ⊓ c ≤ b) t.2.1
        = F.restrict inf_le_right t.2.2 })

instance (a b c : R) : DecidableEq (F.Compat3 a b c) :=
  inferInstanceAs (DecidableEq { t : F.states a × F.states b × F.states c //
    F.restrict (inf_le_left : a ⊓ b ≤ a) t.1
        = F.restrict inf_le_right t.2.1 ∧
      F.restrict (inf_le_left : a ⊓ c ≤ a) t.1
        = F.restrict inf_le_right t.2.2 ∧
      F.restrict (inf_le_left : b ⊓ c ≤ b) t.2.1
        = F.restrict inf_le_right t.2.2 })

/-- The canonical triple comparison. -/
def compare3 (a b c : R) (s : F.states (a ⊔ b ⊔ c)) : F.Compat3 a b c :=
  ⟨(F.restrict (le_sup_left.trans le_sup_left) s,
    F.restrict (le_sup_right.trans le_sup_left) s,
    F.restrict le_sup_right s),
    ⟨by rw [F.restrict_restrict, F.restrict_restrict],
      by rw [F.restrict_restrict, F.restrict_restrict],
      by rw [F.restrict_restrict, F.restrict_restrict]⟩⟩

instance (a b c : R) : Nonempty (F.Compat3 a b c) :=
  (F.nonempty (a ⊔ b ⊔ c)).map (F.compare3 a b c)

end Lattice

end FiniteRestriction

end Descent
