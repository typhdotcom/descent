import Mathlib.Order.Lattice

/-!
# Contexts

A *context* is one admissible description of a system: a resolution, a
coordinate choice, a coarse-graining, a local view. The carrier is a
`Lattice`, so two contexts can always be compared in two ways --- `a ⊓ b` is
the description they jointly refine, `a ⊔ b` the description that refines both.

Nothing here says what a context *is*. Realizations supply that; the defect
calculus downstream consumes only `⊓` and `⊔`.

The pair `(a, b)` spans a *comparison square* with corners `a ⊓ b`, `a`, `b`,
`a ⊔ b`. The square is degenerate exactly when `a` and `b` are comparable, and
that is the case on which every ideal composition law holds trivially.
-/

namespace Descent

variable {R : Type*}

/-- Two contexts are comparable when one refines the other. -/
def Comparable [LE R] (a b : R) : Prop :=
  a ≤ b ∨ b ≤ a

@[refl]
theorem Comparable.refl [Preorder R] (a : R) : Comparable a a :=
  Or.inl le_rfl

theorem Comparable.symm [LE R] {a b : R} (h : Comparable a b) : Comparable b a :=
  Or.symm h

theorem comparable_comm [LE R] {a b : R} : Comparable a b ↔ Comparable b a :=
  ⟨Comparable.symm, Comparable.symm⟩

theorem Comparable.of_le [LE R] {a b : R} (h : a ≤ b) : Comparable a b :=
  Or.inl h

theorem Comparable.of_ge [LE R] {a b : R} (h : b ≤ a) : Comparable a b :=
  Or.inr h

/-- On a comparable pair the comparison square collapses: its two new corners
are the two old ones, in one order or the other. -/
theorem Comparable.corners [Lattice R] {a b : R} (h : Comparable a b) :
    (a ⊓ b = a ∧ a ⊔ b = b) ∨ (a ⊓ b = b ∧ a ⊔ b = a) := by
  rcases h with h | h
  · exact Or.inl ⟨inf_of_le_left h, sup_of_le_right h⟩
  · exact Or.inr ⟨inf_of_le_right h, sup_of_le_left h⟩

end Descent
