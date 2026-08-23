import Descent.Realization.Recognition

/-!
# Observational equivalence and incidence blindness

What does the comparison term see without injectivity? The finite-map
bookkeeping is developed once, below restriction systems: a map between
finite types partitions its codomain into reached and missed values,
and its domain into the reached codomain and the redundancy
`red f = |A| - |range f|`:

    |B| = |range f| + |missed f|        |A| = |range f| + red f

Instantiated at the canonical comparisons, every comparison term becomes

    log ((|range f| + |missed f|) / (|range f| + red f))

with the complete chamber law: positive exactly when missed states
outnumber redundancy, zero exactly when they are equal, negative exactly
when redundancy outnumbers missed states; injectivity is exactly zero
redundancy and surjectivity exactly zero missed cardinality. A zero
comparison term means balanced undercoverage and overidentification in
general --- not successful gluing.

Observational equivalence of finite restriction systems is equality of
the final order-≤3 observable classes of their logarithmic cardinality
fields. Complete defect observation retains only the net cardinal
obstruction; the diamond classification and the second code system in
`Descent.Models.DiamondCode` make the blindness exact.
-/

namespace Descent

namespace Incidence

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B)

/-- The reached codomain of a finite map. -/
def Reached : Type _ :=
  { b : B // ∃ a, f a = b }

/-- The missed codomain of a finite map. -/
def Missed : Type _ :=
  { b : B // ∀ a, f a ≠ b }

instance : Fintype (Reached f) :=
  inferInstanceAs (Fintype { b : B // ∃ a, f a = b })

instance : Fintype (Missed f) :=
  inferInstanceAs (Fintype { b : B // ∀ a, f a ≠ b })

/-- The redundancy of a finite map: the number of domain points beyond
the reached codomain. -/
def redundancy : ℕ :=
  Fintype.card A - Fintype.card (Reached f)

/-- The canonical surjection onto the reached codomain. -/
def toReached (a : A) : Reached f :=
  ⟨f a, a, rfl⟩

omit [Fintype A] [Fintype B] [DecidableEq B] in
theorem surjective_toReached : Function.Surjective (toReached f) := fun p =>
  p.2.elim fun a ha => ⟨a, Subtype.ext ha⟩

theorem card_reached_le : Fintype.card (Reached f) ≤ Fintype.card A :=
  Fintype.card_le_of_surjective _ (surjective_toReached f)

/-- The codomain partitions exactly into reached and missed values. -/
theorem card_eq_reached_add_missed :
    Fintype.card B = Fintype.card (Reached f) + Fintype.card (Missed f) := by
  have hr : Fintype.card (Reached f)
      = Fintype.card { b : B // ∃ a, f a = b } :=
    rfl
  have hmissed : Fintype.card (Missed f)
      = Fintype.card { b : B // ¬∃ a, f a = b } :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun b => by
      simp only [not_exists, ne_eq])
  have hsplit : Fintype.card { b : B // ¬∃ a, f a = b }
      = Fintype.card B - Fintype.card { b : B // ∃ a, f a = b } :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card { b : B // ∃ a, f a = b } ≤ Fintype.card B :=
    Fintype.card_subtype_le _
  omega

/-- The domain partitions exactly into the reached codomain and the
redundancy. -/
theorem card_eq_reached_add_redundancy :
    Fintype.card A = Fintype.card (Reached f) + redundancy f := by
  have := card_reached_le f
  simp only [redundancy]
  omega

/-- Injectivity is exactly zero redundancy. -/
theorem injective_iff_redundancy_eq_zero :
    Function.Injective f ↔ redundancy f = 0 := by
  have hle := card_reached_le f
  constructor
  · intro h
    have hinj : Function.Injective (toReached f) := fun a a' ha =>
      h (congrArg Subtype.val ha)
    have := Fintype.card_le_of_injective _ hinj
    simp only [redundancy]
    omega
  · intro h
    have hcard : Fintype.card A = Fintype.card (Reached f) := by
      simp only [redundancy] at h
      omega
    have hbij : Function.Bijective (toReached f) :=
      (Fintype.bijective_iff_surjective_and_card _).mpr
        ⟨surjective_toReached f, hcard⟩
    intro a a' ha
    exact hbij.injective (Subtype.ext ha)

/-- Surjectivity is exactly zero missed cardinality. -/
theorem surjective_iff_card_missed_eq_zero :
    Function.Surjective f ↔ Fintype.card (Missed f) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  · intro h
    exact ⟨fun p => (h p.1).elim fun a ha => p.2 a ha⟩
  · intro h b
    by_contra hb
    exact h.elim ⟨b, fun a ha => hb ⟨a, ha⟩⟩

end Incidence

namespace FiniteRestriction

variable {R : Type*} [Lattice R] (F : FiniteRestriction R)

/-- The generic missed codomain of the comparison is the missed
compatible states. -/
theorem incidence_missed_compare (a b : R) :
    Incidence.Missed (F.compare a b) = F.Missed a b :=
  rfl

theorem incidence_missed_compare3 (a b c : R) :
    Incidence.Missed (F.compare3 a b c) = F.Missed3 a b c :=
  rfl

/-- The comparison term through incidence bookkeeping: the logarithmic
ratio of reached-plus-missed to reached-plus-redundancy. -/
theorem comparisonTerm_eq_incidence (a b : R) :
    F.comparisonTerm a b
      = Real.log
          (((Fintype.card (Incidence.Reached (F.compare a b))
                + Fintype.card (Incidence.Missed (F.compare a b)) : ℕ) : ℝ)
            / ((Fintype.card (Incidence.Reached (F.compare a b))
                + Incidence.redundancy (F.compare a b) : ℕ) : ℝ)) := by
  simp only [comparisonTerm]
  rw [Incidence.card_eq_reached_add_missed (F.compare a b),
    Incidence.card_eq_reached_add_redundancy (F.compare a b)]

/-- The chamber law, positive side: the comparison term is positive
exactly when missed states outnumber redundancy. -/
theorem comparisonTerm_pos_iff (a b : R) :
    0 < F.comparisonTerm a b
      ↔ Incidence.redundancy (F.compare a b)
          < Fintype.card (Incidence.Missed (F.compare a b)) := by
  have hA : (0 : ℝ) < (Fintype.card (F.states (a ⊔ b)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  simp only [comparisonTerm]
  rw [Real.log_pos_iff (by positivity), one_lt_div hA, Nat.cast_lt,
    Incidence.card_eq_reached_add_missed (F.compare a b),
    Incidence.card_eq_reached_add_redundancy (F.compare a b)]
  omega

/-- The chamber law, negative side: the comparison term is negative
exactly when redundancy outnumbers missed states. -/
theorem comparisonTerm_neg_iff (a b : R) :
    F.comparisonTerm a b < 0
      ↔ Fintype.card (Incidence.Missed (F.compare a b))
          < Incidence.redundancy (F.compare a b) := by
  have hA : (0 : ℝ) < (Fintype.card (F.states (a ⊔ b)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hC : (0 : ℝ) < (Fintype.card (F.Compat a b) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  simp only [comparisonTerm]
  rw [Real.log_neg_iff (div_pos hC hA), div_lt_one hA, Nat.cast_lt,
    Incidence.card_eq_reached_add_missed (F.compare a b),
    Incidence.card_eq_reached_add_redundancy (F.compare a b)]
  omega

/-- The chamber law, zero: the comparison term vanishes exactly when
missed states and redundancy are equal --- balanced undercoverage and
overidentification, not successful gluing. -/
theorem comparisonTerm_eq_zero_iff_missed_eq_redundancy (a b : R) :
    F.comparisonTerm a b = 0
      ↔ Fintype.card (Incidence.Missed (F.compare a b))
          = Incidence.redundancy (F.compare a b) := by
  have hA : (0 : ℝ) < (Fintype.card (F.states (a ⊔ b)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hC : (0 : ℝ) < (Fintype.card (F.Compat a b) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have h1 := Incidence.card_eq_reached_add_missed (F.compare a b)
  have h2 := Incidence.card_eq_reached_add_redundancy (F.compare a b)
  simp only [comparisonTerm]
  constructor
  · intro h0
    rcases Real.log_eq_zero.mp h0 with hz | hz | hz
    · exact absurd hz (div_pos hC hA).ne'
    · have : Fintype.card (F.Compat a b)
          = Fintype.card (F.states (a ⊔ b)) := by
        exact_mod_cast (div_eq_one_iff_eq hA.ne').mp hz
      omega
    · exfalso
      linarith [div_pos hC hA]
  · intro h
    have : Fintype.card (F.Compat a b) = Fintype.card (F.states (a ⊔ b)) := by
      omega
    rw [this, div_self hA.ne']
    exact Real.log_one

/-- Injectivity of the comparison is exactly zero redundancy. -/
theorem compare_injective_iff (a b : R) :
    Function.Injective (F.compare a b)
      ↔ Incidence.redundancy (F.compare a b) = 0 :=
  Incidence.injective_iff_redundancy_eq_zero _

/-- Surjectivity of the comparison is exactly zero missed
cardinality. -/
theorem compare_surjective_iff (a b : R) :
    Function.Surjective (F.compare a b)
      ↔ Fintype.card (Incidence.Missed (F.compare a b)) = 0 :=
  Incidence.surjective_iff_card_missed_eq_zero _

/-- The triple comparison term through incidence bookkeeping. -/
theorem comparisonTerm3_eq_incidence (a b c : R) :
    F.comparisonTerm3 a b c
      = Real.log
          (((Fintype.card (Incidence.Reached (F.compare3 a b c))
                + Fintype.card (Incidence.Missed (F.compare3 a b c)) : ℕ) : ℝ)
            / ((Fintype.card (Incidence.Reached (F.compare3 a b c))
                + Incidence.redundancy (F.compare3 a b c) : ℕ) : ℝ)) := by
  simp only [comparisonTerm3]
  rw [Incidence.card_eq_reached_add_missed (F.compare3 a b c),
    Incidence.card_eq_reached_add_redundancy (F.compare3 a b c)]

/-- The chamber law at order 3, positive side. -/
theorem comparisonTerm3_pos_iff (a b c : R) :
    0 < F.comparisonTerm3 a b c
      ↔ Incidence.redundancy (F.compare3 a b c)
          < Fintype.card (Incidence.Missed (F.compare3 a b c)) := by
  have hA : (0 : ℝ) < (Fintype.card (F.states (a ⊔ b ⊔ c)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  simp only [comparisonTerm3]
  rw [Real.log_pos_iff (by positivity), one_lt_div hA, Nat.cast_lt,
    Incidence.card_eq_reached_add_missed (F.compare3 a b c),
    Incidence.card_eq_reached_add_redundancy (F.compare3 a b c)]
  omega

/-- The chamber law at order 3, negative side. -/
theorem comparisonTerm3_neg_iff (a b c : R) :
    F.comparisonTerm3 a b c < 0
      ↔ Fintype.card (Incidence.Missed (F.compare3 a b c))
          < Incidence.redundancy (F.compare3 a b c) := by
  have hA : (0 : ℝ) < (Fintype.card (F.states (a ⊔ b ⊔ c)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hC : (0 : ℝ) < (Fintype.card (F.Compat3 a b c) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  simp only [comparisonTerm3]
  rw [Real.log_neg_iff (div_pos hC hA), div_lt_one hA, Nat.cast_lt,
    Incidence.card_eq_reached_add_missed (F.compare3 a b c),
    Incidence.card_eq_reached_add_redundancy (F.compare3 a b c)]
  omega

/-- The chamber law at order 3, zero: balanced undercoverage and
overidentification. -/
theorem comparisonTerm3_eq_zero_iff_missed_eq_redundancy (a b c : R) :
    F.comparisonTerm3 a b c = 0
      ↔ Fintype.card (Incidence.Missed (F.compare3 a b c))
          = Incidence.redundancy (F.compare3 a b c) := by
  have hA : (0 : ℝ) < (Fintype.card (F.states (a ⊔ b ⊔ c)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hC : (0 : ℝ) < (Fintype.card (F.Compat3 a b c) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have h1 := Incidence.card_eq_reached_add_missed (F.compare3 a b c)
  have h2 := Incidence.card_eq_reached_add_redundancy (F.compare3 a b c)
  simp only [comparisonTerm3]
  constructor
  · intro h0
    rcases Real.log_eq_zero.mp h0 with hz | hz | hz
    · exact absurd hz (div_pos hC hA).ne'
    · have : Fintype.card (F.Compat3 a b c)
          = Fintype.card (F.states (a ⊔ b ⊔ c)) := by
        exact_mod_cast (div_eq_one_iff_eq hA.ne').mp hz
      omega
    · exfalso
      linarith [div_pos hC hA]
  · intro h
    have : Fintype.card (F.Compat3 a b c)
        = Fintype.card (F.states (a ⊔ b ⊔ c)) := by
      omega
    rw [this, div_self hA.ne']
    exact Real.log_one

/-- Injectivity of the triple comparison is exactly zero redundancy. -/
theorem compare3_injective_iff (a b c : R) :
    Function.Injective (F.compare3 a b c)
      ↔ Incidence.redundancy (F.compare3 a b c) = 0 :=
  Incidence.injective_iff_redundancy_eq_zero _

/-- Surjectivity of the triple comparison is exactly zero missed
cardinality. -/
theorem compare3_surjective_iff (a b c : R) :
    Function.Surjective (F.compare3 a b c)
      ↔ Fintype.card (Incidence.Missed (F.compare3 a b c)) = 0 :=
  Incidence.surjective_iff_card_missed_eq_zero _

end FiniteRestriction

/-- Observational equivalence of finite restriction systems: equality of
the final order-≤3 observable classes of their logarithmic cardinality
fields. -/
def ObservationalEquiv {R : Type*} [Lattice R] (F G : FiniteRestriction R) : Prop :=
  Observable3.mk F.logCard = Observable3.mk G.logCard

end Descent
