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

The extension profile `ext f b = |{a : f a = b}|` recovers what the
scalar term discards. Its total mass is `|A|`; positivity is
reachedness, vanishing is missedness; injectivity, surjectivity, and
bijectivity are the pointwise bounds `≤ 1`, `> 0`, `= 1`; redundancy is
the total fiber excess `∑ (ext f b − 1)`. The reconstruction limit:
two finite maps into the same codomain have equal extension profiles
exactly when an equivalence of their domains carries one to the other
over the codomain --- the conditioned profile determines a finite map
up to relabeling within its fibers. The scalar comparison term is only
the coarse statistic of the profile's sum against the codomain size.
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

/-! ### The extension profile -/

/-- The extension profile of a finite map: each codomain value's number
of extensions. -/
def ext (b : B) : ℕ :=
  Fintype.card { a : A // f a = b }

/-- Total mass: the extension profile sums to the domain size. -/
theorem sum_ext : ∑ b : B, ext f b = Fintype.card A := by
  simp only [ext]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

omit [Fintype B] in
/-- A codomain value is reached exactly when its extension count is
positive. -/
theorem ext_pos_iff (b : B) : 0 < ext f b ↔ ∃ a, f a = b := by
  simp only [ext]
  rw [Fintype.card_pos_iff]
  exact nonempty_subtype

omit [Fintype B] in
/-- A codomain value is missed exactly when its extension count is
zero. -/
theorem ext_eq_zero_iff (b : B) : ext f b = 0 ↔ ∀ a, f a ≠ b := by
  simp only [ext]
  rw [Fintype.card_eq_zero_iff]
  exact isEmpty_subtype _

omit [Fintype B] in
/-- Injectivity is exactly extension counts at most one. -/
theorem injective_iff_ext_le_one :
    Function.Injective f ↔ ∀ b, ext f b ≤ 1 := by
  constructor
  · intro h b
    simp only [ext]
    rw [Fintype.card_le_one_iff]
    rintro ⟨a, ha⟩ ⟨a', ha'⟩
    exact Subtype.ext (h (ha.trans ha'.symm))
  · intro h a a' haa
    have hone : Fintype.card { s : A // f s = f a } ≤ 1 := h (f a)
    exact congrArg Subtype.val
      (Fintype.card_le_one_iff.mp hone ⟨a, rfl⟩ ⟨a', haa.symm⟩)

omit [Fintype B] in
/-- Surjectivity is exactly positive extension counts. -/
theorem surjective_iff_ext_pos :
    Function.Surjective f ↔ ∀ b, 0 < ext f b := by
  constructor
  · intro h b
    exact (ext_pos_iff f b).mpr (h b)
  · intro h b
    exact (ext_pos_iff f b).mp (h b)

omit [Fintype B] in
/-- Bijectivity is exactly extension counts one. -/
theorem bijective_iff_ext_eq_one :
    Function.Bijective f ↔ ∀ b, ext f b = 1 := by
  constructor
  · rintro ⟨hinj, hsurj⟩ b
    have h1 := (injective_iff_ext_le_one f).mp hinj b
    have h2 := (surjective_iff_ext_pos f).mp hsurj b
    omega
  · intro h
    refine ⟨(injective_iff_ext_le_one f).mpr fun b => (h b).le,
      (surjective_iff_ext_pos f).mpr fun b => ?_⟩
    rw [h b]
    exact Nat.one_pos

/-- Redundancy is the total fiber excess. -/
theorem redundancy_eq_sum_ext_sub_one :
    redundancy f = ∑ b : B, (ext f b - 1) := by
  have hpt : ∀ b : B, (ext f b - 1) + (if 0 < ext f b then 1 else 0)
      = ext f b := by
    intro b
    by_cases h : 0 < ext f b
    · simp only [if_pos h]
      omega
    · simp only [if_neg h]
      omega
  have hR : Fintype.card (Reached f)
      = ∑ b : B, if 0 < ext f b then 1 else 0 := by
    have e : Reached f ≃ { b : B // 0 < ext f b } :=
      Equiv.subtypeEquivRight fun b => (ext_pos_iff f b).symm
    rw [Fintype.card_congr e, Fintype.card_subtype, Finset.card_filter]
  have hA := sum_ext f
  have hsplit : ((∑ b : B, (ext f b - 1))
        + ∑ b : B, if 0 < ext f b then 1 else 0)
      = ∑ b : B, ext f b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => hpt b
  have hle := card_reached_le f
  simp only [redundancy]
  omega

omit [Fintype B] in
/-- The reconstruction limit: two finite maps into the same codomain
have equal extension profiles exactly when an equivalence of their
domains carries one to the other over the codomain. The conditioned
profile determines a finite map up to relabeling within its fibers. -/
theorem ext_eq_iff_exists_equiv {C : Type*} [Fintype C] (g : C → B) :
    (∀ b, ext f b = ext g b) ↔ ∃ e : A ≃ C, ∀ a, g (e a) = f a := by
  constructor
  · intro h
    have e_b : ∀ b, { a : A // f a = b } ≃ { c : C // g c = b } := fun b =>
      Fintype.equivOfCardEq (h b)
    exact ⟨(Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight e_b).trans (Equiv.sigmaFiberEquiv g)),
      fun a => (e_b (f a) ⟨a, rfl⟩).2⟩
  · rintro ⟨e, he⟩ b
    exact Fintype.card_congr (Equiv.subtypeEquiv e fun a => by rw [he a])

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

/-! ### The comparison term as a coarse profile statistic -/

/-- The scalar comparison term is only the coarse statistic of the
extension profile: the codomain size against the profile's total
mass. -/
theorem comparisonTerm_eq_ext_sum (a b : R) :
    F.comparisonTerm a b
      = Real.log ((Fintype.card (F.Compat a b) : ℝ)
          / ((∑ p : F.Compat a b, Incidence.ext (F.compare a b) p : ℕ) : ℝ)) := by
  simp only [comparisonTerm]
  rw [← Incidence.sum_ext (F.compare a b)]

/-- The scalar triple comparison term is the same coarse statistic. -/
theorem comparisonTerm3_eq_ext_sum (a b c : R) :
    F.comparisonTerm3 a b c
      = Real.log ((Fintype.card (F.Compat3 a b c) : ℝ)
          / ((∑ t : F.Compat3 a b c,
              Incidence.ext (F.compare3 a b c) t : ℕ) : ℝ)) := by
  simp only [comparisonTerm3]
  rw [← Incidence.sum_ext (F.compare3 a b c)]

/-- The reconstruction limit at a comparison: two maps of global states
into the same compatible local states have equal extension profiles
exactly when a relabeling of global states over the compatible pairs
carries one to the other. -/
theorem compare_ext_eq_iff (a b : R) {S T : Type*} [Fintype S] [Fintype T]
    (f : S → F.Compat a b) (g : T → F.Compat a b) :
    (∀ p, Incidence.ext f p = Incidence.ext g p)
      ↔ ∃ e : S ≃ T, ∀ s, g (e s) = f s :=
  Incidence.ext_eq_iff_exists_equiv f g

/-- The reconstruction limit at a triple comparison. -/
theorem compare3_ext_eq_iff (a b c : R) {S T : Type*} [Fintype S] [Fintype T]
    (f : S → F.Compat3 a b c) (g : T → F.Compat3 a b c) :
    (∀ t, Incidence.ext f t = Incidence.ext g t)
      ↔ ∃ e : S ≃ T, ∀ s, g (e s) = f s :=
  Incidence.ext_eq_iff_exists_equiv f g

end FiniteRestriction

/-- Observational equivalence of finite restriction systems: equality of
the final order-≤3 observable classes of their logarithmic cardinality
fields. -/
def ObservationalEquiv {R : Type*} [Lattice R] (F G : FiniteRestriction R) : Prop :=
  Observable3.mk F.logCard = Observable3.mk G.logCard

end Descent
