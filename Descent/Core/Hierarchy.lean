import Descent.Core.Higher

/-!
# The full inclusion–exclusion hierarchy

One defect for every finite family: for a nonempty family `a :: l`,

    defectFam K a l = inclusionExclusion K (a :: l) - K (supFam a l),

the failure of the inclusion–exclusion prediction from meets to reach the
join. Its arity-2, 3, and 4 specializations recover `defect`, `defect3`,
and `defect4`, and its arbitrary-lattice recurrence
(`defectFam_cons`) carries the finite distributivity-gap remainder

    K (supFam a l ⊓ d) - K (supFam (a ⊓ d) (l.map (· ⊓ d))).

Saturation closes the hierarchy: the binary blindness of the order-≤3
gauge extends to finite joins (`supFam_inf_apply_eq_of_mem_gauge3`), so
every field in `gauge3` has vanishing defect at every arity
(`defectFam_eq_zero_of_mem_gauge3`), and the gauge of the whole hierarchy
is the order-≤3 gauge (`gaugeFam_eq_gauge3`): order 3 is the final
refinement of defect observation, on every lattice and every target.
-/

namespace Descent

variable {R A : Type*} [Lattice R] [AddCommGroup A]

/-! ### Finite families -/

/-- The join of the nonempty family `a :: l`. -/
def supFam (a : R) (l : List R) : R :=
  l.foldr (· ⊔ ·) a

@[simp]
theorem supFam_nil (a : R) : supFam a [] = a :=
  rfl

theorem supFam_cons (a b : R) (l : List R) :
    supFam a (b :: l) = b ⊔ supFam a l :=
  rfl

theorem supFam_sup (x y : R) (l : List R) :
    supFam (x ⊔ y) l = supFam x l ⊔ y := by
  induction l with
  | nil => rfl
  | cons z l ih =>
    rw [supFam_cons, supFam_cons, ih, ← sup_assoc]

/-- The head of a family may rotate to the outside of the join. -/
theorem supFam_comm (d a : R) (l : List R) :
    supFam d (a :: l) = supFam a l ⊔ d := by
  rw [supFam_cons, sup_comm a, ← supFam_sup, sup_comm d a, supFam_sup]

/-- The inclusion–exclusion prediction of a family: the signed sum of `K`
over the meets of its nonempty subfamilies. -/
def inclusionExclusion (K : ContextField R A) : List R → A
  | [] => 0
  | a :: l => K a + inclusionExclusion K l - inclusionExclusion K (l.map (· ⊓ a))
termination_by l => l.length
decreasing_by
  all_goals simp [List.length_map]

/-- The inclusion–exclusion defect of the nonempty family `a :: l`: the
failure of the prediction from meets to reach the join. -/
def defectFam (K : ContextField R A) (a : R) (l : List R) : A :=
  inclusionExclusion K (a :: l) - K (supFam a l)

@[simp]
theorem defectFam_nil (K : ContextField R A) (a : R) : defectFam K a [] = 0 := by
  simp [defectFam, inclusionExclusion]

/-- The exact recurrence of the hierarchy on an arbitrary lattice: peeling
one element costs the pairwise defect against the join of the rest, a
meet-translated copy of the family, and the finite distributivity-gap
remainder. -/
theorem defectFam_cons (K : ContextField R A) (d a : R) (l : List R) :
    defectFam K d (a :: l)
      = defectFam K a l + defect K (supFam a l) d
        - defectFam K (a ⊓ d) (l.map (· ⊓ d))
        + (K (supFam a l ⊓ d) - K (supFam (a ⊓ d) (l.map (· ⊓ d)))) := by
  simp only [defectFam, inclusionExclusion, List.map_cons, defect_def,
    supFam_comm]
  abel

/-! ### Arity recoveries -/

theorem defectFam_pair (K : ContextField R A) (a d : R) :
    defectFam K d [a] = defect K a d := by
  rw [defectFam_cons]
  simp only [List.map_nil, defectFam_nil, supFam_nil]
  abel

theorem defectFam_triple (K : ContextField R A) (a b c : R) :
    defectFam K c [b, a] = defect3 K a b c := by
  have h1 : supFam b [a] = a ⊔ b := rfl
  rw [defectFam_cons]
  simp only [List.map_cons, List.map_nil]
  rw [defectFam_pair, defectFam_pair, h1,
    show supFam (b ⊓ c) [a ⊓ c] = (a ⊓ c) ⊔ (b ⊓ c) from rfl,
    defect3_recurrence]

theorem defectFam_quad (K : ContextField R A) (a b c d : R) :
    defectFam K d [c, b, a] = defect4 K a b c d := by
  have h1 : supFam c [b, a] = a ⊔ b ⊔ c := by
    show b ⊔ (a ⊔ c) = a ⊔ b ⊔ c
    rw [← sup_assoc, sup_comm b a]
  have h2 : supFam (c ⊓ d) [b ⊓ d, a ⊓ d] = (a ⊓ d) ⊔ (b ⊓ d) ⊔ (c ⊓ d) := by
    show (b ⊓ d) ⊔ ((a ⊓ d) ⊔ (c ⊓ d)) = (a ⊓ d) ⊔ (b ⊓ d) ⊔ (c ⊓ d)
    rw [← sup_assoc, sup_comm (b ⊓ d) (a ⊓ d)]
  rw [defectFam_cons]
  simp only [List.map_cons, List.map_nil]
  rw [defectFam_triple, defectFam_triple, h1, h2, defect4_recurrence]

/-! ### The hierarchy gauge -/

theorem inclusionExclusion_zero :
    ∀ l : List R, inclusionExclusion (0 : ContextField R A) l = 0 := by
  suffices H : ∀ (n : ℕ) (l : List R), l.length = n →
      inclusionExclusion (0 : ContextField R A) l = 0 from
    fun l => H l.length l rfl
  intro n
  induction n with
  | zero =>
    intro l hl
    rw [List.length_eq_zero_iff.mp hl]
    simp [inclusionExclusion]
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp at hl
    | cons a l =>
      have hl' : l.length = n := by simpa using hl
      rw [inclusionExclusion, ih l hl', ih (l.map (· ⊓ a)) (by simpa using hl')]
      simp

theorem inclusionExclusion_add (K K' : ContextField R A) :
    ∀ l : List R, inclusionExclusion (K + K') l
      = inclusionExclusion K l + inclusionExclusion K' l := by
  suffices H : ∀ (n : ℕ) (l : List R), l.length = n →
      inclusionExclusion (K + K') l
        = inclusionExclusion K l + inclusionExclusion K' l from
    fun l => H l.length l rfl
  intro n
  induction n with
  | zero =>
    intro l hl
    rw [List.length_eq_zero_iff.mp hl]
    simp [inclusionExclusion]
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp at hl
    | cons a l =>
      have hl' : l.length = n := by simpa using hl
      simp only [inclusionExclusion]
      rw [ih l hl', ih (l.map (· ⊓ a)) (by simpa using hl')]
      simp only [Pi.add_apply]
      abel

/-- The hierarchy defect operator, packaged as an additive
homomorphism. -/
def defectFamHom : ContextField R A →+ (R → List R → A) where
  toFun K := fun a l => defectFam K a l
  map_zero' := by
    funext a l
    simp [defectFam, inclusionExclusion_zero]
  map_add' K K' := by
    funext a l
    simp only [defectFam, inclusionExclusion_add, Pi.add_apply]
    abel

/-- The gauge of the whole hierarchy: fields with vanishing
inclusion–exclusion defect at every arity. -/
def gaugeFam (R A : Type*) [Lattice R] [AddCommGroup A] :
    AddSubgroup (ContextField R A) :=
  defectFamHom.ker

theorem mem_gaugeFam_iff {K : ContextField R A} :
    K ∈ gaugeFam R A ↔ ∀ (a : R) (l : List R), defectFam K a l = 0 := by
  rw [gaugeFam, AddMonoidHom.mem_ker]
  constructor
  · exact fun h a l => congrFun (congrFun h a) l
  · intro h
    funext a l
    exact h a l

/-! ### Saturation at every order -/

/-- Binary blindness extends to finite joins: fields in the order-≤3
gauge do not separate any finite distributivity-defect interval. -/
theorem supFam_inf_apply_eq_of_mem_gauge3 {K : ContextField R A}
    (hK : K ∈ gauge3 R A) :
    ∀ (l : List R) (a c : R),
      K (supFam a l ⊓ c) = K (supFam (a ⊓ c) (l.map (· ⊓ c))) := by
  have h2 := (mem_gauge3_iff.mp hK).1
  have hG := apply_eq_of_mem_gauge3 hK
  have hval : ∀ x y : R, K (x ⊔ y) = K x + K y - K (x ⊓ y) := fun x y => by
    have h := h2 x y
    rw [defect_def] at h
    exact (sub_eq_zero.mp h).symm
  have hA : ∀ y S c : R, K ((y ⊔ S) ⊓ c) = K (y ⊓ c) + K (S ⊓ c) - K ((y ⊓ S) ⊓ c) := by
    intro y S c
    rw [hG y S c, hval (y ⊓ c) (S ⊓ c),
      show (y ⊓ c) ⊓ (S ⊓ c) = (y ⊓ S) ⊓ c from by
        rw [inf_assoc y c, inf_comm c (S ⊓ c), inf_assoc S c, inf_idem, ← inf_assoc]]
  suffices H : ∀ (n : ℕ) (l : List R), l.length = n → ∀ a c : R,
      K (supFam a l ⊓ c) = K (supFam (a ⊓ c) (l.map (· ⊓ c))) from
    fun l a c => H l.length l rfl a c
  intro n
  induction n with
  | zero =>
    intro l hl a c
    rw [List.length_eq_zero_iff.mp hl]
    rfl
  | succ n ih =>
    intro l hl a c
    cases l with
    | nil => simp at hl
    | cons b l =>
      have hl' : l.length = n := by simpa using hl
      have lhs1 : K (supFam a (b :: l) ⊓ c)
          = K (b ⊓ c) + K (supFam a l ⊓ c) - K ((b ⊓ supFam a l) ⊓ c) :=
        hA b (supFam a l) c
      have rhs1 : K (supFam (a ⊓ c) ((b :: l).map (· ⊓ c)))
          = K (b ⊓ c) + K (supFam (a ⊓ c) (l.map (· ⊓ c)))
            - K ((b ⊓ c) ⊓ supFam (a ⊓ c) (l.map (· ⊓ c))) :=
        hval (b ⊓ c) (supFam (a ⊓ c) (l.map (· ⊓ c)))
      have e1 : K (supFam a l ⊓ c) = K (supFam (a ⊓ c) (l.map (· ⊓ c))) :=
        ih l hl' a c
      have e2 : (b ⊓ supFam a l) ⊓ c = supFam a l ⊓ (b ⊓ c) := by
        rw [inf_comm b, inf_assoc]
      have e3 : K (supFam a l ⊓ (b ⊓ c))
          = K (supFam (a ⊓ (b ⊓ c)) (l.map (· ⊓ (b ⊓ c)))) :=
        ih l hl' a (b ⊓ c)
      have e4 : (b ⊓ c) ⊓ supFam (a ⊓ c) (l.map (· ⊓ c))
          = supFam (a ⊓ c) (l.map (· ⊓ c)) ⊓ (b ⊓ c) := inf_comm _ _
      have e5 : K (supFam (a ⊓ c) (l.map (· ⊓ c)) ⊓ (b ⊓ c))
          = K (supFam ((a ⊓ c) ⊓ (b ⊓ c))
              ((l.map (· ⊓ c)).map (· ⊓ (b ⊓ c)))) :=
        ih (l.map (· ⊓ c)) (by simpa using hl') (a ⊓ c) (b ⊓ c)
      have e6 : supFam ((a ⊓ c) ⊓ (b ⊓ c)) ((l.map (· ⊓ c)).map (· ⊓ (b ⊓ c)))
          = supFam (a ⊓ (b ⊓ c)) (l.map (· ⊓ (b ⊓ c))) := by
        rw [List.map_map,
          show (a ⊓ c) ⊓ (b ⊓ c) = a ⊓ (b ⊓ c) from by
            rw [inf_assoc a c, inf_eq_right.mpr inf_le_right],
          show ((· ⊓ (b ⊓ c)) ∘ (· ⊓ c) : R → R) = (· ⊓ (b ⊓ c)) from
            funext fun x => by
              simp only [Function.comp_apply]
              rw [inf_assoc, inf_eq_right.mpr inf_le_right]]
      rw [lhs1, rhs1, e1, e2, e3, e4, e5, e6]

/-- Saturation at every order: a field in the order-≤3 gauge has
vanishing inclusion–exclusion defect at every arity, on every lattice. -/
theorem defectFam_eq_zero_of_mem_gauge3 {K : ContextField R A}
    (hK : K ∈ gauge3 R A) :
    ∀ (l : List R) (a : R), defectFam K a l = 0 := by
  have h2 := (mem_gauge3_iff.mp hK).1
  have hblind := supFam_inf_apply_eq_of_mem_gauge3 hK
  suffices H : ∀ (n : ℕ) (l : List R), l.length = n → ∀ a : R,
      defectFam K a l = 0 from fun l a => H l.length l rfl a
  intro n
  induction n with
  | zero =>
    intro l hl a
    rw [List.length_eq_zero_iff.mp hl, defectFam_nil]
  | succ n ih =>
    intro l hl a
    cases l with
    | nil => simp at hl
    | cons b l =>
      have hl' : l.length = n := by simpa using hl
      rw [defectFam_cons, ih l hl' b, h2 (supFam b l) a,
        ih (l.map (· ⊓ a)) (by simpa using hl') (b ⊓ a), hblind l b a]
      abel

/-- Order 3 is the final refinement: the gauge of the whole
inclusion–exclusion hierarchy is the order-≤3 gauge, on every lattice
and every target. -/
theorem gaugeFam_eq_gauge3 : gaugeFam R A = gauge3 R A := by
  refine le_antisymm (fun K hK => ?_) fun K hK =>
    mem_gaugeFam_iff.mpr fun a l => defectFam_eq_zero_of_mem_gauge3 hK l a
  have h := mem_gaugeFam_iff.mp hK
  refine mem_gauge3_iff.mpr ⟨fun a b => ?_, fun a b c => ?_⟩
  · rw [← defectFam_pair K a b]
    exact h b [a]
  · rw [← defectFam_triple K a b c]
    exact h c [b, a]

end Descent
