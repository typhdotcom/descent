import Descent.Core.Gauge

/-!
# Restricted observation

The gauge theorem of `Descent.Core.Gauge` settles complete observation: the
full pairwise defect field determines exactly the class `[K]`. The inverse
problem proper begins when observation is restricted. For a family `S` of
comparison squares, `defectOn S K` is the datum an observer of `S` receives,
`gaugeOn S A` is the subgroup of fields that observer cannot distinguish from
`0`, and `S` is `ObservationallyComplete` when restricted observation
separates exactly the classes complete observation separates:
`gaugeOn S A = gauge R A`.

Completeness is relative to the pairwise gauge, not absolute. On a context
system whose gauge is everything --- a chain --- every family, including `∅`,
is complete.
-/

namespace Descent

variable {R A : Type*} [Lattice R] [AddCommGroup A]

/-- The pairwise defect datum observed on the family `S` of comparison
squares. -/
def defectOn (S : Set (R × R)) (K : ContextField R A) : S → A :=
  fun p => defect K p.val.1 p.val.2

@[simp]
theorem defectOn_apply (S : Set (R × R)) (K : ContextField R A) (p : S) :
    defectOn S K p = defect K p.val.1 p.val.2 :=
  rfl

/-- Restricted observation, packaged as an additive homomorphism. -/
def defectOnHom (S : Set (R × R)) (A : Type*) [AddCommGroup A] :
    ContextField R A →+ (S → A) where
  toFun := defectOn S
  map_zero' := by funext p; simp
  map_add' K K' := by funext p; simp [defect_add]

@[simp]
theorem defectOnHom_apply (S : Set (R × R)) (K : ContextField R A) :
    defectOnHom S A K = defectOn S K :=
  rfl

/-- The fields invisible to an observer of `S`: the kernel of restricted
observation. -/
def gaugeOn (S : Set (R × R)) (A : Type*) [AddCommGroup A] :
    AddSubgroup (ContextField R A) :=
  (defectOnHom S A).ker

theorem mem_gaugeOn_iff {S : Set (R × R)} {K : ContextField R A} :
    K ∈ gaugeOn S A ↔ ∀ p ∈ S, defect K p.1 p.2 = 0 := by
  constructor
  · intro h p hp
    exact congrFun (AddMonoidHom.mem_ker.mp h) ⟨p, hp⟩
  · intro h
    refine AddMonoidHom.mem_ker.mpr ?_
    funext p
    exact h p.val p.property

/-- Restriction observes less: the full gauge is invisible to every family. -/
theorem gauge_le_gaugeOn (S : Set (R × R)) : gauge R A ≤ gaugeOn S A :=
  fun _K hK => mem_gaugeOn_iff.mpr fun p _ => mem_gauge_iff.mp hK p.1 p.2

theorem gaugeOn_antitone {S T : Set (R × R)} (h : S ⊆ T) :
    gaugeOn T A ≤ gaugeOn S A :=
  fun _K hK => mem_gaugeOn_iff.mpr fun p hp => mem_gaugeOn_iff.mp hK p (h hp)

@[simp]
theorem gaugeOn_univ : gaugeOn (Set.univ : Set (R × R)) A = gauge R A := by
  ext K
  rw [mem_gaugeOn_iff, mem_gauge_iff]
  exact ⟨fun h a b => h (a, b) (Set.mem_univ _), fun h p _ => h p.1 p.2⟩

@[simp]
theorem gaugeOn_empty : gaugeOn (∅ : Set (R × R)) A = ⊤ := by
  ext K
  simp [mem_gaugeOn_iff]

theorem gaugeOn_union (S T : Set (R × R)) :
    gaugeOn (S ∪ T) A = gaugeOn S A ⊓ gaugeOn T A := by
  ext K
  simp only [AddSubgroup.mem_inf, mem_gaugeOn_iff]
  constructor
  · exact fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h₁, h₂⟩ p (hp | hp)
    · exact h₁ p hp
    · exact h₂ p hp

/-- Observation is symmetric: a square and its transpose carry the same
datum. -/
theorem gaugeOn_image_swap (S : Set (R × R)) :
    gaugeOn (Prod.swap '' S) A = gaugeOn S A := by
  ext K
  simp only [mem_gaugeOn_iff]
  constructor
  · intro h p hp
    have := h p.swap ⟨p, hp, rfl⟩
    rwa [Prod.fst_swap, Prod.snd_swap, defect_comm] at this
  · rintro h p ⟨q, hq, rfl⟩
    rw [Prod.fst_swap, Prod.snd_swap, defect_comm]
    exact h q hq

/-- Degenerate squares carry no datum: a family of comparable pairs sees
nothing. -/
theorem gaugeOn_eq_top_of_comparable {S : Set (R × R)}
    (h : ∀ p ∈ S, Comparable p.1 p.2) : gaugeOn S A = ⊤ :=
  eq_top_iff.mpr fun K _ => mem_gaugeOn_iff.mpr fun p hp => (h p hp).defect_eq_zero K

/-- Restricted observation descends to the observable quotient: it consumes
strictly less than the full defect field, never more. -/
def Observable.defectOn (S : Set (R × R)) : Observable R A → (S → A) :=
  Quotient.lift (Descent.defectOn S) fun K K' (h : DefectEquiv K K') =>
    funext fun p => congrFun (congrFun h p.val.1) p.val.2

@[simp]
theorem Observable.defectOn_mk (S : Set (R × R)) (K : ContextField R A) :
    Observable.defectOn S (Observable.mk K) = Descent.defectOn S K :=
  rfl

/-- `S` is observationally complete when observing `S` separates exactly the
classes that complete pairwise observation separates. -/
def ObservationallyComplete (S : Set (R × R)) (A : Type*) [AddCommGroup A] : Prop :=
  gaugeOn S A = gauge R A

theorem observationallyComplete_iff_le {S : Set (R × R)} :
    ObservationallyComplete S A ↔ gaugeOn S A ≤ gauge R A :=
  ⟨le_of_eq, fun h => le_antisymm h (gauge_le_gaugeOn S)⟩

theorem observationallyComplete_univ :
    ObservationallyComplete (Set.univ : Set (R × R)) A :=
  gaugeOn_univ

/-- Completeness survives enlarging the observed family. -/
theorem ObservationallyComplete.mono {S T : Set (R × R)} (hST : S ⊆ T)
    (h : ObservationallyComplete S A) : ObservationallyComplete T A :=
  observationallyComplete_iff_le.mpr <|
    (gaugeOn_antitone hST).trans (observationallyComplete_iff_le.mp h)

/-- The defect field is carried entirely by the incomparable pairs: any
family containing them is complete. -/
theorem observationallyComplete_of_incomparable_subset {S : Set (R × R)}
    (h : {p : R × R | ¬Comparable p.1 p.2} ⊆ S) :
    ObservationallyComplete S A := by
  refine observationallyComplete_iff_le.mpr fun K hK => mem_gauge_iff.mpr fun a b => ?_
  by_cases hab : Comparable a b
  · exact hab.defect_eq_zero K
  · exact mem_gaugeOn_iff.mp hK (a, b) (h hab)

/-- Observational completeness is exactly injectivity of the restricted datum
on the observable quotient: a complete family recovers `[K]`, and no family
recovers more. -/
theorem observationallyComplete_iff_injective {S : Set (R × R)} :
    ObservationallyComplete S A
      ↔ Function.Injective (Observable.defectOn S : Observable R A → S → A) := by
  constructor
  · intro h x y hxy
    induction x using Quotient.inductionOn with
    | _ K =>
      induction y using Quotient.inductionOn with
      | _ K' =>
        refine Observable.mk_eq_mk.mpr (defectEquiv_iff_sub_mem_gauge.mpr ?_)
        rw [← h]
        refine mem_gaugeOn_iff.mpr fun p hp => ?_
        have hpq : defect K p.1 p.2 = defect K' p.1 p.2 := congrFun hxy ⟨p, hp⟩
        rw [defect_sub, hpq, sub_self]
  · intro h
    refine observationallyComplete_iff_le.mpr fun K hK => ?_
    have h0 : Observable.defectOn S (Observable.mk K)
        = Observable.defectOn S (Observable.mk (0 : ContextField R A)) := by
      funext p
      simp only [Observable.defectOn_mk, defectOn_apply]
      rw [mem_gaugeOn_iff.mp hK p.val p.property]
      simp
    have hK0 : DefectEquiv K 0 := Observable.mk_eq_mk.mp (h h0)
    exact mem_gauge_iff.mpr
      (isValuation_iff_defect_eq_zero.mpr (Eq.trans hK0 defect_zero))

/-- On a complete family the restricted datum separates exactly the
defect-equivalence classes. -/
theorem ObservationallyComplete.defectOn_eq_iff {S : Set (R × R)}
    (h : ObservationallyComplete S A) {K K' : ContextField R A} :
    defectOn S K = defectOn S K' ↔ DefectEquiv K K' := by
  constructor
  · intro he
    exact Observable.mk_eq_mk.mp <| observationallyComplete_iff_injective.mp h <| by
      simpa only [Observable.defectOn_mk] using he
  · intro he
    funext p
    exact congrFun (congrFun he p.val.1) p.val.2

end Descent
