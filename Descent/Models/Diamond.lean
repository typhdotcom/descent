import Descent.Core.Hierarchy
import Descent.Core.Higher
import Mathlib.Data.Fintype.Pi

/-!
# The diamond

`M₃`: bottom, three incomparable atoms, top. The smallest modular
non-distributive lattice, and the sharpness witness for order separation:
the height field is a pairwise valuation --- its defect observable
vanishes identically, so it is defect-equivalent to zero --- yet its
order-3 defect at the atom triple is `1`. Off distributivity the order-3
defect does not descend through the pairwise gauge, and third-order
information is genuinely new: the surviving equivalence is joint
pairwise-and-triple defect equality, not pairwise alone.
-/

namespace Descent

/-- The five-element modular non-distributive lattice `M₃`. -/
inductive Diamond : Type
  | bot | x | y | z | top
deriving DecidableEq

namespace Diamond

instance : Fintype Diamond :=
  ⟨{bot, x, y, z, top}, fun a => by cases a <;> decide⟩

/-- Meet: distinct middle elements meet at the bottom. -/
def infD : Diamond → Diamond → Diamond
  | bot, _ => bot
  | _, bot => bot
  | top, q => q
  | p, top => p
  | p, q => if p = q then p else bot

/-- Join: distinct middle elements join at the top. -/
def supD : Diamond → Diamond → Diamond
  | top, _ => top
  | _, top => top
  | bot, q => q
  | p, bot => p
  | p, q => if p = q then p else top

instance : Lattice Diamond where
  le p q := infD p q = p
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  inf := infD
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  sup := supD
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : DecidableLE Diamond := fun p q =>
  inferInstanceAs (Decidable (infD p q = p))

/-- The atom triple is nondegenerate: pairwise incomparable. -/
theorem not_comparable_x_y : ¬Comparable x y := by decide

theorem not_comparable_x_z : ¬Comparable x z := by decide

theorem not_comparable_y_z : ¬Comparable y z := by decide

/-- The height field on the diamond. -/
def height : ContextField Diamond ℤ
  | bot => 0
  | top => 2
  | _ => 1

/-- The height field is a pairwise valuation: its defect observable
vanishes identically. -/
theorem isValuation_height : IsValuation height := by
  show ∀ a b : Diamond, defect height a b = 0
  decide

/-- The diamond is not distributive, and the order-3 defect knows: the
height field is a pairwise valuation with order-3 defect `1` at the atom
triple. -/
theorem defect3_height : defect3 height x y z = 1 := by decide

/-- The height field is defect-equivalent to zero. -/
theorem defectEquiv_height_zero :
    DefectEquiv height (0 : ContextField Diamond ℤ) := by
  show defect height = defect (0 : ContextField Diamond ℤ)
  decide

/-- Off distributivity the order-3 defect does not descend through the
pairwise gauge: two defect-equivalent fields with different order-3
defects. -/
theorem exists_defectEquiv_defect3_ne :
    ∃ K K' : ContextField Diamond ℤ,
      DefectEquiv K K' ∧ defect3 K ≠ defect3 K' := by
  refine ⟨height, 0, defectEquiv_height_zero, ?_⟩
  intro h
  have h0 := congrFun (congrFun (congrFun h x) y) z
  rw [defect3_height] at h0
  simp [defect3_zero] at h0

/-- On the diamond the order-≤3 gauge is strictly below the pairwise
gauge: the height valuation is invisible to pairwise observation and
visible to cumulative observation. -/
theorem gauge3_lt_gauge : gauge3 Diamond ℤ < gauge Diamond ℤ := by
  rw [SetLike.lt_iff_le_and_exists]
  refine ⟨inf_le_left, height, mem_gauge_iff.mpr isValuation_height, fun h => ?_⟩
  have h3 := (mem_gauge3_iff.mp h).2 x y z
  rw [defect3_height] at h3
  exact one_ne_zero h3

/-- Observation through order 3 is strictly finer on the diamond: the
height field and zero share the pairwise observable. -/
theorem observable_mk_height_eq :
    Observable.mk height = Observable.mk (0 : ContextField Diamond ℤ) :=
  Observable.mk_eq_mk.mpr defectEquiv_height_zero

/-- ... and the cumulative observable separates them. -/
theorem observable3_mk_height_ne :
    Observable3.mk height ≠ Observable3.mk (0 : ContextField Diamond ℤ) := by
  rw [Ne, Observable3.mk_eq_mk]
  rintro ⟨-, h3⟩
  have h0 := congrFun (congrFun (congrFun h3 x) y) z
  rw [defect3_height] at h0
  simp [defect3_zero] at h0

/-! ### The final observable, classified -/

section Classification

variable {A : Type*} [AddCommGroup A]

/-- The order-≤3 gauge of the diamond is exactly the constant fields, for
every additive commutative group: the pair valuations at the atom triple
equalize the atoms, and the vanishing order-3 defect pins them to the
bottom. -/
theorem mem_gauge3_iff_exists_const {K : ContextField Diamond A} :
    K ∈ gauge3 Diamond A ↔ ∃ c : A, K = ContextField.const Diamond c := by
  constructor
  · intro hK
    obtain ⟨hval, h3⟩ := mem_gauge3_iff.mp hK
    have h1 := hval x y
    have h2 := hval x z
    have h3' := hval y z
    have h4 := h3 x y z
    rw [defect_def, show (x ⊓ y : Diamond) = bot from by decide,
      show (x ⊔ y : Diamond) = top from by decide] at h1
    rw [defect_def, show (x ⊓ z : Diamond) = bot from by decide,
      show (x ⊔ z : Diamond) = top from by decide] at h2
    rw [defect_def, show (y ⊓ z : Diamond) = bot from by decide,
      show (y ⊔ z : Diamond) = top from by decide] at h3'
    rw [defect3_def, show (x ⊓ y ⊓ z : Diamond) = bot from by decide,
      show (x ⊓ y : Diamond) = bot from by decide,
      show (x ⊓ z : Diamond) = bot from by decide,
      show (y ⊓ z : Diamond) = bot from by decide,
      show (x ⊔ y ⊔ z : Diamond) = top from by decide] at h4
    have hx : K x = K bot := by
      have h := congrArg₂ (· - ·) h4 h3'
      rw [sub_zero] at h
      have h' : K x - K bot = 0 := by
        rw [← h]
        abel
      exact sub_eq_zero.mp h'
    have hy : K y = K bot := by
      have h := congrArg₂ (· - ·) h4 h2
      rw [sub_zero] at h
      have h' : K y - K bot = 0 := by
        rw [← h]
        abel
      exact sub_eq_zero.mp h'
    have hz : K z = K bot := by
      have h := congrArg₂ (· - ·) h4 h1
      rw [sub_zero] at h
      have h' : K z - K bot = 0 := by
        rw [← h]
        abel
      exact sub_eq_zero.mp h'
    have ht : K top = K bot := by
      rw [hx, hy] at h1
      have h' : K bot - K top = 0 := by
        rw [← h1]
        abel
      exact (sub_eq_zero.mp h').symm
    refine ⟨K bot, funext fun p => ?_⟩
    cases p
    · rw [ContextField.const_apply]
    · rw [ContextField.const_apply]
      exact hx
    · rw [ContextField.const_apply]
      exact hy
    · rw [ContextField.const_apply]
      exact hz
    · rw [ContextField.const_apply]
      exact ht
  · rintro ⟨c, rfl⟩
    refine mem_gauge3_iff.mpr ⟨ContextField.isValuation_const c, fun a b c' => ?_⟩
    rw [defect3_const]
    rfl

/-- Two diamond fields share the final observable exactly when their
difference is constant. -/
theorem observable3_mk_eq_mk_iff {K K' : ContextField Diamond A} :
    Observable3.mk K = Observable3.mk K'
      ↔ ∃ c : A, K - K' = ContextField.const Diamond c := by
  rw [Observable3.mk_eq_mk, defect3Equiv_iff_sub_mem_gauge3,
    mem_gauge3_iff_exists_const]

/-- The equality criterion: the observable class and the value at any one
context determine the field. -/
theorem eq_of_mk_eq_of_apply_eq {K K' : ContextField Diamond A} (p : Diamond)
    (h : Observable3.mk K = Observable3.mk K') (hp : K p = K' p) : K = K' := by
  obtain ⟨c, hc⟩ := observable3_mk_eq_mk_iff.mp h
  have h0 := congrFun hc p
  rw [Pi.sub_apply, ContextField.const_apply, hp, sub_self] at h0
  rw [← h0, show ContextField.const Diamond (0 : A) = 0 from funext fun _ => rfl]
    at hc
  exact sub_eq_zero.mp hc

/-- One-point normalization: every observable class contains exactly one
field normalized to zero at a chosen context. -/
theorem existsUnique_mk_eq_and_apply_eq_zero (p : Diamond)
    (K : ContextField Diamond A) :
    ∃! K₀ : ContextField Diamond A,
      Observable3.mk K₀ = Observable3.mk K ∧ K₀ p = 0 := by
  have hw1 : Observable3.mk (K - ContextField.const Diamond (K p))
      = Observable3.mk K := by
    rw [observable3_mk_eq_mk_iff]
    refine ⟨-K p, funext fun q => ?_⟩
    simp only [Pi.sub_apply, ContextField.const_apply]
    abel
  have hw2 : (K - ContextField.const Diamond (K p)) p = 0 := by
    simp only [Pi.sub_apply, ContextField.const_apply, sub_self]
  refine ⟨K - ContextField.const Diamond (K p), ⟨hw1, hw2⟩, ?_⟩
  rintro K₁ ⟨h1, h2⟩
  exact eq_of_mk_eq_of_apply_eq p (h1.trans hw1.symm) (by rw [h2, hw2])

/-! ### Sparse reconstruction: the canonical datum -/

/-- The canonical Diamond datum: the three pairwise defects and the
order-3 defect at the atom triple. -/
def canonicalDatum (K : ContextField Diamond A) : A × A × A × A :=
  (defect K x y, defect K x z, defect K y z, defect3 K x y z)

private theorem pair_cases :
    ∀ a b : Diamond, Comparable a b ∨
      (a = x ∧ b = y) ∨ (a = y ∧ b = x) ∨ (a = x ∧ b = z) ∨ (a = z ∧ b = x) ∨
      (a = y ∧ b = z) ∨ (a = z ∧ b = y) := by
  decide

private theorem triple_cases :
    ∀ a b c : Diamond,
      (Comparable a b ∨ Comparable a c ∨ Comparable b c) ∨
      ((a = x ∧ b = y ∧ c = z) ∨ (a = x ∧ b = z ∧ c = y) ∨
        (a = y ∧ b = x ∧ c = z) ∨ (a = y ∧ b = z ∧ c = x) ∨
        (a = z ∧ b = x ∧ c = y) ∨ (a = z ∧ b = y ∧ c = x)) := by
  decide

/-- Vanishing of the four coordinates puts a field in the order-≤3
gauge: the atom triple carries all nondegenerate data of the diamond. -/
theorem mem_gauge3_of {K : ContextField Diamond A} (hp : defect K x y = 0)
    (hq : defect K x z = 0) (hr : defect K y z = 0)
    (hs : defect3 K x y z = 0) : K ∈ gauge3 Diamond A := by
  have hval : IsValuation K := by
    intro a b
    rcases pair_cases a b with hc | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hc.defect_eq_zero K
    · exact hp
    · rw [defect_comm]
      exact hp
    · exact hq
    · rw [defect_comm]
      exact hq
    · exact hr
    · rw [defect_comm]
      exact hr
  refine mem_gauge3_iff.mpr ⟨hval, fun a b c => ?_⟩
  rcases triple_cases a b c with (hab | hac | hbc) | hperm
  · rcases hab with h | h
    · rw [defect3_of_le K h]
      exact hval _ _
    · rw [defect3_comm_left, defect3_of_le K h]
      exact hval _ _
  · rcases hac with h | h
    · rw [defect3_comm_right, defect3_of_le K h]
      exact hval _ _
    · rw [defect3_comm_right, defect3_comm_left, defect3_of_le K h]
      exact hval _ _
  · rcases hbc with h | h
    · rw [defect3_comm_left, defect3_comm_right, defect3_of_le K h]
      exact hval _ _
    · rw [defect3_comm_left, defect3_comm_right, defect3_comm_left,
        defect3_of_le K h]
      exact hval _ _
  · rcases hperm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact hs
    · rw [defect3_comm_right]
      exact hs
    · rw [defect3_comm_left]
      exact hs
    · rw [defect3_comm_right, defect3_comm_left]
      exact hs
    · rw [defect3_comm_left, defect3_comm_right]
      exact hs
    · rw [defect3_comm_left, defect3_comm_right, defect3_comm_left]
      exact hs

/-- The four coordinates are complete: equality of the canonical datum is
equality in the final observable. -/
theorem canonicalDatum_eq_iff {K K' : ContextField Diamond A} :
    canonicalDatum K = canonicalDatum K'
      ↔ Observable3.mk K = Observable3.mk K' := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ :
        defect K x y = defect K' x y ∧ defect K x z = defect K' x z ∧
          defect K y z = defect K' y z ∧ defect3 K x y z = defect3 K' x y z := by
      simpa [canonicalDatum, Prod.ext_iff] using h
    rw [Observable3.mk_eq_mk, defect3Equiv_iff_sub_mem_gauge3]
    refine mem_gauge3_of ?_ ?_ ?_ ?_
    · rw [defect_sub, h1, sub_self]
    · rw [defect_sub, h2, sub_self]
    · rw [defect_sub, h3, sub_self]
    · rw [defect3_sub, h4, sub_self]
  · intro h
    obtain ⟨h2eq, h3eq⟩ := Observable3.mk_eq_mk.mp h
    rw [canonicalDatum, canonicalDatum,
      show defect K = defect K' from h2eq, h3eq]

/-- Hence the canonical datum determines every finite-family defect. -/
theorem defectFam_eq_of_canonicalDatum_eq {K K' : ContextField Diamond A}
    (h : canonicalDatum K = canonicalDatum K') (a : Diamond) (l : List Diamond) :
    defectFam K a l = defectFam K' a l := by
  have hm : K - K' ∈ gauge3 Diamond A := by
    rw [← defect3Equiv_iff_sub_mem_gauge3]
    exact Observable3.mk_eq_mk.mp (canonicalDatum_eq_iff.mp h)
  have h0 := defectFam_eq_zero_of_mem_gauge3 hm l a
  have hsub : defectFam (K - K') a l = defectFam K a l - defectFam K' a l :=
    congrFun (congrFun (defectFamHom.map_sub K K') a) l
  rw [h0] at hsub
  exact (sub_eq_zero.mp hsub.symm)

/-- The explicit normalized inverse: the zero-at-bottom field with
prescribed canonical datum. -/
def reconstruct (p q r s : A) : ContextField Diamond A
  | bot => 0
  | x => s - r
  | y => s - q
  | z => s - p
  | top => s + s - p - q - r

@[simp]
theorem defect_reconstruct_xy (p q r s : A) :
    defect (reconstruct p q r s) x y = p := by
  rw [defect_def, show (x ⊓ y : Diamond) = bot from by decide,
    show (x ⊔ y : Diamond) = top from by decide]
  show (s - r) + (s - q) - 0 - (s + s - p - q - r) = p
  abel

@[simp]
theorem defect_reconstruct_xz (p q r s : A) :
    defect (reconstruct p q r s) x z = q := by
  rw [defect_def, show (x ⊓ z : Diamond) = bot from by decide,
    show (x ⊔ z : Diamond) = top from by decide]
  show (s - r) + (s - p) - 0 - (s + s - p - q - r) = q
  abel

@[simp]
theorem defect_reconstruct_yz (p q r s : A) :
    defect (reconstruct p q r s) y z = r := by
  rw [defect_def, show (y ⊓ z : Diamond) = bot from by decide,
    show (y ⊔ z : Diamond) = top from by decide]
  show (s - q) + (s - p) - 0 - (s + s - p - q - r) = r
  abel

@[simp]
theorem defect3_reconstruct (p q r s : A) :
    defect3 (reconstruct p q r s) x y z = s := by
  rw [defect3_def, show (x ⊓ y ⊓ z : Diamond) = bot from by decide,
    show (x ⊓ y : Diamond) = bot from by decide,
    show (x ⊓ z : Diamond) = bot from by decide,
    show (y ⊓ z : Diamond) = bot from by decide,
    show (x ⊔ y ⊔ z : Diamond) = top from by decide]
  show (s - r) + (s - q) + (s - p) - 0 - 0 - 0 + 0 - (s + s - p - q - r) = s
  abel

/-- Round trip one: the inverse realizes every quadruple in `A⁴`. -/
theorem canonicalDatum_reconstruct (p q r s : A) :
    canonicalDatum (reconstruct p q r s) = (p, q, r, s) := by
  simp [canonicalDatum]

/-- Round trip two: adjoining the bottom value to the canonical datum
reconstructs the entire field. -/
theorem reconstruct_canonicalDatum_add_const (K : ContextField Diamond A) :
    reconstruct (defect K x y) (defect K x z) (defect K y z)
        (defect3 K x y z)
      + ContextField.const Diamond (K bot) = K := by
  have hP : defect K x y = K x + K y - K bot - K top := by
    rw [defect_def, show (x ⊓ y : Diamond) = bot from by decide,
      show (x ⊔ y : Diamond) = top from by decide]
  have hQ : defect K x z = K x + K z - K bot - K top := by
    rw [defect_def, show (x ⊓ z : Diamond) = bot from by decide,
      show (x ⊔ z : Diamond) = top from by decide]
  have hR : defect K y z = K y + K z - K bot - K top := by
    rw [defect_def, show (y ⊓ z : Diamond) = bot from by decide,
      show (y ⊔ z : Diamond) = top from by decide]
  have hS : defect3 K x y z
      = K x + K y + K z - K bot - K bot - K bot + K bot - K top := by
    rw [defect3_def, show (x ⊓ y ⊓ z : Diamond) = bot from by decide,
      show (x ⊓ y : Diamond) = bot from by decide,
      show (x ⊓ z : Diamond) = bot from by decide,
      show (y ⊓ z : Diamond) = bot from by decide,
      show (x ⊔ y ⊔ z : Diamond) = top from by decide]
  funext u
  cases u
  · show (0 : A) + K bot = K bot
    rw [zero_add]
  · show defect3 K x y z - defect K y z + K bot = K x
    rw [hS, hR]
    abel
  · show defect3 K x y z - defect K x z + K bot = K y
    rw [hS, hQ]
    abel
  · show defect3 K x y z - defect K x y + K bot = K z
    rw [hS, hP]
    abel
  · show defect3 K x y z + defect3 K x y z - defect K x y - defect K x z
        - defect K y z + K bot = K top
    rw [hS, hP, hQ, hR]
    abel

/-- The inverse lands in the class it reconstructs. -/
theorem observable3_mk_reconstruct (K : ContextField Diamond A) :
    Observable3.mk (reconstruct (defect K x y) (defect K x z)
        (defect K y z) (defect3 K x y z))
      = Observable3.mk K := by
  rw [observable3_mk_eq_mk_iff]
  refine ⟨-K bot, ?_⟩
  have h := reconstruct_canonicalDatum_add_const K
  funext u
  have hu := congrFun h u
  simp only [Pi.add_apply, ContextField.const_apply] at hu
  simp only [Pi.sub_apply, ContextField.const_apply]
  rw [← hu]
  abel

/-! ### Irredundancy: deleting any coordinate destroys completeness -/

/-- Without `s`: two fields agreeing in `p, q, r` with different final
observables. -/
theorem exists_pqr_eq_mk_ne [Nontrivial A] :
    ∃ K K' : ContextField Diamond A,
      defect K x y = defect K' x y ∧ defect K x z = defect K' x z ∧
        defect K y z = defect K' y z ∧
        Observable3.mk K ≠ Observable3.mk K' := by
  obtain ⟨e, he⟩ := exists_ne (0 : A)
  refine ⟨0, reconstruct 0 0 0 e, by simp, by simp, by simp, fun hmk => ?_⟩
  have hcomp := congrArg (fun t => t.2.2.2) (canonicalDatum_eq_iff.mpr hmk)
  simp [canonicalDatum] at hcomp
  exact he hcomp.symm

/-- Without `p`: two fields agreeing in `q, r, s` with different final
observables. -/
theorem exists_qrs_eq_mk_ne [Nontrivial A] :
    ∃ K K' : ContextField Diamond A,
      defect K x z = defect K' x z ∧ defect K y z = defect K' y z ∧
        defect3 K x y z = defect3 K' x y z ∧
        Observable3.mk K ≠ Observable3.mk K' := by
  obtain ⟨e, he⟩ := exists_ne (0 : A)
  refine ⟨0, reconstruct e 0 0 0, by simp, by simp, by simp, fun hmk => ?_⟩
  have hcomp := congrArg (fun t => t.1) (canonicalDatum_eq_iff.mpr hmk)
  simp [canonicalDatum] at hcomp
  exact he hcomp.symm

/-- Without `q`: two fields agreeing in `p, r, s` with different final
observables. -/
theorem exists_prs_eq_mk_ne [Nontrivial A] :
    ∃ K K' : ContextField Diamond A,
      defect K x y = defect K' x y ∧ defect K y z = defect K' y z ∧
        defect3 K x y z = defect3 K' x y z ∧
        Observable3.mk K ≠ Observable3.mk K' := by
  obtain ⟨e, he⟩ := exists_ne (0 : A)
  refine ⟨0, reconstruct 0 e 0 0, by simp, by simp, by simp, fun hmk => ?_⟩
  have hcomp := congrArg (fun t => t.2.1) (canonicalDatum_eq_iff.mpr hmk)
  simp [canonicalDatum] at hcomp
  exact he hcomp.symm

/-- Without `r`: two fields agreeing in `p, q, s` with different final
observables. -/
theorem exists_pqs_eq_mk_ne [Nontrivial A] :
    ∃ K K' : ContextField Diamond A,
      defect K x y = defect K' x y ∧ defect K x z = defect K' x z ∧
        defect3 K x y z = defect3 K' x y z ∧
        Observable3.mk K ≠ Observable3.mk K' := by
  obtain ⟨e, he⟩ := exists_ne (0 : A)
  refine ⟨0, reconstruct 0 0 e 0, by simp, by simp, by simp, fun hmk => ?_⟩
  have hcomp := congrArg (fun t => t.2.2.1) (canonicalDatum_eq_iff.mpr hmk)
  simp [canonicalDatum] at hcomp
  exact he hcomp.symm

end Classification

end Diamond

end Descent
