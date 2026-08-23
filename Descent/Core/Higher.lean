import Descent.Core.Cube
import Descent.Core.Gauge

/-!
# The order-3 defect and order separation

The raw order-3 mixed difference is not order-separated: on degenerate
cubes it retains lower-order data (`Descent.Models.Chain`). This file
isolates the higher-order content exactly.

`defect3 K a b c` is the failure of triple inclusion–exclusion:

    D₃(a,b,c) = K a + K b + K c
                - K (a ⊓ b) - K (a ⊓ c) - K (b ⊓ c)
                + K (a ⊓ b ⊓ c) - K (a ⊔ b ⊔ c).

The separation theorems:

* **degeneracy is face data**: on a degenerate triple the order-3 defect
  is a pairwise defect of the surviving pair --- never raw field data ---
  so it vanishes identically on chains;
* **isolation**: the raw order-3 mixed difference decomposes exactly into
  its three pairwise face defects, minus the order-3 defect, plus a named
  base-point residue; at the meet base the residue vanishes
  (`mixedDiff_triple_inf`). Subtracting faces from the raw cube is the
  order-separation datum, and what survives is `defect3`;
* **the exact gauge law**: `defect3` is additive in the field, so it is
  invariant under shifts by fields with vanishing order-3 defect. On a
  distributive lattice every pairwise valuation is such a field, the
  order-3 defect decomposes exactly into pairwise defects at derived
  squares (`defect3_decompose`), and hence descends through the pairwise
  gauge to the observable quotient (`Observable.defect3`): distributively,
  order 3 is an observable of the pairwise class, and carries nothing
  irreducible. Off distributivity descent fails
  (`Descent.Models.Diamond`), and the surviving equivalence is joint
  pairwise-and-triple defect equality.
-/

namespace Descent

section Lattice

variable {R A : Type*} [Lattice R] [AddCommGroup A]

/-- The order-3 defect of `K` on the comparison triple `a, b, c`: the
failure of triple inclusion–exclusion. -/
def defect3 (K : ContextField R A) (a b c : R) : A :=
  K a + K b + K c - K (a ⊓ b) - K (a ⊓ c) - K (b ⊓ c)
    + K (a ⊓ b ⊓ c) - K (a ⊔ b ⊔ c)

theorem defect3_def (K : ContextField R A) (a b c : R) :
    defect3 K a b c
      = K a + K b + K c - K (a ⊓ b) - K (a ⊓ c) - K (b ⊓ c)
        + K (a ⊓ b ⊓ c) - K (a ⊔ b ⊔ c) :=
  rfl

/-! ### Symmetry -/

theorem defect3_comm_left (K : ContextField R A) (a b c : R) :
    defect3 K a b c = defect3 K b a c := by
  simp only [defect3, inf_comm a b, sup_comm a b]
  abel

theorem defect3_comm_right (K : ContextField R A) (a b c : R) :
    defect3 K a b c = defect3 K a c b := by
  simp only [defect3, inf_comm b c, inf_right_comm a b c, sup_right_comm a b c]
  abel

/-! ### Algebra in the field -/

@[simp]
theorem defect3_zero : defect3 (0 : ContextField R A) = 0 := by
  funext a b c
  simp [defect3]

theorem defect3_add (K K' : ContextField R A) (a b c : R) :
    defect3 (K + K') a b c = defect3 K a b c + defect3 K' a b c := by
  simp only [defect3, Pi.add_apply]
  abel

theorem defect3_sub (K K' : ContextField R A) (a b c : R) :
    defect3 (K - K') a b c = defect3 K a b c - defect3 K' a b c := by
  simp only [defect3, Pi.sub_apply]
  abel

/-- The exact gauge law at order 3: shifting by any field with vanishing
order-3 defect moves nothing. -/
theorem defect3_add_of_eq_zero {G : ContextField R A}
    (hG : ∀ a b c, defect3 G a b c = 0) (K : ContextField R A) (a b c : R) :
    defect3 (K + G) a b c = defect3 K a b c := by
  rw [defect3_add, hG, add_zero]

/-! ### Degeneracy is face data -/

/-- On a degenerate triple the order-3 defect is the pairwise defect of
the surviving pair: no raw field data is retained. -/
theorem defect3_of_le (K : ContextField R A) {a b : R} (h : a ≤ b) (c : R) :
    defect3 K a b c = defect K b c := by
  simp only [defect3, defect_def, inf_eq_left.mpr h, sup_eq_right.mpr h]
  abel

theorem defect3_self (K : ContextField R A) (a c : R) :
    defect3 K a a c = defect K a c :=
  defect3_of_le K le_rfl c

/-! ### Isolation: the raw cube decomposes exactly -/

/-- The exact isolation identity at an arbitrary base: the raw order-3
mixed difference is its three pairwise face defects, minus the order-3
defect of the translated triple, plus the base-point residue. -/
theorem mixedDiff_triple_add_defect3 (K : ContextField R A) (a b c r : R) :
    mixedDiff [a, b, c] K r + defect3 K (r ⊔ a) (r ⊔ b) (r ⊔ c)
      = defect K (r ⊔ a) (r ⊔ b) + defect K (r ⊔ a) (r ⊔ c)
        + defect K (r ⊔ b) (r ⊔ c)
        + (K ((r ⊔ a) ⊓ (r ⊔ b) ⊓ (r ⊔ c)) - K r) := by
  have h1 : (r ⊔ a) ⊔ (r ⊔ b) = r ⊔ a ⊔ b := by
    rw [sup_sup_sup_comm, sup_idem, ← sup_assoc]
  have h2 : (r ⊔ a) ⊔ (r ⊔ c) = r ⊔ a ⊔ c := by
    rw [sup_sup_sup_comm, sup_idem, ← sup_assoc]
  have h3 : (r ⊔ b) ⊔ (r ⊔ c) = r ⊔ b ⊔ c := by
    rw [sup_sup_sup_comm, sup_idem, ← sup_assoc]
  have h4 : (r ⊔ a ⊔ b) ⊔ (r ⊔ c) = r ⊔ a ⊔ b ⊔ c := by
    rw [← sup_assoc, sup_eq_left.mpr (le_sup_left.trans le_sup_left : r ≤ r ⊔ a ⊔ b)]
  simp only [mixedDiff_cons, mixedDiff_nil, supDiff_apply, defect3, defect_def,
    h1, h2, h3, h4]
  abel

/-- At the meet base the residue vanishes: the raw order-3 mixed difference
is exactly face data minus the order-3 defect. Subtracting the faces is
the order-separation datum. -/
theorem mixedDiff_triple_inf (K : ContextField R A) (a b c : R) :
    mixedDiff [a, b, c] K (a ⊓ b ⊓ c)
      = defect K a b + defect K a c + defect K b c - defect3 K a b c := by
  have h := mixedDiff_triple_add_defect3 K a b c (a ⊓ b ⊓ c)
  have ha : a ⊓ b ⊓ c ⊔ a = a :=
    sup_eq_right.mpr ((inf_le_left.trans inf_le_left : a ⊓ b ⊓ c ≤ a))
  have hb : a ⊓ b ⊓ c ⊔ b = b :=
    sup_eq_right.mpr ((inf_le_left.trans inf_le_right : a ⊓ b ⊓ c ≤ b))
  have hc : a ⊓ b ⊓ c ⊔ c = c :=
    sup_eq_right.mpr (inf_le_right : a ⊓ b ⊓ c ≤ c)
  rw [ha, hb, hc, sub_self, add_zero] at h
  exact eq_sub_of_add_eq h

/-! ### Naturality -/

theorem defect3_comp {R' : Type*} [Lattice R'] (f : LatticeHom R R')
    (K : ContextField R' A) (a b c : R) :
    defect3 (K ∘ f) a b c = defect3 K (f a) (f b) (f c) := by
  simp [defect3, Function.comp_apply, map_inf, map_sup]

end Lattice

/-! ### Descent on distributive contexts -/

section DistribLattice

variable {R A : Type*} [DistribLattice R] [AddCommGroup A]

/-- On a distributive lattice the order-3 defect decomposes exactly into
pairwise defects at derived squares: order 3 carries nothing irreducible. -/
theorem defect3_decompose (K : ContextField R A) (a b c : R) :
    defect3 K a b c
      = defect K a b + defect K (a ⊔ b) c - defect K (a ⊓ c) (b ⊓ c) := by
  have hd : (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) := inf_sup_right a b c
  have hm : (a ⊓ c) ⊓ (b ⊓ c) = a ⊓ b ⊓ c := by
    rw [inf_assoc a c, inf_comm c (b ⊓ c), inf_assoc b c, inf_idem, ← inf_assoc]
  simp only [defect3, defect_def, hd, hm]
  abel

/-- Pairwise valuations have no order-3 defect on distributive contexts. -/
theorem defect3_eq_zero_of_isValuation {K : ContextField R A}
    (h : IsValuation K) (a b c : R) : defect3 K a b c = 0 := by
  rw [defect3_decompose, h a b, h (a ⊔ b) c, h (a ⊓ c) (b ⊓ c)]
  abel

/-- The descent law: on distributive contexts the order-3 defect descends
through the pairwise gauge. -/
theorem defect3_eq_of_defectEquiv {K K' : ContextField R A}
    (h : DefectEquiv K K') : defect3 K = defect3 K' := by
  funext a b c
  have hG := defectEquiv_iff_sub_isValuation.mp h
  have h0 := defect3_eq_zero_of_isValuation hG a b c
  rw [defect3_sub] at h0
  exact sub_eq_zero.mp h0

/-- On distributive contexts the order-3 defect is an observable of the
pairwise class: it lifts to the observable quotient. -/
def Observable.defect3 : Observable R A → (R → R → R → A) :=
  Quotient.lift (fun K => Descent.defect3 K) fun _ _ h => defect3_eq_of_defectEquiv h

@[simp]
theorem Observable.defect3_mk (K : ContextField R A) :
    Observable.defect3 (Observable.mk K) = Descent.defect3 K :=
  rfl

end DistribLattice

end Descent
