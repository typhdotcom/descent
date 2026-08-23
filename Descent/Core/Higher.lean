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
* **the cumulative observation**: the datum through order 3 is the pair
  `(defect K, defect3 K)`. Its kernel is the order-≤3 gauge `gauge3`,
  equal cumulative data is exactly a difference in that gauge
  (`defect3Equiv_iff_sub_mem_gauge3`), and the datum descends injectively
  to the cumulative quotient `Observable3`
  (`Observable3.datum_injective`);
* **the architecture**: on a distributive lattice the order-3 defect
  decomposes exactly into pairwise defects at derived squares
  (`defect3_decompose`), so the order-≤3 gauge collapses to the pairwise
  gauge (`gauge3_eq_gauge`) and order 3 adds nothing --- `defect3`
  descends to the pairwise quotient (`Observable.defect3`). Off
  distributivity observation through order 3 is strictly finer: on the
  diamond the gauges are strictly nested and two fields share the
  pairwise observable while the cumulative observable separates them
  (`Descent.Models.Diamond`).

Order 4 repeats the pattern exactly, and reveals the recurrence.
`defect4` is the failure of fourfold inclusion–exclusion; degeneracy
collapses it to an order-3 face (`defect4_of_le`); the raw order-4 cube
decomposes exactly into alternating order-3 and order-2 faces, the
order-4 defect, and the base residue (`mixedDiff_quad_add_defect4`); the
cumulative datum `(D₂, D₃, D₄)` has gauge `gauge4`, equivalence
`Defect4Equiv`, and injective quotient observation `Observable4.datum`.
On distributive lattices the collapse persists through the recurrence

    D₄(a,b,c,d) = D₃(a,b,c) + D₂(a ⊔ b ⊔ c, d) - D₃(a ⊓ d, b ⊓ d, c ⊓ d)

(`defect4_decompose`), the same shape as `defect3_decompose` one order
down: `gauge4 = gauge` distributively.

The separation question at order 4 is settled negatively, on every
lattice: the order-≤3 gauge is blind to every two-variable
distributivity-defect interval (`apply_eq_of_mem_gauge3`), the blindness
propagates through the valuation law to the three-variable interval of
the order-4 criterion, and the order-4 defect vanishes on the order-≤3
gauge (`defect4_eq_zero_of_mem_gauge3`). Saturation:
`gauge4 = gauge3` unconditionally (`gauge4_eq_gauge3`), cumulative
equivalence through order 4 is cumulative equivalence through order 3,
and the order-4 datum is a function of the order-≤3 datum on every
carrier.
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

/-- The exact recurrence at order 3 on an arbitrary lattice: the
distributive decomposition plus the field gap across the two-variable
distributivity-defect interval `[(a ⊓ c) ⊔ (b ⊓ c), (a ⊔ b) ⊓ c]`. -/
theorem defect3_recurrence (K : ContextField R A) (a b c : R) :
    defect3 K a b c
      = defect K a b + defect K (a ⊔ b) c - defect K (a ⊓ c) (b ⊓ c)
        + (K ((a ⊔ b) ⊓ c) - K ((a ⊓ c) ⊔ (b ⊓ c))) := by
  have hm : (a ⊓ c) ⊓ (b ⊓ c) = a ⊓ b ⊓ c := by
    rw [inf_assoc a c, inf_comm c (b ⊓ c), inf_assoc b c, inf_idem, ← inf_assoc]
  simp only [defect3, defect_def, hm]
  abel

/-- The order-3 search criterion: on the pairwise gauge the order-3
defect is exactly the field gap across the two-variable
distributivity-defect interval. -/
theorem defect3_eq_of_mem_gauge {K : ContextField R A} (hK : K ∈ gauge R A)
    (a b c : R) :
    defect3 K a b c = K ((a ⊔ b) ⊓ c) - K ((a ⊓ c) ⊔ (b ⊓ c)) := by
  have h2 := mem_gauge_iff.mp hK
  rw [defect3_recurrence, h2 a b, h2 (a ⊔ b) c, h2 (a ⊓ c) (b ⊓ c)]
  abel

/-! ### Order 4 -/

/-- The order-4 defect of `K`: the failure of fourfold
inclusion–exclusion. -/
def defect4 (K : ContextField R A) (a b c d : R) : A :=
  K a + K b + K c + K d
    - K (a ⊓ b) - K (a ⊓ c) - K (a ⊓ d) - K (b ⊓ c) - K (b ⊓ d) - K (c ⊓ d)
    + K (a ⊓ b ⊓ c) + K (a ⊓ b ⊓ d) + K (a ⊓ c ⊓ d) + K (b ⊓ c ⊓ d)
    - K (a ⊓ b ⊓ c ⊓ d) - K (a ⊔ b ⊔ c ⊔ d)

theorem defect4_def (K : ContextField R A) (a b c d : R) :
    defect4 K a b c d
      = K a + K b + K c + K d
        - K (a ⊓ b) - K (a ⊓ c) - K (a ⊓ d) - K (b ⊓ c) - K (b ⊓ d) - K (c ⊓ d)
        + K (a ⊓ b ⊓ c) + K (a ⊓ b ⊓ d) + K (a ⊓ c ⊓ d) + K (b ⊓ c ⊓ d)
        - K (a ⊓ b ⊓ c ⊓ d) - K (a ⊔ b ⊔ c ⊔ d) :=
  rfl

theorem defect4_comm_left (K : ContextField R A) (a b c d : R) :
    defect4 K a b c d = defect4 K b a c d := by
  simp only [defect4, inf_comm a b, sup_comm a b]
  abel

theorem defect4_comm_mid (K : ContextField R A) (a b c d : R) :
    defect4 K a b c d = defect4 K a c b d := by
  simp only [defect4, inf_comm b c, inf_right_comm a b c, sup_right_comm a b c]
  abel

theorem defect4_comm_right (K : ContextField R A) (a b c d : R) :
    defect4 K a b c d = defect4 K a b d c := by
  simp only [defect4, inf_comm c d, inf_right_comm a c d, inf_right_comm b c d,
    inf_right_comm (a ⊓ b) c d, sup_right_comm (a ⊔ b) c d]
  abel

@[simp]
theorem defect4_zero : defect4 (0 : ContextField R A) = 0 := by
  funext a b c d
  simp [defect4]

theorem defect4_add (K K' : ContextField R A) (a b c d : R) :
    defect4 (K + K') a b c d = defect4 K a b c d + defect4 K' a b c d := by
  simp only [defect4, Pi.add_apply]
  abel

theorem defect4_sub (K K' : ContextField R A) (a b c d : R) :
    defect4 (K - K') a b c d = defect4 K a b c d - defect4 K' a b c d := by
  simp only [defect4, Pi.sub_apply]
  abel

/-- On a degenerate quadruple the order-4 defect is the order-3 defect of
the surviving triple: no raw field data is retained. -/
theorem defect4_of_le (K : ContextField R A) {a b : R} (h : a ≤ b) (c d : R) :
    defect4 K a b c d = defect3 K b c d := by
  simp only [defect4, defect3, inf_eq_left.mpr h, sup_eq_right.mpr h]
  abel

theorem defect4_self (K : ContextField R A) (a c d : R) :
    defect4 K a a c d = defect3 K a c d :=
  defect4_of_le K le_rfl c d

/-- If every order-3 defect vanishes, the order-4 defect vanishes on any
quadruple containing a comparable pair: without a 4-antichain, order 4
adds nothing beyond order 3. -/
theorem defect4_eq_zero_of_defect3_eq_zero {K : ContextField R A}
    (h3 : ∀ a b c, defect3 K a b c = 0) {a b c d : R}
    (h : Comparable a b ∨ Comparable a c ∨ Comparable a d ∨ Comparable b c ∨
      Comparable b d ∨ Comparable c d) :
    defect4 K a b c d = 0 := by
  have red : ∀ p q u v : R, p ≤ q → defect4 K p q u v = 0 := fun p q u v hpq => by
    rw [defect4_of_le K hpq]
    exact h3 q u v
  rcases h with (h | h) | (h | h) | (h | h) | (h | h) | (h | h) | (h | h)
  · exact red a b c d h
  · rw [defect4_comm_left]
    exact red b a c d h
  · rw [defect4_comm_mid]
    exact red a c b d h
  · rw [defect4_comm_mid, defect4_comm_left]
    exact red c a b d h
  · rw [defect4_comm_right, defect4_comm_mid]
    exact red a d b c h
  · rw [defect4_comm_right, defect4_comm_mid, defect4_comm_left]
    exact red d a b c h
  · rw [defect4_comm_left, defect4_comm_mid]
    exact red b c a d h
  · rw [defect4_comm_mid, defect4_comm_left, defect4_comm_mid]
    exact red c b a d h
  · rw [defect4_comm_left, defect4_comm_right, defect4_comm_mid]
    exact red b d a c h
  · rw [defect4_comm_left, defect4_comm_right, defect4_comm_mid, defect4_comm_left]
    exact red d b a c h
  · rw [defect4_comm_mid, defect4_comm_left, defect4_comm_right, defect4_comm_mid]
    exact red c d a b h
  · rw [defect4_comm_mid, defect4_comm_left, defect4_comm_right, defect4_comm_mid,
      defect4_comm_left]
    exact red d c a b h

/-- The exact isolation identity at an arbitrary base: the raw order-4
mixed difference is its order-3 faces, minus its order-2 faces, minus the
order-4 defect of the translated quadruple, plus the base-point
residue. -/
theorem mixedDiff_quad_add_defect4 (K : ContextField R A) (a b c d r : R) :
    mixedDiff [a, b, c, d] K r
        + defect4 K (r ⊔ a) (r ⊔ b) (r ⊔ c) (r ⊔ d)
      = defect3 K (r ⊔ a) (r ⊔ b) (r ⊔ c) + defect3 K (r ⊔ a) (r ⊔ b) (r ⊔ d)
          + defect3 K (r ⊔ a) (r ⊔ c) (r ⊔ d) + defect3 K (r ⊔ b) (r ⊔ c) (r ⊔ d)
        - (defect K (r ⊔ a) (r ⊔ b) + defect K (r ⊔ a) (r ⊔ c)
            + defect K (r ⊔ a) (r ⊔ d) + defect K (r ⊔ b) (r ⊔ c)
            + defect K (r ⊔ b) (r ⊔ d) + defect K (r ⊔ c) (r ⊔ d))
        + (K r - K ((r ⊔ a) ⊓ (r ⊔ b) ⊓ (r ⊔ c) ⊓ (r ⊔ d))) := by
  have hstep : ∀ x q : R, r ≤ x → x ⊔ (r ⊔ q) = x ⊔ q := fun x q hx => by
    rw [← sup_assoc, sup_eq_left.mpr hx]
  have h1 : (r ⊔ a) ⊔ (r ⊔ b) = r ⊔ a ⊔ b := hstep _ _ le_sup_left
  have h2 : (r ⊔ a) ⊔ (r ⊔ c) = r ⊔ a ⊔ c := hstep _ _ le_sup_left
  have h3 : (r ⊔ a) ⊔ (r ⊔ d) = r ⊔ a ⊔ d := hstep _ _ le_sup_left
  have h4 : (r ⊔ b) ⊔ (r ⊔ c) = r ⊔ b ⊔ c := hstep _ _ le_sup_left
  have h5 : (r ⊔ b) ⊔ (r ⊔ d) = r ⊔ b ⊔ d := hstep _ _ le_sup_left
  have h6 : (r ⊔ c) ⊔ (r ⊔ d) = r ⊔ c ⊔ d := hstep _ _ le_sup_left
  have t1 : (r ⊔ a ⊔ b) ⊔ (r ⊔ c) = r ⊔ a ⊔ b ⊔ c :=
    hstep _ _ (le_sup_left.trans le_sup_left)
  have t2 : (r ⊔ a ⊔ b) ⊔ (r ⊔ d) = r ⊔ a ⊔ b ⊔ d :=
    hstep _ _ (le_sup_left.trans le_sup_left)
  have t3 : (r ⊔ a ⊔ c) ⊔ (r ⊔ d) = r ⊔ a ⊔ c ⊔ d :=
    hstep _ _ (le_sup_left.trans le_sup_left)
  have t4 : (r ⊔ b ⊔ c) ⊔ (r ⊔ d) = r ⊔ b ⊔ c ⊔ d :=
    hstep _ _ (le_sup_left.trans le_sup_left)
  have q1 : (r ⊔ a ⊔ b ⊔ c) ⊔ (r ⊔ d) = r ⊔ a ⊔ b ⊔ c ⊔ d :=
    hstep _ _ ((le_sup_left.trans le_sup_left).trans le_sup_left)
  simp only [mixedDiff_cons, mixedDiff_nil, supDiff_apply, defect4, defect3,
    defect_def, h1, h2, h3, h4, h5, h6, t1, t2, t3, t4, q1]
  abel

/-- At the meet base the residue vanishes: the raw order-4 mixed
difference is exactly alternating face data minus the order-4 defect. -/
theorem mixedDiff_quad_inf (K : ContextField R A) (a b c d : R) :
    mixedDiff [a, b, c, d] K (a ⊓ b ⊓ c ⊓ d)
      = defect3 K a b c + defect3 K a b d + defect3 K a c d + defect3 K b c d
        - (defect K a b + defect K a c + defect K a d + defect K b c
            + defect K b d + defect K c d)
        - defect4 K a b c d := by
  have h := mixedDiff_quad_add_defect4 K a b c d (a ⊓ b ⊓ c ⊓ d)
  have ha : a ⊓ b ⊓ c ⊓ d ⊔ a = a :=
    sup_eq_right.mpr ((inf_le_left.trans inf_le_left).trans inf_le_left)
  have hb : a ⊓ b ⊓ c ⊓ d ⊔ b = b :=
    sup_eq_right.mpr ((inf_le_left.trans inf_le_left).trans inf_le_right)
  have hc : a ⊓ b ⊓ c ⊓ d ⊔ c = c :=
    sup_eq_right.mpr (inf_le_left.trans inf_le_right)
  have hd : a ⊓ b ⊓ c ⊓ d ⊔ d = d :=
    sup_eq_right.mpr inf_le_right
  rw [ha, hb, hc, hd, sub_self, add_zero] at h
  exact eq_sub_of_add_eq h

theorem defect4_comp {R' : Type*} [Lattice R'] (f : LatticeHom R R')
    (K : ContextField R' A) (a b c d : R) :
    defect4 (K ∘ f) a b c d = defect4 K (f a) (f b) (f c) (f d) := by
  simp [defect4, Function.comp_apply, map_inf, map_sup]

/-- The exact recurrence on an arbitrary lattice: the order-4 defect is
the order-3 recurrence shape plus the field gap across the
distributivity-defect interval
`[(a ⊓ d) ⊔ (b ⊓ d) ⊔ (c ⊓ d), (a ⊔ b ⊔ c) ⊓ d]`. -/
theorem defect4_recurrence (K : ContextField R A) (a b c d : R) :
    defect4 K a b c d
      = defect3 K a b c + defect K (a ⊔ b ⊔ c) d
        - defect3 K (a ⊓ d) (b ⊓ d) (c ⊓ d)
        + (K ((a ⊔ b ⊔ c) ⊓ d) - K ((a ⊓ d) ⊔ (b ⊓ d) ⊔ (c ⊓ d))) := by
  have hm : ∀ x y : R, (x ⊓ d) ⊓ (y ⊓ d) = x ⊓ y ⊓ d := fun x y => by
    rw [inf_assoc x d, inf_comm d (y ⊓ d), inf_assoc y d, inf_idem, ← inf_assoc]
  simp only [defect4, defect3, defect_def, hm]
  abel

/-! ### The cumulative observation through order 3 -/

/-- The order-3 defect operator, packaged as an additive homomorphism. -/
def defect3Hom : ContextField R A →+ (R → R → R → A) where
  toFun K := defect3 K
  map_zero' := defect3_zero
  map_add' K K' := by
    funext a b c
    exact defect3_add K K' a b c

@[simp]
theorem defect3Hom_apply (K : ContextField R A) : defect3Hom K = defect3 K :=
  rfl

/-- The order-≤3 gauge: the kernel of cumulative observation through
order 3. -/
def gauge3 (R A : Type*) [Lattice R] [AddCommGroup A] :
    AddSubgroup (ContextField R A) :=
  gauge R A ⊓ defect3Hom.ker

theorem mem_gauge3_iff {K : ContextField R A} :
    K ∈ gauge3 R A ↔ IsValuation K ∧ ∀ a b c, defect3 K a b c = 0 := by
  rw [gauge3, AddSubgroup.mem_inf, mem_gauge_iff, AddMonoidHom.mem_ker]
  refine and_congr Iff.rfl ?_
  constructor
  · exact fun h a b c => congrFun (congrFun (congrFun h a) b) c
  · intro h
    funext a b c
    exact h a b c

/-- Cumulative defect equivalence: equal pairwise and order-3 data. -/
def Defect3Equiv (K K' : ContextField R A) : Prop :=
  DefectEquiv K K' ∧ defect3 K = defect3 K'

theorem Defect3Equiv.refl (K : ContextField R A) : Defect3Equiv K K :=
  ⟨DefectEquiv.refl K, rfl⟩

theorem Defect3Equiv.symm {K K' : ContextField R A} (h : Defect3Equiv K K') :
    Defect3Equiv K' K :=
  ⟨h.1.symm, h.2.symm⟩

theorem Defect3Equiv.trans {K K' K'' : ContextField R A}
    (h : Defect3Equiv K K') (h' : Defect3Equiv K' K'') : Defect3Equiv K K'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- Equal cumulative data is exactly a difference in the order-≤3
gauge. -/
theorem defect3Equiv_iff_sub_mem_gauge3 {K K' : ContextField R A} :
    Defect3Equiv K K' ↔ K - K' ∈ gauge3 R A := by
  rw [mem_gauge3_iff, Defect3Equiv, defectEquiv_iff_sub_isValuation]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h a b c
    rw [defect3_sub, congrFun (congrFun (congrFun h a) b) c, sub_self]
  · intro h
    funext a b c
    have h0 := h a b c
    rw [defect3_sub] at h0
    exact sub_eq_zero.mp h0

/-- Cumulative equivalence as a setoid. -/
def defect3Setoid (R A : Type*) [Lattice R] [AddCommGroup A] :
    Setoid (ContextField R A) where
  r := Defect3Equiv
  iseqv := ⟨Defect3Equiv.refl, Defect3Equiv.symm, Defect3Equiv.trans⟩

/-- The cumulative observable quotient through order 3. -/
def Observable3 (R A : Type*) [Lattice R] [AddCommGroup A] : Type _ :=
  Quotient (defect3Setoid R A)

namespace Observable3

/-- The cumulative class of a field. -/
def mk (K : ContextField R A) : Observable3 R A :=
  Quotient.mk (defect3Setoid R A) K

theorem mk_eq_mk {K K' : ContextField R A} :
    mk K = mk K' ↔ Defect3Equiv K K' :=
  Quotient.eq (r := defect3Setoid R A)

/-- The cumulative datum, descended to the quotient. -/
def datum : Observable3 R A → (R → R → A) × (R → R → R → A) :=
  Quotient.lift (fun K => (Descent.defect K, defect3 K)) fun _ _ h =>
    Prod.ext h.1 h.2

@[simp]
theorem datum_mk (K : ContextField R A) :
    datum (mk K) = (Descent.defect K, defect3 K) :=
  rfl

/-- Cumulative observation is injective: the quotient carries exactly the
cumulative datum. -/
theorem datum_injective : Function.Injective (datum : Observable3 R A → _) := by
  intro u v h
  induction u using Quotient.inductionOn with
  | _ K =>
    induction v using Quotient.inductionOn with
    | _ K' =>
      exact mk_eq_mk.mpr ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end Observable3

/-! ### The cumulative observation through order 4 -/

/-- The order-4 defect operator, packaged as an additive homomorphism. -/
def defect4Hom : ContextField R A →+ (R → R → R → R → A) where
  toFun K := defect4 K
  map_zero' := defect4_zero
  map_add' K K' := by
    funext a b c d
    exact defect4_add K K' a b c d

@[simp]
theorem defect4Hom_apply (K : ContextField R A) : defect4Hom K = defect4 K :=
  rfl

/-- The order-≤4 gauge: the kernel of cumulative observation through
order 4. -/
def gauge4 (R A : Type*) [Lattice R] [AddCommGroup A] :
    AddSubgroup (ContextField R A) :=
  gauge3 R A ⊓ defect4Hom.ker

theorem mem_gauge4_iff {K : ContextField R A} :
    K ∈ gauge4 R A ↔ IsValuation K ∧ (∀ a b c, defect3 K a b c = 0) ∧
      ∀ a b c d, defect4 K a b c d = 0 := by
  rw [gauge4, AddSubgroup.mem_inf, mem_gauge3_iff, AddMonoidHom.mem_ker, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · exact fun h a b c d =>
      congrFun (congrFun (congrFun (congrFun h a) b) c) d
  · intro h
    funext a b c d
    exact h a b c d

/-- The search criterion for order-4 strictness: on the order-≤3 gauge
everything in the recurrence dies except the remainder, so the order-4
defect is exactly the field gap across the distributivity-defect
interval. Cumulative observation is strictly finer at order 4 precisely
when some order-≤3 gauge field detects such an interval. -/
theorem defect4_eq_of_mem_gauge3 {K : ContextField R A}
    (hK : K ∈ gauge3 R A) (a b c d : R) :
    defect4 K a b c d
      = K ((a ⊔ b ⊔ c) ⊓ d) - K ((a ⊓ d) ⊔ (b ⊓ d) ⊔ (c ⊓ d)) := by
  obtain ⟨h2, h3⟩ := mem_gauge3_iff.mp hK
  rw [defect4_recurrence, h3 a b c, h2 (a ⊔ b ⊔ c) d,
    h3 (a ⊓ d) (b ⊓ d) (c ⊓ d)]
  abel

/-- Two-variable blindness of the order-≤3 gauge: its fields do not
separate any two-variable distributivity-defect interval. -/
theorem apply_eq_of_mem_gauge3 {K : ContextField R A} (hK : K ∈ gauge3 R A)
    (a b c : R) : K ((a ⊔ b) ⊓ c) = K ((a ⊓ c) ⊔ (b ⊓ c)) := by
  obtain ⟨h2, h3⟩ := mem_gauge3_iff.mp hK
  have h := defect3_eq_of_mem_gauge (mem_gauge_iff.mpr h2) a b c
  rw [h3 a b c] at h
  exact sub_eq_zero.mp h.symm

/-- Saturation: on the order-≤3 gauge the order-4 defect vanishes, on
every lattice. Two-variable blindness propagates through the valuation
law to the three-variable interval, so no order-≤3 gauge field detects
it. -/
theorem defect4_eq_zero_of_mem_gauge3 {K : ContextField R A}
    (hK : K ∈ gauge3 R A) (a b c d : R) : defect4 K a b c d = 0 := by
  have h2 := (mem_gauge3_iff.mp hK).1
  have hG := apply_eq_of_mem_gauge3 hK
  have hval : ∀ x y : R, K (x ⊔ y) = K x + K y - K (x ⊓ y) := fun x y => by
    have h := h2 x y
    rw [defect_def] at h
    exact (sub_eq_zero.mp h).symm
  have e1 : ((a ⊔ b) ⊓ d) ⊓ (c ⊓ d) = (a ⊔ b) ⊓ (c ⊓ d) := by
    rw [inf_assoc, inf_eq_right.mpr inf_le_right]
  have e3 : (a ⊓ d) ⊓ (c ⊓ d) = a ⊓ (c ⊓ d) := by
    rw [inf_assoc, inf_eq_right.mpr inf_le_right]
  have e4 : (b ⊓ d) ⊓ (c ⊓ d) = b ⊓ (c ⊓ d) := by
    rw [inf_assoc, inf_eq_right.mpr inf_le_right]
  rw [defect4_eq_of_mem_gauge3 hK, sub_eq_zero]
  calc K ((a ⊔ b ⊔ c) ⊓ d)
      = K (((a ⊔ b) ⊓ d) ⊔ (c ⊓ d)) := hG (a ⊔ b) c d
    _ = K ((a ⊔ b) ⊓ d) + K (c ⊓ d) - K ((a ⊔ b) ⊓ (c ⊓ d)) := by
        rw [hval, e1]
    _ = K ((a ⊓ d) ⊔ (b ⊓ d)) + K (c ⊓ d)
          - K ((a ⊓ (c ⊓ d)) ⊔ (b ⊓ (c ⊓ d))) := by
        rw [hG a b d, hG a b (c ⊓ d)]
    _ = K ((a ⊓ d) ⊔ (b ⊓ d)) + K (c ⊓ d)
          - K (((a ⊓ d) ⊔ (b ⊓ d)) ⊓ (c ⊓ d)) := by
        rw [hG (a ⊓ d) (b ⊓ d) (c ⊓ d), e3, e4]
    _ = K ((a ⊓ d) ⊔ (b ⊓ d) ⊔ (c ⊓ d)) := (hval _ _).symm

/-- The saturation theorem: the order-≤4 gauge is the order-≤3 gauge on
every lattice and for every target. Cumulative observation cannot become
strictly finer at order 4. -/
theorem gauge4_eq_gauge3 : gauge4 R A = gauge3 R A := by
  refine le_antisymm inf_le_left fun K hK => ?_
  rw [gauge4, AddSubgroup.mem_inf]
  refine ⟨hK, ?_⟩
  rw [AddMonoidHom.mem_ker]
  funext a b c d
  exact defect4_eq_zero_of_mem_gauge3 hK a b c d

/-- Cumulative defect equivalence through order 4. -/
def Defect4Equiv (K K' : ContextField R A) : Prop :=
  Defect3Equiv K K' ∧ defect4 K = defect4 K'

theorem Defect4Equiv.refl (K : ContextField R A) : Defect4Equiv K K :=
  ⟨Defect3Equiv.refl K, rfl⟩

theorem Defect4Equiv.symm {K K' : ContextField R A} (h : Defect4Equiv K K') :
    Defect4Equiv K' K :=
  ⟨h.1.symm, h.2.symm⟩

theorem Defect4Equiv.trans {K K' K'' : ContextField R A}
    (h : Defect4Equiv K K') (h' : Defect4Equiv K' K'') : Defect4Equiv K K'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- Equal cumulative data through order 4 is exactly a difference in the
order-≤4 gauge. -/
theorem defect4Equiv_iff_sub_mem_gauge4 {K K' : ContextField R A} :
    Defect4Equiv K K' ↔ K - K' ∈ gauge4 R A := by
  rw [gauge4, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, Defect4Equiv,
    ← defect3Equiv_iff_sub_mem_gauge3]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h
    funext a b c d
    show defect4 (K - K') a b c d = 0
    rw [defect4_sub, congrFun (congrFun (congrFun (congrFun h a) b) c) d,
      sub_self]
  · intro h
    funext a b c d
    have h0 : defect4 (K - K') a b c d = 0 :=
      congrFun (congrFun (congrFun (congrFun h a) b) c) d
    rw [defect4_sub] at h0
    exact sub_eq_zero.mp h0

/-- Cumulative equivalence through order 4 as a setoid. -/
def defect4Setoid (R A : Type*) [Lattice R] [AddCommGroup A] :
    Setoid (ContextField R A) where
  r := Defect4Equiv
  iseqv := ⟨Defect4Equiv.refl, Defect4Equiv.symm, Defect4Equiv.trans⟩

/-- The cumulative observable quotient through order 4. -/
def Observable4 (R A : Type*) [Lattice R] [AddCommGroup A] : Type _ :=
  Quotient (defect4Setoid R A)

namespace Observable4

/-- The cumulative class of a field. -/
def mk (K : ContextField R A) : Observable4 R A :=
  Quotient.mk (defect4Setoid R A) K

theorem mk_eq_mk {K K' : ContextField R A} :
    mk K = mk K' ↔ Defect4Equiv K K' :=
  Quotient.eq (r := defect4Setoid R A)

/-- The cumulative datum through order 4, descended to the quotient. -/
def datum :
    Observable4 R A → (R → R → A) × (R → R → R → A) × (R → R → R → R → A) :=
  Quotient.lift (fun K => (Descent.defect K, defect3 K, defect4 K)) fun _ _ h =>
    Prod.ext h.1.1 (Prod.ext h.1.2 h.2)

@[simp]
theorem datum_mk (K : ContextField R A) :
    datum (mk K) = (Descent.defect K, defect3 K, defect4 K) :=
  rfl

/-- Cumulative observation through order 4 is injective on its
quotient. -/
theorem datum_injective : Function.Injective (datum : Observable4 R A → _) := by
  intro u v h
  induction u using Quotient.inductionOn with
  | _ K =>
    induction v using Quotient.inductionOn with
    | _ K' =>
      exact mk_eq_mk.mpr
        ⟨⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h⟩,
          congrArg (fun p => p.2.2) h⟩

end Observable4

/-- Saturation at the level of equivalences: cumulative equivalence
through order 4 is cumulative equivalence through order 3, on every
lattice. -/
theorem defect4Equiv_iff_defect3Equiv {K K' : ContextField R A} :
    Defect4Equiv K K' ↔ Defect3Equiv K K' := by
  rw [defect4Equiv_iff_sub_mem_gauge4, defect3Equiv_iff_sub_mem_gauge3,
    gauge4_eq_gauge3]

/-- The order-4 datum is a function of the cumulative order-≤3 datum, on
every lattice. -/
theorem defect4_eq_of_defect3Equiv {K K' : ContextField R A}
    (h : Defect3Equiv K K') : defect4 K = defect4 K' :=
  (defect4Equiv_iff_defect3Equiv.mpr h).2

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

/-- On distributive contexts cumulative equivalence collapses to pairwise
equivalence: order 3 adds nothing. -/
theorem defect3Equiv_iff_defectEquiv {K K' : ContextField R A} :
    Defect3Equiv K K' ↔ DefectEquiv K K' :=
  ⟨And.left, fun h => ⟨h, defect3_eq_of_defectEquiv h⟩⟩

/-- On distributive contexts the order-≤3 gauge is the pairwise gauge. -/
theorem gauge3_eq_gauge : gauge3 R A = gauge R A := by
  refine le_antisymm inf_le_left fun K hK => mem_gauge3_iff.mpr ?_
  exact ⟨mem_gauge_iff.mp hK,
    defect3_eq_zero_of_isValuation (mem_gauge_iff.mp hK)⟩

/-! On a distributive lattice the recurrence continues one order up, and
the collapse persists. -/

/-- On a distributive lattice the remainder of `defect4_recurrence`
vanishes and the order-4 defect decomposes exactly through order 3 ---
the same shape as `defect3_decompose` one order down. -/
theorem defect4_decompose (K : ContextField R A) (a b c d : R) :
    defect4 K a b c d
      = defect3 K a b c + defect K (a ⊔ b ⊔ c) d
        - defect3 K (a ⊓ d) (b ⊓ d) (c ⊓ d) := by
  have hd : (a ⊔ b ⊔ c) ⊓ d = (a ⊓ d) ⊔ (b ⊓ d) ⊔ (c ⊓ d) := by
    rw [inf_sup_right, inf_sup_right]
  rw [defect4_recurrence, hd, sub_self, add_zero]

/-- Pairwise valuations have no order-4 defect on distributive
contexts: the collapse persists at order 4. -/
theorem defect4_eq_zero_of_isValuation {K : ContextField R A}
    (h : IsValuation K) (a b c d : R) : defect4 K a b c d = 0 := by
  rw [defect4_decompose, defect3_eq_zero_of_isValuation h,
    defect3_eq_zero_of_isValuation h, h (a ⊔ b ⊔ c) d]
  abel

/-- The descent law at order 4 on distributive contexts. -/
theorem defect4_eq_of_defectEquiv {K K' : ContextField R A}
    (h : DefectEquiv K K') : defect4 K = defect4 K' := by
  funext a b c d
  have hG := defectEquiv_iff_sub_isValuation.mp h
  have h0 := defect4_eq_zero_of_isValuation hG a b c d
  rw [defect4_sub] at h0
  exact sub_eq_zero.mp h0

/-- On distributive contexts the order-4 defect is an observable of the
pairwise class. -/
def Observable.defect4 : Observable R A → (R → R → R → R → A) :=
  Quotient.lift (fun K => Descent.defect4 K) fun _ _ h => defect4_eq_of_defectEquiv h

@[simp]
theorem Observable.defect4_mk (K : ContextField R A) :
    Observable.defect4 (Observable.mk K) = Descent.defect4 K :=
  rfl

/-- On distributive contexts cumulative equivalence through order 4
collapses to pairwise equivalence. -/
theorem defect4Equiv_iff_defectEquiv {K K' : ContextField R A} :
    Defect4Equiv K K' ↔ DefectEquiv K K' :=
  ⟨fun h => h.1.1, fun h =>
    ⟨⟨h, defect3_eq_of_defectEquiv h⟩, defect4_eq_of_defectEquiv h⟩⟩

/-- On distributive contexts the order-≤4 gauge is the pairwise gauge:
order 4 still adds nothing. -/
theorem gauge4_eq_gauge : gauge4 R A = gauge R A := by
  rw [gauge4, gauge3_eq_gauge, inf_eq_left]
  intro K hK
  rw [AddMonoidHom.mem_ker]
  funext a b c d
  exact defect4_eq_zero_of_isValuation (mem_gauge_iff.mp hK) a b c d

end DistribLattice

end Descent
