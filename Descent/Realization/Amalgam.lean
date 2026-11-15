import Amalgam.System.Binary
import Descent.Realization.Incidence

/-!
# Finite restriction systems are Amalgam restriction systems

A `FiniteRestriction` is an Amalgam `RestrictionSystem` with finiteness,
nonemptiness, and decidable equality added; both read `a ≤ b` as `a`
coarser than `b`, with restriction from `b` to `a`
(`FiniteRestriction.toRestrictionSystem`). Over a lattice the
local-to-global layer is Amalgam's:

* `Compat a b` is the pullback `Function.Pullback` of the two restriction
  legs to the meet, and `compare a b` is its universal map
  `Function.Pullback.lift` from the join, both by definition
  (`compat_eq_pullback`, `compare_eq_lift`);
* compatible pairs and triples are compatible families over `![a, b]`
  and `![a, b, c]` (`compatEquivFamily`, `compat3EquivFamily`), and the
  comparisons are restriction of the one-context family at the join
  (`compatEquivFamily_compare`, `compat3EquivFamily_compare3`);
* the extension profile is the cardinality of the fiber,
  `ext f b = Nat.card {a // f a = b}` (`Incidence.ext_eq_natCard_fiber`),
  so positivity, the bound `≤ 1`, and the value `1` are nonemptiness,
  subsingletonness, and unique inhabitation of the fiber.

Compatible pairs fiber in two ways. `compatSigmaEquiv` fibers them over
the meet as products of both legs' fibers; Amalgam's `fiberFstEquiv`
fibers them over the left state by the right leg's fiber
(`compatSigmaFstEquiv`).
-/

namespace Descent

open Function

section Lattice

variable {R : Type*} [Lattice R] (S : RestrictionSystem R)

/-- Over a lattice, agreement at the meet is agreement at every common
coarser context. -/
theorem res_eq_res_of_res_inf {a b : R} {u : S.State a} {v : S.State b}
    (h : S.res (inf_le_left : a ⊓ b ≤ a) u = S.res inf_le_right v) {c : R} (hi : c ≤ a)
    (hj : c ≤ b) : S.res hi u = S.res hj v :=
  S.res_eq_res_of_res_eq_res inf_le_left inf_le_right (fun _ => le_inf) h hi hj

/-- Over a lattice, compatibility of a family is agreement of every two
members at their meet. -/
theorem compatible_iff_res_inf {ι : Type*} (F : ι → R) (x : ∀ i, S.State (F i)) :
    S.Compatible F x ↔
      ∀ i j, S.res (inf_le_left : F i ⊓ F j ≤ F i) (x i) = S.res inf_le_right (x j) where
  mp h _ _ := h inf_le_left inf_le_right
  mpr h _ i j hi hj := res_eq_res_of_res_inf S (h i j) hi hj

end Lattice

namespace FiniteRestriction

variable {R : Type*}

section Preorder

variable [Preorder R] (F : FiniteRestriction R)

/-- The underlying Amalgam restriction system. -/
def toRestrictionSystem : RestrictionSystem R where
  State := F.states
  res := F.restrict
  res_refl _ x := F.restrict_rfl _ x
  res_trans h₁ h₂ x := F.restrict_restrict h₁ h₂ x

@[simp]
theorem toRestrictionSystem_state (r : R) : F.toRestrictionSystem.State r = F.states r :=
  rfl

@[simp]
theorem toRestrictionSystem_res {a b : R} (h : a ≤ b) (s : F.states b) :
    F.toRestrictionSystem.res h s = F.restrict h s :=
  rfl

/-- A state is a compatible family over one context. -/
def stateEquivFamily (r : R) :
    F.states r ≃ F.toRestrictionSystem.CompatibleFamily fun _ : Unit => r where
  toFun s := ⟨fun _ => s, fun _ _ _ _ _ => rfl⟩
  invFun x := x.1 ()
  left_inv _ := rfl
  right_inv _ := rfl

end Preorder

section Lattice

variable [Lattice R] (F : FiniteRestriction R)

/-- Compatible pairs are the pullback of the two restriction legs to the
meet. -/
theorem compat_eq_pullback (a b : R) :
    F.Compat a b
      = Pullback (F.toRestrictionSystem.res (inf_le_left : a ⊓ b ≤ a))
          (F.toRestrictionSystem.res inf_le_right) :=
  rfl

/-- The canonical comparison is the universal map into the pullback. -/
theorem compare_eq_lift (a b : R) :
    F.compare a b
      = Pullback.lift (p := F.toRestrictionSystem.res (inf_le_left : a ⊓ b ≤ a))
          (q := F.toRestrictionSystem.res inf_le_right)
          (F.toRestrictionSystem.res le_sup_left) (F.toRestrictionSystem.res le_sup_right)
          fun s => (F.restrict_restrict _ _ s).trans (F.restrict_restrict _ _ s).symm :=
  rfl

/-- Compatible pairs are compatible families over `![a, b]`. -/
def compatEquivFamily (a b : R) :
    F.Compat a b ≃ F.toRestrictionSystem.CompatibleFamily ![a, b] :=
  (F.toRestrictionSystem.binaryEquiv inf_le_left inf_le_right fun _ => le_inf).symm

/-- The restriction from the join to the pair `![a, b]`. -/
def joinPair (a b : R) : FamilyMap (fun _ : Unit => a ⊔ b) ![a, b] where
  index _ := ()
  le
    | 0 => le_sup_left
    | 1 => le_sup_right

/-- The canonical comparison is Amalgam restriction from the join. -/
theorem compatEquivFamily_compare (a b : R) (s : F.states (a ⊔ b)) :
    F.compatEquivFamily a b (F.compare a b s)
      = F.toRestrictionSystem.restrict (joinPair a b) (F.stateEquivFamily _ s) :=
  Subtype.ext (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩))

/-- Compatible triples are compatible families over `![a, b, c]`. -/
def compat3EquivFamily (a b c : R) :
    F.Compat3 a b c ≃ F.toRestrictionSystem.CompatibleFamily ![a, b, c] where
  toFun t := ⟨Fin.cons t.1.1 (Fin.cons t.1.2.1 (Fin.cons t.1.2.2 finZeroElim)), by
    obtain ⟨⟨x, y, z⟩, hab, hac, hbc⟩ := t
    have e := @res_eq_res_of_res_inf R _ F.toRestrictionSystem
    intro d i j hi hj
    match i, j, hi, hj with
    | 0, 0, _, _ => rfl
    | 0, 1, hi, hj => exact e hab hi hj
    | 0, 2, hi, hj => exact e hac hi hj
    | 1, 0, hi, hj => exact (e hab hj hi).symm
    | 1, 1, _, _ => rfl
    | 1, 2, hi, hj => exact e hbc hi hj
    | 2, 0, hi, hj => exact (e hac hj hi).symm
    | 2, 1, hi, hj => exact (e hbc hj hi).symm
    | 2, 2, _, _ => rfl⟩
  invFun x := ⟨(x.1 0, x.1 1, x.1 2),
    x.2 (i := 0) (j := 1) inf_le_left inf_le_right,
    x.2 (i := 0) (j := 2) inf_le_left inf_le_right,
    x.2 (i := 1) (j := 2) inf_le_left inf_le_right⟩
  left_inv _ := rfl
  right_inv x := Subtype.ext (funext fun i => by fin_cases i <;> rfl)

/-- The restriction from the join to the triple `![a, b, c]`. -/
def joinTriple (a b c : R) : FamilyMap (fun _ : Unit => a ⊔ b ⊔ c) ![a, b, c] where
  index _ := ()
  le
    | 0 => le_sup_left.trans le_sup_left
    | 1 => le_sup_right.trans le_sup_left
    | 2 => le_sup_right

/-- The canonical triple comparison is Amalgam restriction from the
join. -/
theorem compat3EquivFamily_compare3 (a b c : R) (s : F.states (a ⊔ b ⊔ c)) :
    F.compat3EquivFamily a b c (F.compare3 a b c s)
      = F.toRestrictionSystem.restrict (joinTriple a b c) (F.stateEquivFamily _ s) :=
  Subtype.ext (funext fun i => by fin_cases i <;> rfl)

/-- Compatible pairs fibered over the left state: the fiber of the
projection is the right leg's fiber (`Function.Pullback.fiberFstEquiv`). -/
def compatSigmaFstEquiv (a b : R) :
    F.Compat a b
      ≃ Σ s : F.states a,
          { u : F.states b // F.restrict inf_le_right u = F.restrict inf_le_left s } :=
  (Equiv.sigmaFiberEquiv (Pullback.fst (f := F.toRestrictionSystem.res
      (inf_le_left : a ⊓ b ≤ a)) (g := F.toRestrictionSystem.res inf_le_right))).symm.trans
    (Equiv.sigmaCongrRight fun s => Pullback.fiberFstEquiv s)

/-- The compatible-pair count summed over left states. -/
theorem card_compat_eq_sum_fst (a b : R) :
    Fintype.card (F.Compat a b)
      = ∑ s : F.states a,
          Fintype.card
            { u : F.states b // F.restrict inf_le_right u = F.restrict inf_le_left s } := by
  rw [Fintype.card_congr (F.compatSigmaFstEquiv a b), Fintype.card_sigma]

end Lattice

end FiniteRestriction

namespace Incidence

variable {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B)

/-- The extension profile is the cardinality of the fiber. -/
theorem ext_eq_natCard_fiber (b : B) : ext f b = Nat.card { a // f a = b } :=
  (Nat.card_eq_fintype_card).symm

/-- Positive extension count is a nonempty fiber. -/
theorem ext_pos_iff_nonempty_fiber (b : B) : 0 < ext f b ↔ Nonempty { a // f a = b } :=
  Fintype.card_pos_iff

/-- Reachedness through Amalgam's fiber criterion. -/
theorem ext_pos_iff_mem_range (b : B) : 0 < ext f b ↔ b ∈ Set.range f :=
  (ext_pos_iff_nonempty_fiber f b).trans (nonempty_fiber_iff_mem_range f b)

/-- Extension count at most one is a subsingleton fiber. -/
theorem ext_le_one_iff_subsingleton_fiber (b : B) :
    ext f b ≤ 1 ↔ Subsingleton { a // f a = b } :=
  Fintype.card_le_one_iff_subsingleton

/-- Extension count one is a uniquely inhabited fiber. -/
theorem ext_eq_one_iff_nonempty_unique_fiber (b : B) :
    ext f b = 1 ↔ Nonempty (Unique { a // f a = b }) :=
  Fintype.card_eq_one_iff_nonempty_unique

/-- The extension profile of a comparison counts the global states over
a compatible pair (`Function.Pullback.fiberLiftEquiv`). -/
theorem ext_compare_eq_card {R : Type*} [Lattice R] (F : FiniteRestriction R) (a b : R)
    (c : F.Compat a b) :
    ext (F.compare a b) c
      = Fintype.card { s : F.states (a ⊔ b) //
          F.restrict le_sup_left s = c.1.1 ∧ F.restrict le_sup_right s = c.1.2 } :=
  Fintype.card_congr (Pullback.fiberLiftEquiv c)

end Incidence

end Descent
