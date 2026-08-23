import Descent.Models.Diamond
import Descent.Realization.Restriction

/-!
# The diamond code system

The restriction realization of the diamond witness: bottom `Unit`, each
atom `Bool`, top the three codewords `{000, 011, 101}`, restrictions
from the top the coordinate projections.

The four irredundant measurements of the diamond become literal,
proved local-to-global losses: every top-to-atom restriction is
surjective; each atom-pair comparison injects the three global states
into the four compatible pairs and misses exactly one; the triple
comparison injects them into the eight compatible triples and misses
exactly five. The logarithmic cardinality field is exactly the witness
field `logCountField`, and its canonical datum is exactly
`(log (4/3), log (4/3), log (4/3), log (8/3))`.
-/

namespace Descent

namespace Diamond

/-- The three codewords `000`, `011`, `101`. -/
inductive Code : Type
  | c0 | c1 | c2
deriving DecidableEq

instance : Fintype Code :=
  ⟨{.c0, .c1, .c2}, fun c => by cases c <;> decide⟩

theorem card_code : Fintype.card Code = 3 :=
  rfl

/-- First coordinate of the codewords. -/
def px : Code → Bool
  | .c0 => false
  | .c1 => false
  | .c2 => true

/-- Second coordinate. -/
def py : Code → Bool
  | .c0 => false
  | .c1 => true
  | .c2 => false

/-- Third coordinate. -/
def pz : Code → Bool
  | .c0 => false
  | .c1 => true
  | .c2 => true

/-- The state types of the code system. -/
def codeStates : Diamond → Type
  | .bot => Unit
  | .x => Bool
  | .y => Bool
  | .z => Bool
  | .top => Code

/-- Restriction: coordinate projection from the top, collapse to the
bottom, identity on a context. -/
def codeRestrict : ∀ {a b : Diamond}, a ≤ b → codeStates b → codeStates a
  | .bot, _, _, _ => ()
  | .x, .x, _, s => s
  | .x, .top, _, s => px s
  | .y, .y, _, s => s
  | .y, .top, _, s => py s
  | .z, .z, _, s => s
  | .z, .top, _, s => pz s
  | .top, .top, _, s => s
  | .x, .bot, h, _ => absurd h (by decide)
  | .x, .y, h, _ => absurd h (by decide)
  | .x, .z, h, _ => absurd h (by decide)
  | .y, .bot, h, _ => absurd h (by decide)
  | .y, .x, h, _ => absurd h (by decide)
  | .y, .z, h, _ => absurd h (by decide)
  | .z, .bot, h, _ => absurd h (by decide)
  | .z, .x, h, _ => absurd h (by decide)
  | .z, .y, h, _ => absurd h (by decide)
  | .top, .bot, h, _ => absurd h (by decide)
  | .top, .x, h, _ => absurd h (by decide)
  | .top, .y, h, _ => absurd h (by decide)
  | .top, .z, h, _ => absurd h (by decide)

/-- The diamond code system as a finite restriction system. -/
def codeSystem : FiniteRestriction Diamond where
  states := codeStates
  fintype d := by
    cases d
    exacts [inferInstanceAs (Fintype Unit), inferInstanceAs (Fintype Bool),
      inferInstanceAs (Fintype Bool), inferInstanceAs (Fintype Bool),
      inferInstanceAs (Fintype Code)]
  nonempty d := by
    cases d
    exacts [⟨()⟩, ⟨false⟩, ⟨false⟩, ⟨false⟩, ⟨.c0⟩]
  decEq d := by
    cases d
    exacts [inferInstanceAs (DecidableEq Unit),
      inferInstanceAs (DecidableEq Bool), inferInstanceAs (DecidableEq Bool),
      inferInstanceAs (DecidableEq Bool), inferInstanceAs (DecidableEq Code)]
  restrict := codeRestrict
  restrict_rfl r s := by
    cases r <;> rfl
  restrict_restrict {a b c} hab hbc s := by
    cases a <;> cases b <;> cases c <;>
      first
        | rfl
        | exact absurd hab (by decide)
        | exact absurd hbc (by decide)

/-! ### The obstruction, exactly -/

/-- Every top-to-atom restriction is surjective. -/
theorem surjective_restrict_x :
    Function.Surjective (codeSystem.restrict (show x ≤ top from by decide)) := by
  decide

theorem surjective_restrict_y :
    Function.Surjective (codeSystem.restrict (show y ≤ top from by decide)) := by
  decide

theorem surjective_restrict_z :
    Function.Surjective (codeSystem.restrict (show z ≤ top from by decide)) := by
  decide

/-- Each atom-pair comparison injects the three global states… -/
theorem compare_xy_injective :
    Function.Injective (codeSystem.compare x y) := by
  decide

theorem compare_xz_injective :
    Function.Injective (codeSystem.compare x z) := by
  decide

theorem compare_yz_injective :
    Function.Injective (codeSystem.compare y z) := by
  decide

/-- …into four compatible pairs… -/
theorem card_compat_xy : Fintype.card (codeSystem.Compat x y) = 4 := by
  decide

theorem card_compat_xz : Fintype.card (codeSystem.Compat x z) = 4 := by
  decide

theorem card_compat_yz : Fintype.card (codeSystem.Compat y z) = 4 := by
  decide

/-- …and misses exactly one. -/
theorem card_missed_xy :
    Fintype.card
      {p : codeSystem.Compat x y // ∀ s, codeSystem.compare x y s ≠ p} = 1 := by
  decide

theorem card_missed_xz :
    Fintype.card
      {p : codeSystem.Compat x z // ∀ s, codeSystem.compare x z s ≠ p} = 1 := by
  decide

theorem card_missed_yz :
    Fintype.card
      {p : codeSystem.Compat y z // ∀ s, codeSystem.compare y z s ≠ p} = 1 := by
  decide

/-- The triple comparison injects the three global states into the eight
compatible triples… -/
theorem compare3_injective :
    Function.Injective (codeSystem.compare3 x y z) := by
  decide

theorem card_compat3 : Fintype.card (codeSystem.Compat3 x y z) = 8 := by
  decide

/-- …and misses exactly five. -/
theorem card_missed3 :
    Fintype.card
      {t : codeSystem.Compat3 x y z //
        ∀ s, codeSystem.compare3 x y z s ≠ t} = 5 := by
  decide

/-- The logarithmic cardinality field of the code system is exactly the
witness field. -/
theorem logCard_codeSystem : codeSystem.logCard = logCountField := by
  have c1 : Fintype.card (codeSystem.states Diamond.bot) = 1 := by decide
  have c2 : Fintype.card (codeSystem.states Diamond.x) = 2 := by decide
  have c3 : Fintype.card (codeSystem.states Diamond.y) = 2 := by decide
  have c4 : Fintype.card (codeSystem.states Diamond.z) = 2 := by decide
  have c5 : Fintype.card (codeSystem.states Diamond.top) = 3 := by decide
  funext r
  cases r <;>
    · simp only [FiniteRestriction.logCard, logCountField, countField,
        c1, c2, c3, c4, c5]
      norm_num

/-- The canonical datum of the witness field, exactly: the four
irredundant measurements are literal local-to-global losses. -/
theorem canonicalDatum_logCountField_eq :
    canonicalDatum logCountField
      = (Real.log (4 / 3), Real.log (4 / 3), Real.log (4 / 3),
          Real.log (8 / 3)) := by
  have h43 : Real.log ((4 : ℝ) / 3) = Real.log 2 + Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 * 2 from by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have h83 : Real.log ((8 : ℝ) / 3)
      = Real.log 2 + Real.log 2 + Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2 * (2 * 2) from by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have e1 : defect logCountField x y = Real.log (4 / 3) := by
    rw [defect_def, show (x ⊓ y : Diamond) = bot from by decide,
      show (x ⊔ y : Diamond) = top from by decide]
    show Real.log 2 + Real.log 2 - Real.log 1 - Real.log 3 = _
    rw [Real.log_one, h43]
    ring
  have e2 : defect logCountField x z = Real.log (4 / 3) := by
    rw [defect_def, show (x ⊓ z : Diamond) = bot from by decide,
      show (x ⊔ z : Diamond) = top from by decide]
    show Real.log 2 + Real.log 2 - Real.log 1 - Real.log 3 = _
    rw [Real.log_one, h43]
    ring
  have e3 : defect logCountField y z = Real.log (4 / 3) := by
    rw [defect_def, show (y ⊓ z : Diamond) = bot from by decide,
      show (y ⊔ z : Diamond) = top from by decide]
    show Real.log 2 + Real.log 2 - Real.log 1 - Real.log 3 = _
    rw [Real.log_one, h43]
    ring
  have e4 : defect3 logCountField x y z = Real.log (8 / 3) := by
    rw [defect3_def, show (x ⊓ y ⊓ z : Diamond) = bot from by decide,
      show (x ⊓ y : Diamond) = bot from by decide,
      show (x ⊓ z : Diamond) = bot from by decide,
      show (y ⊓ z : Diamond) = bot from by decide,
      show (x ⊔ y ⊔ z : Diamond) = top from by decide]
    show Real.log 2 + Real.log 2 + Real.log 2 - Real.log 1 - Real.log 1
        - Real.log 1 + Real.log 1 - Real.log 3 = _
    rw [Real.log_one, h83]
    ring
  rw [canonicalDatum, e1, e2, e3, e4]

end Diamond

end Descent
