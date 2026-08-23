import Descent.Geometry.Chambers
import Descent.Realization.FiniteGibbs

/-!
# Derived kernels and chamber geometry

Geometry is an output. The raw defect is not a distance; the kernels
derived from a field on the two lattice sides are

    joinKernel K a b = 2 K (a ⊔ b) - K a - K b
    meetKernel K a b = K a + K b - 2 K (a ⊓ b)

and the defect is exactly half their gap. The triangle slack of each
kernel decomposes exactly into a defect value at a derived square plus two
order gaps, so sign and order hypotheses --- one chamber, one monotonicity
--- make the kernel a pseudometric, packaged as the canonical
`PseudoMetricSpace`. The sign hypothesis is necessary: a monotone field
outside the chamber breaks the triangle inequality.

Realizations land in this geometry with no hypotheses: log-partitions are
submodular and monotone, so every finite Gibbs realization induces a
canonical pseudometric on its context lattice.
-/

namespace Descent

variable {R : Type*} [Lattice R]

/-- The kernel derived from a field on the join side. -/
def joinKernel (K : ContextField R ℝ) (a b : R) : ℝ :=
  2 * K (a ⊔ b) - K a - K b

/-- The kernel derived from a field on the meet side. -/
def meetKernel (K : ContextField R ℝ) (a b : R) : ℝ :=
  K a + K b - 2 * K (a ⊓ b)

/-- The defect is half the gap between the derived kernels. -/
theorem meetKernel_sub_joinKernel (K : ContextField R ℝ) (a b : R) :
    meetKernel K a b - joinKernel K a b = 2 * defect K a b := by
  simp only [meetKernel, joinKernel, defect]
  ring

/-- The join kernel is the span corrected by the defect. -/
theorem joinKernel_eq (K : ContextField R ℝ) (a b : R) :
    joinKernel K a b = (K (a ⊔ b) - K (a ⊓ b)) - defect K a b := by
  simp only [joinKernel, defect]
  ring

/-- The meet kernel is the span extended by the defect. -/
theorem meetKernel_eq (K : ContextField R ℝ) (a b : R) :
    meetKernel K a b = (K (a ⊔ b) - K (a ⊓ b)) + defect K a b := by
  simp only [meetKernel, defect]
  ring

theorem joinKernel_comm (K : ContextField R ℝ) (a b : R) :
    joinKernel K a b = joinKernel K b a := by
  simp only [joinKernel, sup_comm a b]
  ring

theorem meetKernel_comm (K : ContextField R ℝ) (a b : R) :
    meetKernel K a b = meetKernel K b a := by
  simp only [meetKernel, inf_comm a b]
  ring

theorem joinKernel_self (K : ContextField R ℝ) (a : R) : joinKernel K a a = 0 := by
  simp only [joinKernel, sup_idem]
  ring

theorem meetKernel_self (K : ContextField R ℝ) (a : R) : meetKernel K a a = 0 := by
  simp only [meetKernel, inf_idem]
  ring

theorem joinKernel_nonneg {K : ContextField R ℝ} (hK : Monotone K) (a b : R) :
    0 ≤ joinKernel K a b := by
  have h1 := hK (le_sup_left : a ≤ a ⊔ b)
  have h2 := hK (le_sup_right : b ≤ a ⊔ b)
  simp only [joinKernel]
  linarith

theorem meetKernel_nonneg {K : ContextField R ℝ} (hK : Monotone K) (a b : R) :
    0 ≤ meetKernel K a b := by
  have h1 := hK (inf_le_left : a ⊓ b ≤ a)
  have h2 := hK (inf_le_right : a ⊓ b ≤ b)
  simp only [meetKernel]
  linarith

/-- Exact triangle decomposition for the join kernel: the slack is a defect
value at a derived square plus two order gaps. -/
theorem joinKernel_triangle_decomposition (K : ContextField R ℝ) (a b c : R) :
    joinKernel K a b + joinKernel K b c - joinKernel K a c
      = 2 * defect K (a ⊔ b) (b ⊔ c) + 2 * (K (a ⊔ b ⊔ c) - K (a ⊔ c))
        + 2 * (K ((a ⊔ b) ⊓ (b ⊔ c)) - K b) := by
  have hj : (a ⊔ b) ⊔ (b ⊔ c) = a ⊔ b ⊔ c := by
    rw [sup_assoc a b, ← sup_assoc b b c, sup_idem, ← sup_assoc]
  simp only [joinKernel, defect, hj]
  ring

/-- Exact triangle decomposition for the meet kernel. -/
theorem meetKernel_triangle_decomposition (K : ContextField R ℝ) (a b c : R) :
    meetKernel K a b + meetKernel K b c - meetKernel K a c
      = -(2 * defect K (a ⊓ b) (b ⊓ c)) + 2 * (K (a ⊓ c) - K (a ⊓ b ⊓ c))
        + 2 * (K b - K ((a ⊓ b) ⊔ (b ⊓ c))) := by
  have hm : (a ⊓ b) ⊓ (b ⊓ c) = a ⊓ b ⊓ c := by
    rw [inf_assoc a b, ← inf_assoc b b c, inf_idem, ← inf_assoc]
  simp only [meetKernel, defect, hm]
  ring

/-- On the submodular chamber, monotone fields obey the triangle inequality
for the join kernel. -/
theorem joinKernel_triangle {K : ContextField R ℝ} (hs : Submodular K)
    (hK : Monotone K) (a b c : R) :
    joinKernel K a c ≤ joinKernel K a b + joinKernel K b c := by
  have h0 := joinKernel_triangle_decomposition K a b c
  have h1 := hs (a ⊔ b) (b ⊔ c)
  have h2 : K (a ⊔ c) ≤ K (a ⊔ b ⊔ c) := hK (sup_le_sup_right le_sup_left c)
  have h3 : K b ≤ K ((a ⊔ b) ⊓ (b ⊔ c)) := hK (le_inf le_sup_right le_sup_left)
  linarith

/-- On the supermodular chamber, monotone fields obey the triangle
inequality for the meet kernel. -/
theorem meetKernel_triangle {K : ContextField R ℝ} (hs : Supermodular K)
    (hK : Monotone K) (a b c : R) :
    meetKernel K a c ≤ meetKernel K a b + meetKernel K b c := by
  have h0 := meetKernel_triangle_decomposition K a b c
  have h1 := hs (a ⊓ b) (b ⊓ c)
  have h2 : K (a ⊓ b ⊓ c) ≤ K (a ⊓ c) := hK (inf_le_inf_right c inf_le_left)
  have h3 : K ((a ⊓ b) ⊔ (b ⊓ c)) ≤ K b := hK (sup_le inf_le_right inf_le_left)
  linarith

/-- Chamber geometry: a monotone field in the submodular chamber generates
a canonical pseudometric, the join kernel. -/
@[instance_reducible]
noncomputable def Submodular.pseudoMetricSpace {K : ContextField R ℝ}
    (hs : Submodular K) (hK : Monotone K) : PseudoMetricSpace R where
  dist := joinKernel K
  dist_self := joinKernel_self K
  dist_comm := joinKernel_comm K
  dist_triangle a b c := joinKernel_triangle hs hK a b c

/-- Chamber geometry: a monotone field in the supermodular chamber
generates a canonical pseudometric, the meet kernel. -/
@[instance_reducible]
noncomputable def Supermodular.pseudoMetricSpace {K : ContextField R ℝ}
    (hs : Supermodular K) (hK : Monotone K) : PseudoMetricSpace R where
  dist := meetKernel K
  dist_self := meetKernel_self K
  dist_comm := meetKernel_comm K
  dist_triangle a b c := meetKernel_triangle hs hK a b c

/-- The sign hypothesis is necessary: a monotone field outside the
submodular chamber breaks the triangle inequality for the join kernel. -/
theorem exists_monotone_joinKernel_triangle_fails :
    ∃ K : ContextField Square ℝ, Monotone K ∧
      ¬joinKernel K Square.left Square.right
        ≤ joinKernel K Square.left ⊥ + joinKernel K ⊥ Square.right := by
  classical
  refine ⟨fun p => if p = ⊤ then 1 else 0, ?_, ?_⟩
  · refine Square.monotone_iff.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
      norm_num [show Square.left ≠ (⊤ : Square) from by decide,
        show Square.right ≠ (⊤ : Square) from by decide,
        show (⊥ : Square) ≠ (⊤ : Square) from by decide]
  · rw [joinKernel, joinKernel, joinKernel,
      show Square.left ⊔ Square.right = (⊤ : Square) from by decide,
      show Square.left ⊔ (⊥ : Square) = Square.left from by decide,
      show (⊥ : Square) ⊔ Square.right = Square.right from by decide]
    norm_num [show Square.left ≠ (⊤ : Square) from by decide,
      show Square.right ≠ (⊤ : Square) from by decide,
      show (⊥ : Square) ≠ (⊤ : Square) from by decide]

/-! ### The Gibbs chamber -/

namespace FiniteGibbs

variable {Ω : Type*} [DecidableEq Ω] (X : FiniteGibbs R Ω)

/-- The recognition bridge in chamber language: log-partitions lie in the
submodular chamber. -/
theorem submodular_logPartition : Submodular X.logPartition :=
  X.defect_logPartition_nonneg

/-- Every finite Gibbs realization induces a canonical pseudometric on its
context lattice: the join kernel of its log-partition. -/
@[instance_reducible]
noncomputable def pseudoMetricSpace : PseudoMetricSpace R :=
  X.submodular_logPartition.pseudoMetricSpace X.logPartition_mono

end FiniteGibbs

end Descent
