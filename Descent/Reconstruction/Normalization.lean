import Descent.Core.Gauge

/-!
# Normalization

Defect data determines at most the class `[K]`. Recovering the field itself
needs a normalization datum, and every adequacy theorem must name it. Here the
datum is a value restriction: `T.domRestrict K` records `K` on a subset `T` of
contexts, and `T` is `AdequateOn` when class together with restriction is
injective.

Adequacy is a property of the gauge alone: `T` is adequate exactly when no
nonzero valuation vanishes on `T` (`adequateOn_iff_eq_zero`). Sharp
classifications for concrete context lattices live with the models.
-/

namespace Descent

variable {R A : Type*} [Lattice R] [AddCommGroup A]

/-- `T` is an adequate normalization datum when class together with the
values on `T` determines the field. -/
def AdequateOn (T : Set R) (A : Type*) [AddCommGroup A] : Prop :=
  Function.Injective fun K : ContextField R A => (Observable.mk K, T.domRestrict K)

/-- Adequacy is a property of the gauge: `T` is adequate exactly when no
nonzero valuation vanishes on `T`. -/
theorem adequateOn_iff_eq_zero {T : Set R} :
    AdequateOn T A
      ↔ ∀ K : ContextField R A, IsValuation K → T.domRestrict K = 0 → K = 0 := by
  constructor
  · intro h K hK hT
    refine h (a₁ := K) (a₂ := 0) (Prod.ext ?_ ?_)
    · exact Observable.mk_eq_mk.mpr
        (Eq.trans (isValuation_iff_defect_eq_zero.mp hK) defect_zero.symm)
    · exact hT
  · intro h K K' hKK'
    obtain ⟨hcl, hres⟩ := Prod.ext_iff.mp hKK'
    have hval : IsValuation (K - K') :=
      defectEquiv_iff_sub_isValuation.mp (Observable.mk_eq_mk.mp hcl)
    have hzero : T.domRestrict (K - K') = 0 := by
      funext t
      have h1 : K t.val = K' t.val := congrFun hres t
      show K t.val - K' t.val = 0
      rw [h1, sub_self]
    have := h (K - K') hval hzero
    rwa [sub_eq_zero] at this

/-- Enlarging the normalization datum preserves adequacy. -/
theorem AdequateOn.mono {T T' : Set R} (hTT' : T ⊆ T') (h : AdequateOn T A) :
    AdequateOn T' A := by
  rw [adequateOn_iff_eq_zero] at h ⊢
  intro K hK hT'
  refine h K hK ?_
  funext t
  exact congrFun hT' ⟨t.val, hTT' t.property⟩

/-- The complete value datum is always adequate. -/
theorem adequateOn_univ : AdequateOn (Set.univ : Set R) A := by
  rw [adequateOn_iff_eq_zero]
  intro K _ hK
  funext r
  exact congrFun hK ⟨r, Set.mem_univ r⟩

end Descent
