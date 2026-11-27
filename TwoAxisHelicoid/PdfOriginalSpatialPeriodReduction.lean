import TwoAxisHelicoid.OriginalHeightPeriod
import TwoAxisHelicoid.OriginalPeriodBridge
import TwoAxisHelicoid.VerticalZeroDomain

namespace TwoAxisHelicoid.PdfVertical
open Set

/-- Eliminate the two spatial generators in favor of the scalar sigma
period and the actual vertical root. The upper bound on the height is
a conclusion of spatial closure. -/
theorem spatial_generators_iff_original_scalar {t a c : ℝ} (ht : 0<t)
    (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0) :
    (∀ j : Fin 3, (originalCoordinatePeriod t a c ht j).re=0 ∧
      (conjugateCoordinatePeriod t a c ht j).re=0) ↔
    t<ellipticVerticalUpper ∧ a=verticalA t ∧ originalPeriodAlong t=0 := by
  rw [original_all_generators_close_iff ht ⟨ha.1,by linarith [ha.2]⟩ hc]
  constructor
  · rintro ⟨vertical,horizontal⟩
    obtain ⟨upper,eqn⟩ := (thetaG_zero_iff_verticalA ht ha).mp vertical
    refine ⟨upper,eqn,(originalPeriodAlong_eq_actual ⟨ht,upper⟩).trans ?_⟩
    change thetaHorizontalPeriod t (verticalA t)=0
    rwa [← eqn]
  · rintro ⟨upper,rfl,horizontal⟩
    exact ⟨(verticalA_spec ⟨ht,upper⟩).2,(originalPeriodAlong_eq_actual ⟨ht,upper⟩).symm.trans horizontal⟩

/-- Any unique scalar zero on a chosen height set yields exactly one
admissible pair closing all six real coordinate periods on that set. -/
theorem unique_generators_on_of_scalar {S : Set ℝ} (domain : S⊆Ioo (0:ℝ) ellipticVerticalUpper)
    (root : ∃! t : ℝ, t∈S ∧ originalPeriodAlong t=0) (c : ℝ) (hc : c≠0) :
    ∃! p : ℝ × ℝ, p.1∈S ∧ ∃ ht : 0<p.1, p.2∈Ioo (0:ℝ) 1 ∧
      ∀ j : Fin 3, (originalCoordinatePeriod p.1 p.2 c ht j).re=0 ∧
        (conjugateCoordinatePeriod p.1 p.2 c ht j).re=0 := by
  obtain ⟨t,⟨hs,zero⟩,only⟩ := root
  have dom := domain hs
  have unit := (verticalA_spec dom).1
  refine ⟨(t,verticalA t),⟨hs,dom.1,unit,(spatial_generators_iff_original_scalar dom.1 unit hc).mpr
    ⟨dom.2,rfl,zero⟩⟩,?_⟩
  rintro ⟨u,b⟩ ⟨hu,hp,hb,closed⟩
  obtain ⟨_,ab,hz⟩ := (spatial_generators_iff_original_scalar hp hb hc).mp closed
  have eqn := only u ⟨hu,hz⟩
  exact Prod.ext eqn (ab.trans (congrArg verticalA eqn))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.unique_generators_on_of_scalar

