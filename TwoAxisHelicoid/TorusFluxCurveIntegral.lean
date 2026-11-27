import TwoAxisHelicoid.HarmonicTorusHeightFlux
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

namespace TwoAxisHelicoid
open Complex Set MeasureTheory

noncomputable def complexPlaneOneForm (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ :=
  f z • ContinuousLinearMap.id ℂ ℂ

theorem PlanePolygon.curveIntegral_eq {Ω : Set ℂ} {x y : ℂ} (p : PlanePolygon Ω x y)
    {f : ℂ → ℂ} (hf : ContinuousOn f Ω) :
    CurveIntegrable (complexPlaneOneForm f) (p.pathIn.map continuous_subtype_val) ∧
    curveIntegral (complexPlaneOneForm f) (p.pathIn.map continuous_subtype_val) = p.integral f := by
  induction p with
  | refl z hz =>
    exact ⟨CurveIntegrable.refl _ _,curveIntegral_refl _ _⟩
  | trans p q hp hq =>
    change CurveIntegrable _ ((p.pathIn.trans q.pathIn).map _) ∧
      curveIntegral _ ((p.pathIn.trans q.pathIn).map _) = p.integral f+q.integral f
    rw [Path.map_trans]
    exact ⟨hp.1.trans hq.1,by rw [curveIntegral_trans hp.1 hq.1,hp.2,hq.2]⟩
  | step a b h =>
    change CurveIntegrable _ (Path.segment a b) ∧ curveIntegral _ (Path.segment a b) = _
    have hc : ContinuousOn (fun s : ℝ => f (AffineMap.lineMap (k := ℝ) a b s)) (Icc 0 1) :=
      hf.comp AffineMap.lineMap_continuous.continuousOn h
    constructor
    · rw [curveIntegrable_segment]
      exact (hc.mul_const (b-a)).intervalIntegrable_of_Icc (by norm_num)
    · rw [curveIntegral_segment]
      change (∫ s : ℝ in 0..1, f (AffineMap.lineMap (k := ℝ) a b s)*(b-a)) =
        (b-a)*∫ s : ℝ in 0..1, f (AffineMap.lineMap (k := ℝ) a b s)
      rw [intervalIntegral.integral_mul_const,mul_comm]

/-- Nonzero flux measured by mathlib's curve integral along a lift of the
closed punctured-torus path constructed by the argument. -/
theorem harmonic_torus_nonzero_flux_curveIntegral (L : PeriodPair) (H : PuncturedPeriodTorus L → ℝ)
    (hh : ∀ z ∉ L.lattice, InnerProductSpace.HarmonicAt (puncturedTorusPullback L H) z)
    (hm : MeromorphicAt (scalarComplexCoefficient (puncturedTorusPullback L H)) 0)
    (ho : meromorphicOrderAt (scalarComplexCoefficient (puncturedTorusPullback L H)) 0 = (-2 : ℤ)) :
    ∃ γ : TorusPeriodPolygon L,
      (curveIntegral (complexPlaneOneForm (scalarComplexCoefficient (puncturedTorusPullback L H)))
        (γ.edges.pathIn.map continuous_subtype_val)).im ≠ 0 := by
  obtain ⟨γ,hγ⟩ := harmonic_punctured_torus_has_nonzero_height_flux L H hh hm ho
  refine ⟨γ,?_⟩
  rw [(γ.edges.curveIntegral_eq (fun z hz => (scalarComplexCoefficient_analyticAt
    (hh z hz)).continuousAt.continuousWithinAt)).2]
  exact hγ

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_torus_nonzero_flux_curveIntegral
