import TwoAxisHelicoid.SmoothCoefficientTranslations
import TwoAxisHelicoid.PlaneConductivityL2
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace TwoAxisHelicoid
open MeasureTheory Complex Filter Set
open scoped ENNReal ContDiff BoundedContinuousFunction

private theorem boundedCoefficient_memLp (f : ℂ →ᵇ ℝ) : MemLp (⇑f) ∞ (volume:Measure ℂ) :=
  memLp_top_of_bound f.continuous.aestronglyMeasurable ‖f‖ (ae_of_all _ f.norm_coe_le_norm)

/-- The bounded coefficient acts on *global*, infinite-volume L². Its
dependence on the coefficient is continuous linear in the supremum norm. -/
theorem exists_bounded_coefficient_multiplier :
    ∃ J : (ℂ →ᵇ ℝ) →L[ℝ] Lp ℂ 2 (volume:Measure ℂ) →L[ℝ] Lp ℂ 2 (volume:Measure ℂ),
      ∀ f w, ⇑(J f w) =ᵐ[volume] (fun z => f z • w z) := by
  let lift := fun f : ℂ →ᵇ ℝ => (boundedCoefficient_memLp f).toLp (⇑f)
  have rep (f : ℂ →ᵇ ℝ) : ⇑(lift f) =ᵐ[volume] ⇑f := (boundedCoefficient_memLp f).coeFn_toLp
  let lin : (ℂ →ᵇ ℝ) →ₗ[ℝ] Lp ℝ ∞ (volume:Measure ℂ) := {
    toFun := lift
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [rep (f+g),rep f,rep g,Lp.coeFn_add (lift f) (lift g)] with z h a b e
      rw [h,e,Pi.add_apply,a,b]
      rfl
    map_smul' := by
      intro r f
      apply Lp.ext
      filter_upwards [rep (r • f),rep f,Lp.coeFn_smul r (lift f)] with z h a e
      change (lift (r • f)) z=(r • lift f) z
      rw [h,e,Pi.smul_apply,a]
      rfl }
  have bd (f : ℂ →ᵇ ℝ) : ‖lin f‖≤1*‖f‖ := by
    rw [one_mul]
    change ‖(boundedCoefficient_memLp f).toLp (⇑f)‖≤_
    rw [Lp.norm_toLp,eLpNorm_exponent_top f.continuous.aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound (ae_of_all _ f.norm_coe_le_norm))).trans_eq
      (ENNReal.toReal_ofReal (norm_nonneg _))
  let H := lin.mkContinuous 1 bd
  let B : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  let J := (B.holderL (volume:Measure ℂ) ∞ 2 2).comp H
  refine ⟨J,?_⟩
  intro f w
  have act := B.coeFn_holder (r:=2) (lift f) w
  filter_upwards [act,rep f] with z hz hf
  change B.holder 2 (lift f) w z=f z • w z
  rw [hz,hf]
  rfl
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_bounded_coefficient_multiplier
