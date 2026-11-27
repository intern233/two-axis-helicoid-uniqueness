import TwoAxisHelicoid.SmoothParameterCoefficient
import TwoAxisHelicoid.BoundedCoefficientMultiplier
import TwoAxisHelicoid.FrozenPlaneConductivity
import TwoAxisHelicoid.PlaneWeakConductivity

namespace TwoAxisHelicoid
open MeasureTheory Complex Set InnerProductSpace
open scoped ContDiff RealInnerProductSpace BoundedContinuousFunction

private noncomputable def frozenTrace (F : ℂ → ℝ) (sf : ContDiff ℝ ∞ F) (p : ℂ) (x : ℝ × ℂ) : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.const ℂ (F p) +
    compactParameterTrace _ (planeFreezePerturbation_smooth sf p).continuous (planeFreezePerturbation_compact F p) x

private theorem frozenTrace_smooth {F : ℂ → ℝ} (sf : ContDiff ℝ ∞ F) (p : ℂ) :
    ContDiff ℝ ∞ (frozenTrace F sf p) :=
  contDiff_const.add (smooth_compactParameterTrace (planeFreezePerturbation_smooth sf p) (planeFreezePerturbation_compact F p))

/-- The rescaled conductivity is smooth in scale and translation in operator
norm and retains the original energy lower bound on the whole plane. -/
theorem exists_frozen_plane_flux_operator {A B C : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C) (p : ℂ) {k : ℝ}
    (low : ∀ z x y, (x^2+y^2)/k≤C z*x^2-2*B z*x*y+A z*y^2) :
    ∃ T : ℝ × ℂ → Lp ℂ 2 (volume:Measure ℂ) →L[ℝ] Lp ℂ 2 (volume:Measure ℂ),
      ContDiff ℝ ∞ T ∧
      (∀ t w, ⇑(T t w) =ᵐ[volume] (fun z => planeMetricFlux (planeFrozenCoefficient A p t.1)
        (planeFrozenCoefficient B p t.1) (planeFrozenCoefficient C p t.1) (z+t.2) (w z))) ∧
      ∀ t w, k⁻¹*‖w‖^2≤⟪T t w,w⟫_ℝ := by
  let E := Lp ℂ 2 (volume:Measure ℂ)
  obtain ⟨J,hJ⟩ := exists_bounded_coefficient_multiplier
  let X := ofRealCLM.comp reCLM
  let Y : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℂ)-X
  let Z : ℂ →L[ℝ] ℂ := -(ofRealCLM.comp imCLM)-I • X
  let px := X.compLpL 2 (volume:Measure ℂ)
  let py := Y.compLpL 2 (volume:Measure ℂ)
  let pz := Z.compLpL 2 (volume:Measure ℂ)
  let T := fun t => (J (frozenTrace C sc p t)).comp px +
    (J (frozenTrace A sa p t)).comp py + (J (frozenTrace B sb p t)).comp pz
  have s1 := (J.contDiff.comp (frozenTrace_smooth sc p)).clm_comp (contDiff_const (c:=px))
  have s2 := (J.contDiff.comp (frozenTrace_smooth sa p)).clm_comp (contDiff_const (c:=py))
  have s3 := (J.contDiff.comp (frozenTrace_smooth sb p)).clm_comp (contDiff_const (c:=pz))
  have act (t : ℝ × ℂ) (w : E) : ⇑(T t w) =ᵐ[volume] fun z =>
      planeMetricFlux (planeFrozenCoefficient A p t.1) (planeFrozenCoefficient B p t.1)
        (planeFrozenCoefficient C p t.1) (z+t.2) (w z) := by
    let x := J (frozenTrace C sc p t) (px w)
    let y := J (frozenTrace A sa p t) (py w)
    let z := J (frozenTrace B sb p t) (pz w)
    change ⇑((x+y)+z) =ᵐ[volume] _
    filter_upwards [Lp.coeFn_add (x+y) z,Lp.coeFn_add x y,
      hJ (frozenTrace C sc p t) (px w),hJ (frozenTrace A sa p t) (py w),hJ (frozenTrace B sb p t) (pz w),
      X.coeFn_compLpL w,Y.coeFn_compLpL w,Z.coeFn_compLpL w]
      with v total first xx yy zz d1 d2 d3
    rw [total,Pi.add_apply,first,Pi.add_apply,xx,yy,zz,d1,d2,d3]
    change planeFrozenCoefficient C p t.1 (v+t.2) • X (w v)+planeFrozenCoefficient A p t.1 (v+t.2) • Y (w v)+
      planeFrozenCoefficient B p t.1 (v+t.2) • Z (w v)=_
    apply Complex.ext <;> simp [planeMetricFlux,X,Y,Z,Complex.mul_re,Complex.mul_im] <;> ring
  refine ⟨T,(s1.add s2).add s3,act,?_⟩
  intro t w
  rw [←real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def,←integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner (𝕜:=ℝ) w w).const_mul _) (L2.integrable_inner (𝕜:=ℝ) (T t w) w)
  filter_upwards [act t w] with z hz
  rw [hz,real_inner_self_eq_norm_sq,planeMetricFlux_energy]
  have length : ‖w z‖^2=(w z).re^2+(w z).im^2 := by linarith [Complex.sq_norm_sub_sq_re (w z)]
  rw [length,mul_comm,←div_eq_mul_inv]
  exact planeFrozenCoefficient_lower A B C p low t.1 (z+t.2) _ _
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_frozen_plane_flux_operator
