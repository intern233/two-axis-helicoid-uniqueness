import TwoAxisHelicoid.FiniteGaussSphericalEstimate
import TwoAxisHelicoid.MinimalHorizontalDevelopmentForm
import TwoAxisHelicoid.PositiveMinimalChangeOfCoordinates
import Mathlib.Analysis.Complex.HasPrimitives

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology
open scoped Topology ContDiff

noncomputable def measuredChartGauss (X : ℂ → Fin 3 → ℝ) (z : ℂ) : ℂ :=
  gaussCoordinateOfNormal (unitCrossNormal (fderiv ℝ X z 1) (fderiv ℝ X z I))

noncomputable def complexScaleReal (c : ℂ) : ℂ →L[ℝ] ℂ :=
  ((1 : ℂ →L[ℂ] ℂ).smulRight c).restrictScalars ℝ

private theorem horizontal_form_in_conformal_coordinate {Y : ℂ → Fin 3 → ℝ} {w : ℂ} {p : Fin 3 → ℂ}
    (hp : ComplexNull p) (np : p≠0) (d : HasFDerivAt Y (nullRealDerivative p) w) :
    physicalHorizontalForm Y w=complexScaleReal (nullHorizontalMinus p) := by
  ext v
  change horizontalNullCovector (unitCrossNormal (fderiv ℝ Y w 1) (fderiv ℝ Y w I)) (fderiv ℝ Y w v)=v*nullHorizontalMinus p
  rw [d.fderiv]
  exact horizontalNullCovector_of_null hp np v

/-- On any regular minimal patch separated from the north pole at its
center, the measured Gauss coordinate is holomorphic relative to the
physical horizontal differential. The latter has a local C² primitive,
and its norm recovers the exact speed in arbitrary physical coordinates. -/
theorem minimal_chart_local_horizontal_development {X : ℂ → Fin 3 → ℝ} {a : ℂ}
    (data : ∀ᶠ z in 𝓝 a, ContDiffAt ℝ ∞ X z ∧ Function.Injective (fderiv ℝ X z) ∧ coordinateMeanCurvature X z=0)
    (bound : unitCrossNormal (fderiv ℝ X a 1) (fderiv ℝ X a I) 2≤15/16) :
    (∃ H : ℂ → ℂ, ContDiffAt ℝ 2 H a ∧ ∀ᶠ z in 𝓝 a, HasFDerivAt H (physicalHorizontalForm X z) z) ∧
    (∃ q : ℂ, HasFDerivAt (measuredChartGauss X) ((complexScaleReal q).comp (physicalHorizontalForm X a)) a) ∧
    ‖measuredChartGauss X a‖≤6 ∧ (euclideanUnitChartNormal X =ᶠ[𝓝 a] coordinateToEuclidean ∘ finiteGaussNormal ∘ measuredChartGauss X) ∧
    ∀ v, ‖coordinateToEuclidean (fderiv ℝ X a v)‖=
      (1+normSq (measuredChartGauss X a))/2*‖physicalHorizontalForm X a v‖ := by
  obtain ⟨k,ka,orientation,_,complexData⟩ := positive_minimal_change_of_coordinates data
  let Y := X ∘ k.symm
  let p := immersionComplexCoefficient Y
  let l := fun w => nullHorizontalMinus (p w)
  let g := fun w => nullGauss (p w)
  let z := k a
  have dk := (orientation.self_of_nhds.1.differentiableAt (by simp)).hasFDerivAt
  have transfer : ∀ᶠ x in 𝓝 a, (unitCrossNormal (fderiv ℝ X x 1) (fderiv ℝ X x I)=
      unitCrossNormal (nullRealDerivative (p (k x)) 1) (nullRealDerivative (p (k x)) I)) ∧
      physicalHorizontalForm X x=(complexScaleReal (l (k x))).comp (fderiv ℝ k x) ∧
      fderiv ℝ X x=(nullRealDerivative (p (k x))).comp (fderiv ℝ k x) := by
    filter_upwards [k.open_source.mem_nhds ka,orientation,(k.continuousAt ka).eventually complexData] with x hx ori h
    obtain ⟨_,hp,np,d⟩ := h
    have same : X =ᶠ[𝓝 x] Y ∘ k := by
      filter_upwards [k.open_source.mem_nhds hx] with y hy
      exact congrArg X (k.left_inv hy).symm
    obtain ⟨norm,form⟩ := physicalHorizontalForm_pullback same d.differentiableAt
      (ori.1.differentiableAt (by simp)) ori.2
    rw [d.fderiv] at norm
    rw [horizontal_form_in_conformal_coordinate hp np d] at form
    exact ⟨norm,form,same.fderiv_eq.trans (d.comp x (ori.1.differentiableAt (by simp)).hasFDerivAt).fderiv⟩
  obtain ⟨an,hp,np,_⟩ := complexData.self_of_nhds
  have atCenter := transfer.self_of_nhds
  rw [atCenter.1] at bound
  obtain ⟨nonzero,_,bounded⟩ := null_gauss_chart_of_normal_bound hp np bound
  have al : AnalyticAt ℂ l z := (an 0).sub (analyticAt_const.mul (an 1))
  have ag : AnalyticAt ℂ g z := (an 2).div al nonzero
  have near : ∀ᶠ x in 𝓝 a, unitCrossNormal (fderiv ℝ X x 1) (fderiv ℝ X x I)=finiteGaussNormal (g (k x)) := by
    filter_upwards [transfer,(k.continuousAt ka).eventually complexData,
      (k.continuousAt ka).eventually (al.continuousAt.eventually_ne nonzero)] with x tr cx nz
    exact tr.1.trans ((congrArg (fun q => unitCrossNormal (nullRealDerivative q 1) (nullRealDerivative q I))
      (null_in_finite_gauss_chart cx.2.1 nz)).trans (finiteGaussTriple_oriented_unit_normal _ nz))
  have eqG : measuredChartGauss X =ᶠ[𝓝 a] g ∘ k := near.mono fun _ h =>
    (congrArg gaussCoordinateOfNormal h).trans (gaussCoordinateOfNormal_finite _)
  obtain ⟨r,rp,nb⟩ := Metric.mem_nhds_iff.mp al.eventually_analyticAt
  have dif : DifferentiableOn ℂ l (ball z r) := fun w hw => (nb hw).differentiableAt.differentiableWithinAt
  obtain ⟨H,_,der⟩ := dif.isExactOn_ball.with_val_at z 0
  have hh (w : ℂ) (hw : w∈ball z r) : HasDerivAt H (l w) w := der w hw
  have hz := mem_ball_self rp (x:=z)
  have sH : AnalyticAt ℂ H z := ((show DifferentiableOn ℂ H (ball z r) from
    fun w hw => (hh w hw).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball) z hz
  have fForm : ∀ᶠ x in 𝓝 a, HasFDerivAt (H ∘ k) (physicalHorizontalForm X x) x := by
    filter_upwards [orientation,transfer,(k.continuousAt ka).eventually (isOpen_ball.mem_nhds hz)] with x o h b
    rw [h.2.1]
    exact ((hh _ b).hasFDerivAt.restrictScalars ℝ).comp x (o.1.differentiableAt (by simp)).hasFDerivAt
  refine ⟨⟨H ∘ k,(sH.restrictScalars (𝕜:=ℝ)).contDiffAt.comp a (orientation.self_of_nhds.1.of_le (by norm_num)),fForm⟩,
    ⟨deriv g z/l z,?_⟩,eqG.self_of_nhds ▸ bounded,?_,?_⟩
  · have dg := ((ag.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp a dk).congr_of_eventuallyEq eqG
    convert dg using 1
    ext v
    rw [atCenter.2.1]
    change (fderiv ℝ k a v*l z)*(deriv g z/l z)=fderiv ℝ k a v*deriv g z
    have nz : l z≠0 := nonzero
    field_simp [nz]
  · filter_upwards [near,eqG] with x nx gx
    rw [euclidean_chart_normal_eq_unitCross,nx]
    exact congrArg (fun h => coordinateToEuclidean (finiteGaussNormal h)) gx.symm
  · intro v
    rw [atCenter.2.2,atCenter.2.1,eqG.self_of_nhds]
    change ‖coordinateToEuclidean (nullRealDerivative (p z) (fderiv ℝ k a v))‖=
      (1+normSq (g z))/2*‖fderiv ℝ k a v*l z‖
    rw [mul_comm (fderiv ℝ k a v) (l z)]
    exact physical_speed_in_finite_gauss_chart hp nonzero _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.minimal_chart_local_horizontal_development

