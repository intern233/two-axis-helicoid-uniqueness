import TwoAxisHelicoid.CenterRulingGaussAlgebra
import TwoAxisHelicoid.HelicoidGraphSpatialGrowth

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- At zero base radius both tangent vectors of a normal graph are
realized by the isothermal immersion, including the radial contribution
of its angular derivative. -/
theorem graph_center_gauss_direction {X : ℂ → Fin 3 → ℝ} {p : Fin 3 → ℂ} {z : ℂ}
    {u : ℝ × ℝ → ℝ} {θ : ℝ} (dx : HasFDerivAt X (nullRealDerivative p) z)
    (null : ComplexNull p) (height : p 2≠0) (imm : Function.Injective (fderiv ℝ X z))
    (tube : coordinateToTube (X z)∈helicoidTubeEquiv.target)
    (center : helicoidProjectedComplexParameter (coordinateToTube (X z))=(θ:ℂ)*I)
    (du : DifferentiableAt ℝ u (0,θ)) (small : |u (0,θ)|≤1/2) (slope : helicoidGraphGradientNorm u (0,θ)≤1/2)
    (localEq : coordinateToTube ∘ X =ᶠ[𝓝 z] (helicoidGraphMap u ∘ helicoidConformalBase) ∘
      (helicoidProjectedComplexParameter ∘ (coordinateToTube ∘ X))) :
    (∀ a : ℝ, nullGauss p≠(a:ℂ)*exp ((θ:ℂ)*I)) ∧ 1/10≤‖nullGauss p‖ ∧ ‖nullGauss p‖≤10 := by
  let Y := coordinateToTube ∘ X
  let P := helicoidProjectedComplexParameter ∘ Y
  let G := helicoidGraphMap u ∘ helicoidConformalBase
  have cp : P z=(θ:ℂ)*I := center
  have base : helicoidConformalBase (P z)=(0,θ) := by simp [cp,helicoidConformalBase]
  have y' := coordinateToTube.hasFDerivAt.comp z dx
  have dp := (helicoidProjectedComplexParameter_differentiable tube).comp z y'.differentiableAt
  have dg := (helicoidGraphMap_differentiableAt (base.symm ▸ du)).comp (P z) (helicoidConformalBase_hasFDerivAt _).differentiableAt
  have chain : coordinateToTube.comp (nullRealDerivative p)=(fderiv ℝ G (P z)).comp (fderiv ℝ P z) :=
    y'.fderiv.symm.trans (localEq.fderiv_eq.trans (fderiv_comp z dg dp))
  have inj : Function.Injective (fderiv ℝ P z) := by
    intro a b h
    apply imm
    rw [dx.fderiv]
    apply coordinateTubeHomeomorph.injective
    change (coordinateToTube.comp (nullRealDerivative p)) a=(coordinateToTube.comp (nullRealDerivative p)) b
    rw [chain,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,h]
  let g := nullGauss p
  let Q : ℝ × ℝ := (0,θ)
  let R := fderiv ℝ u Q (1,0)
  let T := fderiv ℝ u Q (0,1)
  have tangent (v : ℂ) :
      let a := fderiv ℝ helicoidConformalBase (P z) v
      let V := tubeCartesian (fderiv ℝ (helicoidGraphMap u) Q a)
      (2*g.re)*V 0+(2*g.im)*V 1+(‖g‖^2-1)*V 2=0 := by
    obtain ⟨w,hw⟩ := (LinearMap.injective_iff_surjective.mp (show Function.Injective (fderiv ℝ P z).toLinearMap from inj)) v
    have vec := congrArg (fun D : ℂ →L[ℝ] HelicoidTubeCoordinates => D w) chain
    change coordinateToTube (nullRealDerivative p w)=fderiv ℝ G (P z) (fderiv ℝ P z w) at vec
    rw [show fderiv ℝ P z w=v from hw] at vec
    have diff := fderiv_comp (P z) (helicoidGraphMap_differentiableAt (base.symm ▸ du)) (helicoidConformalBase_hasFDerivAt _).differentiableAt
    change fderiv ℝ G (P z)=_ at diff
    rw [diff,ContinuousLinearMap.comp_apply,base] at vec
    have eq := congrArg tubeCartesian vec
    rw [tubeCartesian_coordinateToTube] at eq
    dsimp only
    rw [← eq]
    exact null_gauss_normal_annihilates null height w
  have rad := tangent 1
  have tan := tangent I
  have fc (v : ℂ) : fderiv ℝ helicoidConformalBase (P z) v=(v.re,v.im) := by
    rw [(helicoidConformalBase_hasFDerivAt _).fderiv,cp]
    simp
  simp only [fc,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im] at rad tan
  rw [helicoidGraphMap_fderiv du] at rad tan
  simp [helicoidTubeR,helicoidTubeTheta,standardHelicoidR,standardHelicoidTheta,standardHelicoidNormal,helicoidQ] at rad tan
  have grad : Real.sqrt (R^2+T^2)≤1/2 := by simpa [R,T,Q,helicoidGraphGradientNorm,helicoidQ] using slope
  have squares := Real.sq_sqrt (show 0≤R^2+T^2 by positivity)
  have radius : |R|≤1 := abs_le.mpr ⟨by nlinarith [sq_nonneg T,Real.sqrt_nonneg (R^2+T^2)],by nlinarith [sq_nonneg T,Real.sqrt_nonneg (R^2+T^2)]⟩
  have angular : |T|≤1 := abs_le.mpr ⟨by nlinarith [sq_nonneg R,Real.sqrt_nonneg (R^2+T^2)],by nlinarith [sq_nonneg R,Real.sqrt_nonneg (R^2+T^2)]⟩
  apply center_ruling_gauss_phase_and_modulus (nullGauss_ne_zero_of_height null height) small radius angular
  · dsimp only [R,Q]; linear_combination rad
  · dsimp only [T,Q]; linear_combination tan

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_center_gauss_direction
