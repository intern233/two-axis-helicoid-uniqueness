import TwoAxisHelicoid.VariableHeightAreaHessian
import TwoAxisHelicoid.PositiveMetricCompactArea
import TwoAxisHelicoid.ActualAreaVariationIndex

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Function
open scoped Topology ContDiff

/-- In an arbitrary regular conformal Weierstrass chart the second
derivative of the compact area integral is the quadratic form of the
Gauss map. The test is supported in the chosen compact patch. -/
theorem compact_variable_height_area_second_derivative {X : ℂ → Fin 3 → ℝ} {W h : ℂ → ℂ}
    {v : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K) (support : tsupport v ⊆ K)
    (hv : ContDiff ℝ ∞ v) (hn : ∀ p ∈ K, h (planeComplex p)≠0)
    (hc : ContinuousOn (h ∘ planeComplex) K)
    (hX : ∀ p ∈ K, HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (W (planeComplex p))) (h (planeComplex p)))) (planeComplex p))
    (hW : ∀ p ∈ K, AnalyticAt ℂ W (planeComplex p)) :
    HasDerivAt (deriv (fun s => ∫ p in K, coordinateVariationDensity X W v s p))
      (planarQuadraticEnergy (gaussNormalDirichletDensity W) v) 0 := by
  let D := fun p => deriv W (planeComplex p)
  let k := h ∘ planeComplex
  let g := fun p => ‖k p‖^2*(Real.cosh (W (planeComplex p)).re)^2
  let b := fun p => (k p).re*(-(D p).re)+(k p).im*(D p).im
  let c := fun p => -(k p).im*(-(D p).re)+(k p).re*(D p).im
  let dx := fun p => fderiv ℝ v p (1,0)
  let dy := fun p => fderiv ℝ v p (0,1)
  let A := fun p => g p*((dx p)^2+(dy p)^2)-2*(v p)^2*((b p)^2+(c p)^2)
  let B := fun p => 2*v p*b p*((dx p)^2-(dy p)^2)+4*v p*c p*dx p*dy p
  let C := fun p => (v p)^4*((b p)^2+(c p)^2)^2/(g p)^2+
      (v p)^2*((b p)^2+(c p)^2)/g p*((dx p)^2+(dy p)^2)
  have plc : Continuous planeComplex := by unfold planeComplex; fun_prop
  have wc : ContinuousOn (fun p => W (planeComplex p)) K :=
    fun p hp => ((hW p hp).continuousAt.comp plc.continuousAt).continuousWithinAt
  have dc : ContinuousOn D K :=
    fun p hp => ((hW p hp).deriv.continuousAt.comp plc.continuousAt).continuousWithinAt
  have kc : ContinuousOn k K := hc
  have gc : ContinuousOn g K := (kc.norm.pow 2).mul
    ((Real.continuous_cosh.comp_continuousOn (Complex.continuous_re.comp_continuousOn wc)).pow 2)
  have bc : ContinuousOn b K := by dsimp only [b]; fun_prop
  have cc : ContinuousOn c K := by dsimp only [c]; fun_prop
  have vc : ContinuousOn v K := hv.continuous.continuousOn
  have dxc : ContinuousOn dx K := ((hv.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  have dyc : ContinuousOn dy K := ((hv.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  have gp (p) (hp : p∈K) : 0<g p := mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (hn p hp))) (sq_pos_of_pos (Real.cosh_pos _))
  have ac : ContinuousOn A K := by dsimp only [A]; fun_prop
  have bc' : ContinuousOn B K := by dsimp only [B]; fun_prop
  have cc' : ContinuousOn C K := by
    have squares := (bc.pow 2).add (cc.pow 2)
    have grad := (dxc.pow 2).add (dyc.pow 2)
    have l := ((vc.pow 4).mul (squares.pow 2)).div (gc.pow 2) (fun x hx => pow_ne_zero _ (gp x hx).ne')
    have r := ((vc.pow 2).mul squares).div gc (fun x hx => (gp x hx).ne')
    exact l.add (r.mul grad)
  have form (p) (hp : p∈K) : (fun s => coordinateVariationDensity X W v s p)=
      fun s => Real.sqrt (areaQuartic (g p) (A p) (B p) (C p) s) := by
    have e := variable_height_normal_variation_area (hn p hp) (hX p hp) (hW p hp).differentiableAt.hasDerivAt
      ((hv.differentiable (by simp)) p)
    change (fun s => coordinateVariationDensity X W v s p)=normalVariationArea (g p) (b p) (c p) (v p) (dx p) (dy p) at e
    rw [normalVariationArea_eq_quartic (gp p hp).ne'] at e
    exact e
  have area : (fun s => ∫ p in K, coordinateVariationDensity X W v s p)=
      fun s => ∫ p in K, Real.sqrt (areaQuartic (g p) (A p) (B p) (C p) s) := by
    funext s
    exact setIntegral_congr_fun hK.measurableSet fun p hp => congrFun (form p hp) s
  have density (p) (hp : p∈K) : (A p)/(g p)=
      (dx p)^2+(dy p)^2-gaussNormalDirichletDensity W p*(v p)^2 := by
    have he := variable_height_coordinate_hessian (hn p hp) (hX p hp) (hW p hp).differentiableAt.hasDerivAt
      ((hv.differentiable (by simp)) p)
    change deriv (deriv (fun s => coordinateVariationDensity X W v s p)) 0=_ at he
    rw [form p hp,(areaQuartic_sqrt_second_derivative (gp p hp) _ _ _).deriv] at he
    exact he
  have energy : (∫ p in K,A p/g p)=planarQuadraticEnergy (gaussNormalDirichletDensity W) v := by
    rw [← integral_indicator hK.measurableSet]
    unfold planarQuadraticEnergy
    congr 1
    funext p
    by_cases hp : p∈K
    · rw [indicator_of_mem hp]
      exact density p hp
    · rw [indicator_of_notMem hp]
      have off := notMem_tsupport_iff_eventuallyEq.mp (fun hz => hp (support hz))
      have zero : v p=0 := off.self_of_nhds
      have df : fderiv ℝ v p=0 := by simpa using off.fderiv_eq
      simp [zero,df]
  rw [area,← energy]
  exact positive_compact_quartic_area_second_derivative hK gc ac bc' cc' gp

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_variable_height_area_second_derivative
