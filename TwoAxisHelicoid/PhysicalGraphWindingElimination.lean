import TwoAxisHelicoid.CartesianHelicoidRay
import TwoAxisHelicoid.PowerRayRelativePhase

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology ComplexConjugate

/-- In a true height chart, the single-layer physical helicoid fixes the
exponential coefficient and eliminates all integral winding of the
Gauss map. The parameter rays need not lie on the surface's axes. -/
theorem physical_graph_winding_elimination {M : Type*} [TopologicalSpace M]
    {Y : M → Fin 3 → ℝ} (graph : HasHelicoidC1End (coordinateToTube ∘ Y)) (cy : Continuous Y)
    (e : OpenPartialHomeomorph M ℂ) {R : ℝ} (target : e.target={w : ℂ | R<‖w‖})
    (height : ∀ x∈e.source, Y x 2=(e x).re) (m : ℤ) {c : ℂ} (cn : c≠0)
    {B : ℂ → ℂ} (ba : ContinuousAt B 0) (bn : B 0≠0)
    (forms : ∀ᶠ w in cobounded ℂ, HasFDerivAt (Y ∘ e.symm)
      (nullRealDerivative (weierstrassTriple (w^m*exp (c*w)*B w⁻¹) 1)) w) :
    c=I ∧ m=0 := by
  let K := -B 0/(2*c)
  have kn : K≠0 := div_ne_zero (neg_ne_zero.mpr bn) (mul_ne_zero two_ne_zero cn)
  apply helicoid_sector_phase_determines_both_coefficients cn kn m
  intro ζ pos
  let μ := c*ζ
  let b := ζ^m*B 0
  have zn : ζ≠0 := fun h => (by simpa only [h,mul_zero,zero_re] using pos : (0:ℝ)<0).false
  have bpos : b≠0 := mul_ne_zero (zpow_ne_zero _ zn) bn
  let ℓ := fun t : ℝ => (t:ℂ)*ζ
  let U := exponentialPowerRay m μ
  let g := fun t => (ℓ t)^m*exp (c*ℓ t)*B (ℓ t)⁻¹
  let p := e.symm ∘ ℓ
  let W := fun t => spatialGraphProjection 0 1 (Y (p t))
  have far : Tendsto ℓ atTop (cobounded ℂ) := by
    apply tendsto_norm_atTop_iff_cobounded.mp
    apply (tendsto_id.atTop_mul_const (norm_pos_iff.mpr zn)).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    simp [ℓ,abs_of_pos ht]
  have limB := ba.tendsto.comp (tendsto_inv₀_cobounded.comp far)
  have factor : Tendsto (fun t => g t/U t) atTop (𝓝 b) := by
    apply (limB.const_mul (ζ^m)).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    dsimp [g,ℓ,U,exponentialPowerRay,μ]
    rw [mul_zpow,ofReal_zpow,show c*((t:ℂ)*ζ)=c*ζ*t by ring]
    field_simp [zpow_ne_zero m (ofReal_ne_zero.mpr ht.ne'),exp_ne_zero]
  have derivative : ∀ᶠ t in atTop, HasDerivAt W ((conj (ζ/g t)-ζ*g t)/2) t := by
    filter_upwards [far.eventually forms] with t h
    have line : HasDerivAt ℓ ζ t := by simpa using! (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const ζ
    have d := (spatialGraphProjection 0 1).hasFDerivAt.comp_hasDerivAt t (h.comp_hasDerivAt t line)
    exact (weierstrass_horizontal_velocity (g t) ζ) ▸ d
  have ratio := horizontal_position_on_growing_ray m pos bpos factor derivative
  let q := K*ζ^m
  have eq : (-(ζ*b)/2)/μ=q := by dsimp [μ,b,q,K]; field_simp
  rw [eq] at ratio
  have qn : q≠0 := mul_ne_zero kn (zpow_ne_zero _ zn)
  have grows : Tendsto (fun t => ‖W t‖) atTop atTop := by
    apply ((exponentialPowerRay_escape m pos).atTop_mul_pos (norm_pos_iff.mpr qn) ratio.norm).congr'
    filter_upwards [(exponentialPowerRay_escape m pos).eventually_gt_atTop 0] with t ht
    change ‖U t‖*‖W t/U t‖=‖W t‖
    rw [norm_div]
    calc
      _=‖W t‖*‖U t‖/‖U t‖ := by ring
      _=_ := mul_div_cancel_right₀ _ ht.ne' 
  have phase := normal_graph_horizontal_ray_phase graph cy p grows
  have actualHeight : ∀ᶠ t in atTop, Y (p t) 2=ζ.re*t := by
    filter_upwards [(tendsto_norm_atTop_iff_cobounded.mpr far).eventually_gt_atTop R] with t ht
    have tar : ℓ t∈e.target := target ▸ ht
    change Y (e.symm (ℓ t)) 2=ζ.re*t
    rw [height _ (e.map_target tar),e.right_inv tar]
    simp [ℓ,Complex.mul_re,mul_comm]
  apply relative_height_phase_forces_ray_limit m μ ζ.re qn ratio
  apply phase.congr'
  filter_upwards [actualHeight] with t ht
  change complexLinePhase (exp (((-(Y (p t) 2):ℝ):ℂ)*I)*W t)=_
  rw [ht]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_graph_winding_elimination
