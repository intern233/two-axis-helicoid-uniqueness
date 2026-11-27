import TwoAxisHelicoid.EllipticOriginLaurentCoefficients
import TwoAxisHelicoid.UnreducedWeierstrassHeat
import TwoAxisHelicoid.WeierstrassParameterOriginLimit

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

private theorem cancel_unreduced_heat_poles (z u v w e g d : ℂ) (hz : z ≠ 0) :
    2*(z⁻¹^2+z^2*u)^2-2*e*(z⁻¹^2+z^2*u)-e^2-g/4+
      (z⁻¹-e*z+z^3*v)*(-2*z⁻¹^3+z*w)-d =
      4*u-2*v+w-e^2-g/4-d+z^2*(-2*e*u-e*w+z^2*(2*u^2+v*w)) := by
  field_simp [hz]
  ring

/-- The right side of the intermediate heat equation before the derivative of η
is evaluated. -/
noncomputable def unreducedHeatRHS (t : ℝ) (ht : 0 < t) (z : ℂ) : ℂ :=
  let L := rhombicPeriodPair t ht
  2*(L.weierstrassP z)^2-2*thetaEtaExpression t*L.weierstrassP z-
    (thetaEtaExpression t)^2-L.g₂/4+
    (thetaZeta t z-thetaEtaExpression t*z)*L.derivWeierstrassP z-
    (Real.pi:ℂ)*deriv thetaEtaExpression t

/-- The Laurent constant and an analytic quadratic remainder for the full
right side of Appendix A.1, line 1929. -/
theorem unreduced_heat_rhs_origin_factor {t : ℝ} (ht : 0 < t) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), unreducedHeatRHS t ht z =
        (rhombicPeriodPair t ht).g₂/12-(thetaEtaExpression t)^2-
          (Real.pi:ℂ)*deriv thetaEtaExpression t+z^2*R z := by
  let L := rhombicPeriodPair t ht
  let e := thetaEtaExpression t
  let d := (Real.pi:ℂ)*deriv thetaEtaExpression t
  obtain ⟨A,B,ha,hb,hp,hzeta⟩ := elliptic_origin_laurent_factors ht
  let U := fun z : ℂ => L.g₂/20+z^2*A z
  let V := fun z : ℂ => -(L.g₂/60)+z^2*B z
  let W := fun z : ℂ => L.g₂/10+z^2*(4*A z+z*deriv A z)
  let R := fun z : ℂ => 8*A z-2*B z+z*deriv A z-2*e*U z-e*W z+
    z^2*(2*(U z)^2+V z*W z)
  have hda : AnalyticAt ℂ (deriv A) 0 := ha.deriv
  have hr : AnalyticAt ℂ R 0 := by
    dsimp only [R,U,V,W]
    fun_prop (disch := assumption)
  refine ⟨R,hr,?_⟩
  filter_upwards [hp.eventually_nhds.filter_mono nhdsWithin_le_nhds, hzeta,
    ha.eventually_analyticAt.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with z localP zeta localA nz
  have nz' : z ≠ 0 := nz
  have germ : L.weierstrassP =ᶠ[𝓝 z] (fun w : ℂ => w⁻¹^2+(L.g₂/20)*w^2+w^4*A w) :=
    localP
  have p : L.weierstrassP z = z⁻¹^2+z^2*U z := by
    rw [localP.self_of_nhds]
    dsimp only [U]
    ring
  have v : thetaZeta t z-e*z = z⁻¹-e*z+z^3*V z := by
    rw [zeta]
    dsimp only [V]
    ring
  have polynomialJet : HasDerivAt
      (fun w : ℂ => w⁻¹^2+(L.g₂/20)*w^2+w^4*A w) _ z :=
    (((hasDerivAt_inv nz').fun_pow 2).fun_add ((hasDerivAt_pow 2 z).const_mul (L.g₂/20))).fun_add
      ((hasDerivAt_pow 4 z).fun_mul localA.differentiableAt.hasDerivAt)
  have dp : L.derivWeierstrassP z = -2*z⁻¹^3+z*W z := by
    rw [← L.deriv_weierstrassP,germ.deriv_eq,polynomialJet.deriv]
    dsimp only [W,id_eq]
    norm_num
    field_simp [nz']
    ring
  change 2*(L.weierstrassP z)^2-2*e*L.weierstrassP z-e^2-L.g₂/4+
    (thetaZeta t z-e*z)*L.derivWeierstrassP z-d = L.g₂/12-e^2-d+z^2*R z
  rw [p,v,dp,cancel_unreduced_heat_poles z (U z) (V z) (W z) e L.g₂ d nz']
  dsimp only [R,U,V,W]
  ring

theorem unreduced_heat_rhs_tendsto_origin {t : ℝ} (ht : 0 < t) :
    Tendsto (unreducedHeatRHS t ht) (𝓝[≠] (0:ℂ))
      (𝓝 ((rhombicPeriodPair t ht).g₂/12-(thetaEtaExpression t)^2-
        (Real.pi:ℂ)*deriv thetaEtaExpression t)) := by
  obtain ⟨R,hr,same⟩ := unreduced_heat_rhs_origin_factor ht
  let c := (rhombicPeriodPair t ht).g₂/12-(thetaEtaExpression t)^2-
    (Real.pi:ℂ)*deriv thetaEtaExpression t
  have cont : ContinuousAt (fun z : ℂ => c+z^2*R z) 0 :=
    continuousAt_const.add ((continuousAt_id.pow 2).mul hr.continuousAt)
  apply (tendsto_congr' same).mpr
  simpa only [zero_pow (by decide : 2 ≠ 0),zero_mul,add_zero] using
    (cont.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ))))

/-- The η heat equation recovered by comparing the two limits at the pole,
along the specific proof route in Appendix A.1. -/
theorem thetaEtaExpression_hasDerivAt_via_origin_constants {t : ℝ} (ht : 0 < t) :
    HasDerivAt thetaEtaExpression
      (((rhombicPeriodPair t ht).g₂/12-(thetaEtaExpression t)^2)/(Real.pi:ℂ)) t := by
  have leftlim : Tendsto
      (fun z : ℂ => (Real.pi:ℂ)*deriv (fun s : ℝ => actualWeierstrassPFamily s z) t)
      (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    simpa only [mul_zero] using
      (actualWeierstrassPFamily_parameter_deriv_tendsto_zero ht).const_mul (Real.pi:ℂ)
  have same : (fun z : ℂ => (Real.pi:ℂ)*deriv (fun s : ℝ => actualWeierstrassPFamily s z) t)
      =ᶠ[𝓝[≠] (0:ℂ)] unreducedHeatRHS t ht := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      ((rhombicPeriodPair t ht).compl_lattice_sdiff_singleton_mem_nhds 0),self_mem_nhdsWithin]
      with z isolated nz
    exact actualWeierstrassPFamily_unreduced_heat ht (fun mem => isolated ⟨mem,nz⟩)
  have constant := tendsto_nhds_unique_of_eventuallyEq leftlim (unreduced_heat_rhs_tendsto_origin ht) same
  have value : deriv thetaEtaExpression t =
      ((rhombicPeriodPair t ht).g₂/12-(thetaEtaExpression t)^2)/(Real.pi:ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).mpr
    linear_combination constant
  rw [← value]
  exact (thetaEtaExpression_analyticAt ht).differentiableAt.hasDerivAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unreduced_heat_rhs_origin_factor
#print axioms TwoAxisHelicoid.unreduced_heat_rhs_tendsto_origin
#print axioms TwoAxisHelicoid.thetaEtaExpression_hasDerivAt_via_origin_constants
