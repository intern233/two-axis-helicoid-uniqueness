import TwoAxisHelicoid.PlaneLaplacianSobolev

namespace TwoAxisHelicoid
open MeasureTheory FourierTransform TemperedDistribution Real
open scoped SchwartzMap BoundedContinuousFunction ContDiff

/-- A fixed bounded linear operator recovers the entire continuous field
from its order-two Bessel potential, including its point values. -/
theorem exists_plane_bessel_evaluation :
    ∃ J : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] (ℂ →ᵇ ℂ),
      ∀ (u v : Lp ℂ 2 (volume : Measure ℂ)),
        besselPotential ℂ ℂ 2 (u : 𝓢'(ℂ, ℂ)) = (v : 𝓢'(ℂ, ℂ)) →
        ⇑u =ᵐ[volume] ⇑(J v) := by
  let weight := fun x : ℂ => (1+‖x‖^2)⁻¹
  have pos (x : ℂ) : 0 < 1+‖x‖^2 := by positivity
  have wm : MemLp weight 2 volume := by
    apply (memLp_two_iff_integrable_sq (by dsimp only [weight]; fun_prop)).mpr
    have h := integrable_rpow_neg_one_add_norm_sq (μ:=volume) (E:=ℂ) (r:=4)
      (by rw [Complex.finrank_real_complex]; norm_num)
    convert h using 1
    funext z
    dsimp only [weight]
    norm_num [Real.rpow_neg (pos z).le]
  let g := fun x : ℂ => Complex.ofReal (weight x)
  have gm : MemLp g 2 volume := wm.ofReal
  have e : g = (fun x : ℂ => Complex.ofReal ((1+‖x‖^2)^((-2:ℝ)/2))) := by
    funext x
    rw [show (-2:ℝ)/2=-1 by norm_num, Real.rpow_neg_one]
  have sg : g.HasTemperateGrowth := by
    rw [e]
    fun_prop
  let B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.lsmul ℂ ℂ
  let K := (B.holderL (volume:Measure ℂ) 2 2 1) (gm.toLp g)
  let J := (Lp.fourierTransformInvCLM ℂ ℂ).comp (K.comp (Lp.fourierTransformₗᵢ ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨J,?_⟩
  intro u v h
  let b := K (𝓕 v)
  have mul : b = (gm.toLp g) • (𝓕 v) := by
    apply Lp.ext
    filter_upwards [B.coeFn_holder (r:=1) (gm.toLp g) (𝓕 v), Lp.coeFn_lpSMul (r:=1) (gm.toLp g) (𝓕 v)] with z a c
    exact a.trans c.symm
  have inv := (besselPotential_neg_apply_eq_iff 2 (v : 𝓢'(ℂ, ℂ)) (u : 𝓢'(ℂ, ℂ))).mpr h
  have freq : 𝓕 (u : 𝓢'(ℂ, ℂ)) = (b : 𝓢'(ℂ, ℂ)) := by
    rw [← inv, fourier_besselPotential_eq_smulLeftCLM_fourier_apply,mul,
      Lp.toTemperedDistribution_smul_eq sg gm, Lp.fourier_toTemperedDistribution_eq]
    rw [← e]
  have identity : (u : 𝓢'(ℂ, ℂ))=𝓕⁻ (b : 𝓢'(ℂ, ℂ)) := by rw [←freq,fourierInv_fourier_eq]
  change ⇑u =ᵐ[volume] ⇑(Lp.fourierTransformInv b)
  apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp u).locallyIntegrable (by norm_num))
    (Lp.fourierTransformInv b).continuous.locallyIntegrable
  intro ψ smooth support
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := support.comp_left rfl
  let φ := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp smooth)
  have eq := congrArg (fun U : 𝓢'(ℂ, ℂ) => U φ) identity
  change (Lp.toTemperedDistribution u) φ = (Lp.toTemperedDistribution b) (𝓕⁻ φ) at eq
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply, plane_inverse_fourier_test_pairing _ (L1.integrable_coeFn b)] at eq
  simpa [φ] using eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_plane_bessel_evaluation

