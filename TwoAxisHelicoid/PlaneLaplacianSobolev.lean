import TwoAxisHelicoid.PlaneSobolevRepresentative

namespace TwoAxisHelicoid
open MeasureTheory FourierTransform TemperedDistribution Real
open scoped SchwartzMap Laplacian BoundedContinuousFunction

/-- In the Fourier normalization used here the order-two Bessel operator is
the identity minus the Laplacian divided by the square of two pi. -/
theorem plane_order_two_bessel (f : 𝓢'(ℂ, ℂ)) :
    besselPotential ℂ ℂ 2 f = f + ((-(2 * π) ^ 2 : ℝ)⁻¹) • (Δ f) := by
  let g := fun x : ℂ => Complex.ofReal (‖x‖^2)
  let one := fun _ : ℂ => (1:ℂ)
  have split : (fun x : ℂ => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((2:ℝ)/2))) = one + g := by
    ext x
    simp [one,g]
  have sg : g.HasTemperateGrowth := by dsimp only [g]; fun_prop
  have so : one.HasTemperateGrowth := by dsimp only [one]; fun_prop
  have nonzero : (-(2 * π)^2 : ℝ) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  rw [laplacian_eq_fourierMultiplierCLM, inv_smul_smul₀ nonzero, besselPotential, split,
    fourierMultiplierCLM_apply, smulLeftCLM_add so sg, add_apply,
    fourierInv_add]
  simp [one, g, fourierMultiplierCLM_apply]

/-- An L² representative for the weak Laplacian already gives a bounded
continuous representative of the original field on the full plane. -/
theorem plane_continuous_of_laplacian_L2 (u v : Lp ℂ 2 (volume : Measure ℂ))
    (h : Δ (u : 𝓢'(ℂ, ℂ)) = (v : 𝓢'(ℂ, ℂ))) :
    ∃ f : ℂ →ᵇ ℂ, ⇑u =ᵐ[volume] ⇑f := by
  apply plane_sobolev_continuous_representative u (s:=2) (by norm_num)
  let c : ℝ := (-(2 * π)^2)⁻¹
  use u + c • v
  change besselPotential ℂ ℂ 2 _ = Lp.toTemperedDistributionCLM ℂ volume 2 (u+c • v)
  rw [plane_order_two_bessel,h,map_add,ContinuousLinearMap.map_smul_of_tower]
  rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_continuous_of_laplacian_L2

