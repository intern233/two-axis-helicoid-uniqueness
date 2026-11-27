import TwoAxisHelicoid.ResidueFreeDoublePoleChange
import TwoAxisHelicoid.UniformizedEndCoordinate
import TwoAxisHelicoid.ExteriorHeightGaussPoles
import Mathlib.Analysis.Calculus.LogDeriv

namespace TwoAxisHelicoid
open Complex Filter Topology Set
open scoped Topology Manifold ContDiff

/-- Differentiating an exponential Gauss end in a regular marked
coordinate yields a double pole with a holomorphic remainder. -/
theorem exponential_end_log_derivative_in_coordinate {G u F : ℂ → ℂ} {C : ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0=0) (du : deriv u 0 ≠ 0) (hF : AnalyticAt ℂ F 0)
    (hg : G =ᶠ[𝓝[≠] (0:ℂ)] fun z => Complex.exp (C/u z+F (u z))) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), logDeriv G z = -(C/deriv u 0)/z^2+r z := by
  obtain ⟨v,hv,he⟩ := reciprocal_simple_coordinate_expansion hu hu0 du
  let R := fun z => C*v z+F (u z)
  let B := C/deriv u 0
  have ha : AnalyticAt ℂ R 0 := (analyticAt_const.mul hv).add ((show AnalyticAt ℂ F (u 0) by rwa [hu0]).comp hu)
  have norm : G =ᶠ[𝓝[≠] (0:ℂ)] fun z => Complex.exp (B/z+R z) := by
    filter_upwards [hg,he] with z hz hvz
    rw [hz]
    apply congrArg Complex.exp
    rw [div_eq_mul_inv C (u z),hvz.2]
    dsimp [R,B]
    ring
  refine ⟨deriv R,ha.deriv,?_⟩
  filter_upwards [logDeriv_congr_nhdsNE norm,ha.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hR hn
  have nz : z ≠ 0 := hn
  have d : HasDerivAt (fun w : ℂ => B/w) (-B/z^2) z := by
    simpa only [zero_mul,one_mul,mul_one,zero_sub,id_eq] using! (hasDerivAt_const z B).div (hasDerivAt_id z) nz
  have e := (d.add hR.differentiableAt.hasDerivAt).cexp.deriv
  rw [hz,logDeriv_apply]
  change deriv (Complex.exp ∘ fun w => B/w+R w) z / Complex.exp (B/z+R z) = _
  change deriv (fun w => Complex.exp (((fun t : ℂ => B/t)+R) w)) z / _ = _
  rw [e]
  change Complex.exp (B/z+R z)*(-B/z^2+deriv R z)/Complex.exp (B/z+R z) = _
  exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)

/-- The residue-free expansion survives passing from the filled exterior
chart to the covering plane of a biholomorphically marked compact torus.
The coordinate and its nonzero derivative are obtained from the marking. -/
theorem uniformized_actual_gauss_end_residue {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N]
    {L : PeriodPair} (H : N ≃ₜ PeriodTorus L) (p : N) (h0 : H p = 0)
    (hH : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H) (hi : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm)
    (χ : OpenPartialHomeomorph N ℂ) (hχ : χ ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω N)
    (hp : p ∈ χ.source) (hz : χ p=0) (X : N → Fin 3 → ℝ)
    (hr : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ (X ∘ χ.symm) z)
    {C : ℂ} (hC : C ≠ 0) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hg : immersionGaussMap (X ∘ χ.symm) =ᶠ[𝓝[≠] (0:ℂ)] fun z => Complex.exp (C/z+F z)) :
    let Y := X ∘ H.symm ∘ periodTorusProjection L
    ∃ (A : ℂ) (r : ℂ → ℂ), A ≠ 0 ∧ AnalyticAt ℂ r 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), logDeriv (immersionGaussMap Y) z=A/z^2+r z := by
  obtain ⟨u,hu,hu0,hn,he⟩ := marked_torus_end_chart_germ H p h0 hH hi χ hχ hp hz
  let Y := X ∘ H.symm ∘ periodTorusProjection L
  have hT : Tendsto u (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := by
    simpa only [hu0] using hu.differentiableAt.hasDerivAt.tendsto_nhdsNE hn
  have eY : Y =ᶠ[𝓝[≠] (0:ℂ)] (X ∘ χ.symm) ∘ u := by
    filter_upwards [nhdsWithin_le_nhds he] with z hz using congrArg X hz.symm
  have d := (spatial_equal_germ_end_coefficients eY).1
  have gY : immersionGaussMap Y =ᶠ[𝓝[≠] (0:ℂ)] fun z => Complex.exp (C/u z+F (u z)) := by
    filter_upwards [d,hT.eventually hg,hT.eventually hr,hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hu.deriv.continuousAt.eventually_ne hn).filter_mono nhdsWithin_le_nhds] with z hw hg' hr' hau hd
    have h := immersionGaussMap_comp_holomorphic hr' hau.differentiableAt.hasDerivAt hd
    exact (congrArg nullGauss hw).trans (h.trans hg')
  obtain ⟨r,hr,eq⟩ := exponential_end_log_derivative_in_coordinate hu hu0 hn hF gY
  exact ⟨-(C/deriv u 0),r,neg_ne_zero.mpr (div_ne_zero hC hn),hr,eq⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.uniformized_actual_gauss_end_residue
