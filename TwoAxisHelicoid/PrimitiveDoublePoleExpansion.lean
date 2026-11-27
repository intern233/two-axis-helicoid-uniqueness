import TwoAxisHelicoid.PuncturedDiskPolygon
import TwoAxisHelicoid.StripPrimitives

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- A primitive of a differential with a residue-free double pole has a
simple pole with the opposite leading coefficient. -/
theorem primitive_of_double_pole_expansion {F g : ℂ → ℂ} {A : ℂ}
    (hg : AnalyticAt ℂ g 0)
    (hder : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → HasDerivAt F (A/z^2+g z) z) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → F z = (-A)/z+G z := by
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ g z := (isOpen_analyticAt ℂ g).mem_nhds hg
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hder.and hnear)
  let B := ball (0 : ℂ) r
  let D := B \ {0}
  have hD : IsOpen D := isOpen_ball.sdiff (isClosed_singleton (X := ℂ))
  have hc : IsPreconnected D := complex_ball_diff_finite_isPreconnected 0 hr (finite_singleton 0)
  let H (z : ℂ) := wedgeIntegral 0 z g
  have hd : DifferentiableOn ℂ g B := fun z hz => (hsub hz).2.differentiableAt.differentiableWithinAt
  have hH (z : ℂ) (hz : z ∈ B) : HasDerivAt H (g z) z :=
    hd.isConservativeOn.hasDerivAt_wedgeIntegral hd.continuousOn hz
  have hR (z : ℂ) (hz : z ∈ D) :
      HasDerivAt (fun w : ℂ => F w-((-A)/w+H w)) 0 z := by
    have hn : z ≠ 0 := hz.2
    have hneg : HasDerivAt (fun w : ℂ => (-A)/w) (A/z^2) z := by
      simpa only [zero_mul,mul_one,zero_sub,neg_neg,id_eq,Pi.div_def] using!
        (hasDerivAt_const z (-A)).div (hasDerivAt_id z) hn
    simpa only [sub_self] using! ((hsub hz.1).1 hn).sub (hneg.add (hH z hz.1))
  obtain ⟨C,hC⟩ := hD.exists_is_const_of_deriv_eq_zero hc
    (fun z hz => (hR z hz).differentiableAt.differentiableWithinAt) (fun z hz => (hR z hz).deriv)
  have hHa : AnalyticAt ℂ H 0 :=
    (show DifferentiableOn ℂ H B from fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
      ).analyticOnNhd isOpen_ball 0 (mem_ball_self hr)
  refine ⟨fun z => H z+C,hHa.add analyticAt_const,?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz hn
  have h := hC z ⟨hz,hn⟩
  change F z-((-A)/z+H z) = C at h
  linear_combination h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.primitive_of_double_pole_expansion
