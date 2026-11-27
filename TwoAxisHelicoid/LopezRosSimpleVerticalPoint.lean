import TwoAxisHelicoid.AnalyticPrimitiveLeadingTerm
import TwoAxisHelicoid.LopezRosRescaledPrimitive

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ComplexConjugate

/-- Large positive López–Ros multipliers produce a double point in every
neighborhood of a simple vertical point. The hypotheses are on holomorphic
primitives of the three characteristic forms, including their null identity.
No regularity of a limiting family is assumed. -/
theorem lopez_ros_large_multiplier_at_simple_vertical_point
    (A B C : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hC : AnalyticAt ℂ C 0)
    (hnull : ∀ᶠ z : ℂ in 𝓝 0, deriv A z*deriv B z+(deriv C z)^2 = 0)
    (hminus : deriv B 0 ≠ 0) (hheight : deriv C 0 = 0) (hsimple : deriv (deriv C) 0 ≠ 0)
    {U : Set ℂ} (hU : U ∈ 𝓝 0) :
    ∀ᶠ k : ℝ in atTop, ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧
      lopezRosPrimitivePosition A B C k x = lopezRosPrimitivePosition A B C k y := by
  obtain ⟨d,hd,hD,h₀⟩ := analytic_primitive_leading_factor (deriv C) (deriv (deriv C)) 0
    hC.deriv hC.deriv.deriv (by simp)
  have hD' (z : ℂ) : deriv C z = z*d z := by simpa only [hheight,zero_add,pow_one] using hD z
  have hd₀ : d 0 ≠ 0 := by simpa using h₀.trans_ne hsimple
  let a' := fun z : ℂ => -(d z)^2/deriv B z
  have ha' : AnalyticAt ℂ a' 0 := (hd.pow 2).neg.div hB.deriv hminus
  have hDA : deriv A =ᶠ[𝓝 0] fun z : ℂ => z^2*a' z := by
    filter_upwards [hnull,hB.deriv.continuousAt.eventually_ne hminus] with z hz hn
    dsimp only [a']
    rw [hD' z] at hz
    field_simp [hn]
    linear_combination hz
  obtain ⟨a,ha,ea,va⟩ := analytic_primitive_leading_factor A a' 2 hA ha' hDA
  obtain ⟨b,hb,eb,vb⟩ := analytic_primitive_leading_factor B (deriv B) 0 hB hB.deriv (by simp)
  obtain ⟨c,hc,ec,vc⟩ := analytic_primitive_leading_factor C d 1 hC hd (by
    filter_upwards with z using by simpa only [pow_one] using hD' z)
  have hb₀ : b 0 = deriv B 0 := by simpa using vb
  have hc₀ : 2*c 0 = d 0 := by norm_num at vc; exact vc
  have ha₀ : 3*a 0 = -(d 0)^2/b 0 := by
    rw [hb₀]
    change ((2:ℂ)+1)*a 0 = -(d 0)^2/deriv B 0 at va
    norm_num at va
    exact va
  have bne : b 0 ≠ 0 := hb₀.trans_ne hminus
  have cne : c 0 ≠ 0 := by intro h; apply hd₀; rw [← hc₀,h,mul_zero]
  apply lopez_ros_large_multiplier_of_factored_primitives A B C a b c ha hb hc bne cne _ ea _ ec hU
  · rw [ha₀,div_mul_cancel₀ _ bne,← hc₀]
    ring
  · intro z
    simpa using eb z

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lopez_ros_large_multiplier_at_simple_vertical_point
