import TwoAxisHelicoid.SimplePoleHeightChart
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

/-- In a univalent local coordinate a meromorphic pole of degree n is
exactly the inverse n-th power. A local logarithm is applied only to a
unit normalized to one, so this also works for a negative real leading
coefficient. -/
theorem meromorphic_pole_power_coordinate {H : ℂ → ℂ} (mer : MeromorphicAt H 0)
    {n : ℕ} (hn : 0<n) (order : meromorphicOrderAt H 0 = ((-(n:ℤ):ℤ):WithTop ℤ)) :
    ∃ f k : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ k 0 ∧ f 0=0 ∧ k 0=0 ∧
      (∀ᶠ w in 𝓝 (0:ℂ), f (k w)=w) ∧ (∀ᶠ z in 𝓝 (0:ℂ), k (f z)=z) ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), H z=((f z)^n)⁻¹ := by
  obtain ⟨u,an,unit,germ⟩ := (meromorphicOrderAt_eq_int_iff mer).mp order
  let v := fun z => exp (-(log (u z/u 0)+log (u 0))/(n:ℂ))
  have atOne : u 0/u 0∈slitPlane := by rw [div_self unit]; exact one_mem_slitPlane
  have av : AnalyticAt ℂ v 0 := analyticAt_cexp.comp
    ((((an.div analyticAt_const unit).clog atOne).add analyticAt_const ).neg.div_const)
  have nonzero (z : ℂ) : v z≠0 := exp_ne_zero _
  have nth {z : ℂ} (hu : u z≠0) : v z^n=(u z)⁻¹ := by
    have hnc : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
    change exp (-(log (u z/u 0)+log (u 0))/(n:ℂ))^n=_
    rw [← Complex.exp_nat_mul,show (n:ℂ)*(-(log (u z/u 0)+log (u 0))/(n:ℂ))=
      -(log (u z/u 0)+log (u 0)) by field_simp,Complex.exp_neg,Complex.exp_add,
      Complex.exp_log (div_ne_zero hu unit),Complex.exp_log unit,div_mul_cancel₀ _ unit]
  let f := fun z : ℂ => z*v z
  have af : AnalyticAt ℂ f 0 := analyticAt_id.mul av
  have df : HasDerivAt f (v 0) 0 := by
    simpa only [id_eq,one_mul,zero_mul,add_zero] using! (hasDerivAt_id (0:ℂ)).mul av.differentiableAt.hasDerivAt
  have f0 : f 0=0 := zero_mul _
  have dn : deriv f 0≠0 := df.deriv ▸ nonzero 0
  let k := af.hasStrictDerivAt.localInverse _ _ _ dn
  have ak : AnalyticAt ℂ k 0 := by simpa only [f0] using af.analyticAt_localInverse dn
  have left : ∀ᶠ z in 𝓝 (0:ℂ), k (f z)=z := af.hasStrictDerivAt.eventually_left_inverse dn
  have right : ∀ᶠ z in 𝓝 (0:ℂ), f (k z)=z := by simpa only [f0] using af.hasStrictDerivAt.eventually_right_inverse dn
  refine ⟨f,k,af,ak,f0,(by simpa only [f0] using left.self_of_nhds),right,left,?_⟩
  filter_upwards [germ,(an.continuousAt.eventually_ne unit).filter_mono nhdsWithin_le_nhds] with z eq hu
  change H z=((z*v z)^n)⁻¹
  rw [eq,sub_zero,zpow_neg,zpow_natCast,smul_eq_mul,mul_pow,nth hu,mul_inv,inv_inv]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.meromorphic_pole_power_coordinate
