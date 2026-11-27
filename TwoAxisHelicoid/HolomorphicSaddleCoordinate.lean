import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology

/-- A simple critical point of a complex analytic function admits a
local holomorphic coordinate in which its increment is exactly a square. -/
theorem holomorphic_simple_critical_coordinate {F : ℂ → ℂ} {z : ℂ} (ha : AnalyticAt ℂ F z)
    (first : deriv F z=0) (second : deriv (deriv F) z≠0) :
    ∃ φ ψ : ℂ → ℂ, AnalyticAt ℂ φ z ∧ AnalyticAt ℂ ψ 0 ∧ φ z=0 ∧ ψ 0=z ∧
      (∀ᶠ w in 𝓝 z, ψ (φ w)=w) ∧ (∀ᶠ u in 𝓝 (0:ℂ), φ (ψ u)=u) ∧
      ∀ᶠ u in 𝓝 (0:ℂ), F (ψ u)=F z+u^2 := by
  have ord : analyticOrderAt (fun w => F w-F z) z = ((2:ℕ):ℕ∞) := by
    rw [← ha.analyticOrderAt_deriv_add_one,ha.deriv.analyticOrderAt_eq_one_of_zero_deriv_ne_zero first second]
    rfl
  obtain ⟨g,ag,ng,factor⟩ := (ha.fun_sub analyticAt_const).analyticOrderAt_eq_natCast.mp ord
  obtain ⟨r,rsq⟩ := IsAlgClosed.exists_pow_nat_eq (g z) (by decide : 0<2)
  have nr : r≠0 := by
    intro h
    apply ng
    rw [← rsq,h,zero_pow (by decide)]
  let sq := fun w : ℂ => w^2
  have aq : AnalyticAt ℂ sq r := analyticAt_id.pow 2
  have dq : deriv sq r≠0 := by simp [sq,nr]
  let root := aq.hasStrictDerivAt.localInverse _ _ _ dq
  have qr : sq r=g z := rsq
  have ar : AnalyticAt ℂ root (g z) := qr ▸ aq.analyticAt_localInverse dq
  have rr : root (g z)=r := qr ▸ (aq.hasStrictDerivAt.eventually_left_inverse dq).self_of_nhds
  have inverseSquare : ∀ᶠ w in 𝓝 (g z), (root w)^2=w := qr ▸ aq.hasStrictDerivAt.eventually_right_inverse dq
  let φ := fun w => (w-z)*root (g w)
  have aφ : AnalyticAt ℂ φ z := (analyticAt_id.fun_sub analyticAt_const).mul (ar.comp ag)
  have center : φ z=0 := by simp [φ]
  have dφ : deriv φ z≠0 := by
    have d := ((hasDerivAt_id z).sub_const z).mul (ar.comp ag).differentiableAt.hasDerivAt
    have h : deriv φ z=r := by simpa [φ,rr,Pi.mul_def,Function.comp_def] using d.deriv
    exact h.trans_ne nr
  have normal : ∀ᶠ w in 𝓝 z, F w=F z+(φ w)^2 := by
    filter_upwards [factor,ag.continuousAt.eventually inverseSquare] with w hw hroot
    change F w=F z+((w-z)*root (g w))^2
    rw [mul_pow,hroot]
    exact eq_add_of_sub_eq' (by simpa only [smul_eq_mul] using hw)
  let ψ := aφ.hasStrictDerivAt.localInverse _ _ _ dφ
  have aψ : AnalyticAt ℂ ψ 0 := center ▸ aφ.analyticAt_localInverse dφ
  have lp : ∀ᶠ w in 𝓝 z, ψ (φ w)=w := aφ.hasStrictDerivAt.eventually_left_inverse dφ
  have rp : ∀ᶠ u in 𝓝 (0:ℂ), φ (ψ u)=u := center ▸ aφ.hasStrictDerivAt.eventually_right_inverse dφ
  have cp : ψ 0=z := center ▸ lp.self_of_nhds
  refine ⟨φ,ψ,aφ,aψ,center,cp,lp,rp,?_⟩
  filter_upwards [(show Tendsto ψ (𝓝 0) (𝓝 z) from cp ▸ aψ.continuousAt.tendsto).eventually normal,rp] with u hf hu
  simpa only [hu] using hf

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.holomorphic_simple_critical_coordinate
