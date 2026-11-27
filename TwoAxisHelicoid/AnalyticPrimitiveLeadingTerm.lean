import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Filter Topology
open scoped Topology

/-- If a holomorphic derivative factors as z^n times an analytic germ h,
the centered primitive factors as z^(n+1) times a germ with value
h(0)/(n+1). The extension of that germ away from zero may be chosen so
that the factorization of the given primitive is an actual equality. -/
theorem analytic_primitive_leading_factor (F H : ℂ → ℂ) (n : ℕ)
    (hF : AnalyticAt ℂ F 0) (hH : AnalyticAt ℂ H 0)
    (hD : deriv F =ᶠ[𝓝 0] fun z => z^n*H z) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ (∀ z, F z = F 0+z^(n+1)*G z) ∧
      ((n:ℂ)+1)*G 0 = H 0 := by
  let f := fun z => F z-F 0
  have hf : AnalyticAt ℂ f 0 := hF.sub analyticAt_const
  have hf₀ : f 0 = 0 := sub_self _
  have hd : deriv f =ᶠ[𝓝 0] fun z => z^n*H z := by
    filter_upwards [hF.eventually_analyticAt,hD] with z hz h
    exact (hz.differentiableAt.hasDerivAt.sub_const (F 0)).deriv.trans h
  have ho : (n:ℕ∞) ≤ analyticOrderAt (deriv f) 0 := by
    apply (natCast_le_analyticOrderAt hf.deriv).2
    exact ⟨H,hH,by filter_upwards [hd] with z h using by simpa only [sub_zero,smul_eq_mul] using h⟩
  have ho' : ((n+1:ℕ):ℕ∞) ≤ analyticOrderAt f 0 := by
    simpa only [Nat.cast_add_one] using (analyticOrderAt_deriv_ge_iff hf hf₀).1 ho
  obtain ⟨g,hg,hfg⟩ := (natCast_le_analyticOrderAt hf).1 ho'
  let G := fun z : ℂ => if z = 0 then g 0 else f z / z^(n+1)
  have germ : G =ᶠ[𝓝 0] g := by
    filter_upwards [hfg] with z hz
    by_cases h : z = 0
    · simp [G,h]
    · simp only [G,ite_eq_right h,hz,sub_zero,smul_eq_mul]
      field_simp
  have hG : AnalyticAt ℂ G 0 := hg.congr germ.symm
  have equal (z : ℂ) : f z = z^(n+1)*G z := by
    by_cases h : z = 0
    · simp [h,hf₀]
    · simp [G,h,mul_div_cancel₀]
  refine ⟨G,hG,fun z => by have h := equal z; dsimp [f] at h; linear_combination h,?_⟩
  have co : (fun z => ((n:ℂ)+1)*G z+z*deriv G z) =ᶠ[𝓝[≠] 0] H := by
    filter_upwards [hG.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      hd.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz h hn
    have hn' : z ≠ 0 := hn
    have hp := ((hasDerivAt_id z).pow (n+1)).mul hz.differentiableAt.hasDerivAt
    have e := hp.deriv
    change deriv (fun w => w^(n+1)*G w) z = _ at e
    rw [← funext equal] at e
    change deriv f z = _ at e
    rw [h] at e
    apply mul_left_cancel₀ (pow_ne_zero n hn')
    calc
      _ = (((n:ℂ)+1)*z^n*1)*G z+z^(n+1)*deriv G z := by ring
      _ = z^n*H z := by simpa only [Nat.cast_add_one,Nat.add_sub_cancel,id_eq,Pi.pow_apply] using e.symm
  have hcont : ContinuousAt (fun z : ℂ => ((n:ℂ)+1)*G z+z*deriv G z) 0 :=
    (continuousAt_const.mul hG.continuousAt).add (continuousAt_id.mul hG.deriv.continuousAt)
  simpa only [zero_mul,add_zero] using tendsto_nhds_unique_of_eventuallyEq
    (hcont.continuousWithinAt (s := ({0}:Set ℂ)ᶜ)) hH.continuousAt.continuousWithinAt co

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_primitive_leading_factor
