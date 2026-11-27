import TwoAxisHelicoid.PrimitiveDoublePoleExpansion
import TwoAxisHelicoid.HeightGaussEndNormalForm
import Mathlib.Analysis.Calculus.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- The nonzero pitch in the local end theorem follows already from
the logarithmic Gauss pole and the holomorphic differential remainder. -/
theorem logarithmic_gauss_pole_forces_pitch {g h K : ℂ → ℂ} {α : ℝ}
    (order : meromorphicOrderAt (logDeriv g) 0=(-2:ℤ)) (an : AnalyticAt ℂ K 0)
    (remainder : (fun z => logDeriv g z-I*(α:ℂ)*h z) =ᶠ[𝓝[≠] (0:ℂ)] K) : α≠0 := by
  intro zero
  have eq : logDeriv g =ᶠ[𝓝[≠] (0:ℂ)] K := by simpa only [zero,ofReal_zero,mul_zero,zero_mul,sub_zero] using remainder
  have nonneg := an.meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr eq,order] at nonneg
  exact (by decide : ¬(0:WithTop ℤ)≤(-2:ℤ)) nonneg

/-- From the holomorphic extension of dg/g − k dh obtain an actual
single-valued exponential correction, for any height primitive H on
the punctured disk. No logarithm of g on the annulus is assumed. -/
theorem holomorphic_log_difference_integrates {g H h K : ℂ → ℂ} {k : ℂ}
    (an : AnalyticAt ℂ K 0)
    (endData : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g z ∧ g z≠0 ∧
      HasDerivAt H (h z) z ∧ logDeriv g z-k*h z=K z) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (K z) z ∧ g z=exp (k*H z+F z) := by
  obtain ⟨r,hr,sub⟩ := Metric.mem_nhdsWithin_iff.mp (endData.and (an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds))
  let B := ball (0:ℂ) r
  let U := B \ {0}
  have reg (z : ℂ) (hz : z∈B) : AnalyticAt ℂ K z := by
    by_cases e : z=0
    · exact e ▸ an
    · exact (sub ⟨hz,e⟩).2
  let P := fun z => wedgeIntegral 0 z K
  have dK : DifferentiableOn ℂ K B := fun z hz => (reg z hz).differentiableAt.differentiableWithinAt
  have dP (z : ℂ) (hz : z∈B) : HasDerivAt P (K z) z := dK.isConservativeOn.hasDerivAt_wedgeIntegral dK.continuousOn hz
  have aP : AnalyticAt ℂ P 0 := (show DifferentiableOn ℂ P B from fun z hz =>
    (dP z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball 0 (mem_ball_self hr)
  let W := fun z => g z*exp (-(k*H z+P z))
  have dW (z : ℂ) (hz : z∈U) : HasDerivAt W 0 z := by
    obtain ⟨dg,ng,dh,eq⟩ := (sub hz).1
    have der := dg.hasDerivAt.mul (((dh.const_mul k).add (dP z hz.1)).neg.cexp)
    convert der using 1
    change 0=deriv g z*exp (-(k*H z+P z))+g z*(exp (-(k*H z+P z))*(-(k*h z+K z)))
    rw [← eq,logDeriv_apply]
    field_simp [ng]
    ring
  have op : IsOpen U := isOpen_ball.sdiff (isClosed_singleton (X := ℂ))
  have co : IsPreconnected U := complex_ball_diff_finite_isPreconnected 0 hr (finite_singleton 0)
  obtain ⟨C,constant⟩ := op.exists_is_const_of_deriv_eq_zero co
    (fun z hz => (dW z hz).differentiableAt.differentiableWithinAt) (fun z hz => (dW z hz).deriv)
  have near : ∀ᶠ z in 𝓝[≠] (0:ℂ), z∈U := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) hr),self_mem_nhdsWithin] with z hz hne
    exact ⟨hz,hne⟩
  obtain ⟨w,hw⟩ := near.exists
  have unit : C≠0 := by rw [← constant w hw]; exact mul_ne_zero (sub hw).1.2.1 (exp_ne_zero _)
  refine ⟨fun z => P z+log C,aP.add analyticAt_const,?_⟩
  filter_upwards [near] with z hz
  refine ⟨(dP z hz.1).add_const _,?_⟩
  calc
    g z = W z*exp (k*H z+P z) := by simp only [W,mul_assoc,← exp_add,neg_add_cancel,exp_zero,mul_one]
    _ = exp (k*H z+(P z+log C)) := by rw [constant z hz,← add_assoc,exp_add (k*H z+P z) (log C),exp_log unit,mul_comm]

/-- For the finite-topology end of Proposition 2.1 the correction can
be made zero at the puncture by an additive constant in the height
coordinate. Its full derivative remains the given holomorphic germ. -/
theorem general_end_normalized_exponential_of_log_difference {g H h K : ℂ → ℂ} {α : ℝ}
    (order : meromorphicOrderAt (logDeriv g) 0=(-2:ℤ)) (an : AnalyticAt ℂ K 0)
    (endData : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g z ∧ g z≠0 ∧
      HasDerivAt H (h z) z ∧ logDeriv g z-I*(α:ℂ)*h z=K z) :
    α≠0 ∧ ∃ (c : ℂ) (F : ℂ → ℂ), AnalyticAt ℂ F 0 ∧ F 0=0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (K z) z ∧ g z=exp (I*(α:ℂ)*(H z+c)+F z) := by
  have non := logarithmic_gauss_pole_forces_pitch order an (endData.mono fun _ h => h.2.2.2)
  let k := I*(α:ℂ)
  have kn : k≠0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr non)
  obtain ⟨P,ap,formula⟩ := holomorphic_log_difference_integrates an endData
  refine ⟨non,P 0/k,fun z => P z-P 0,ap.sub analyticAt_const,sub_self _,?_⟩
  filter_upwards [formula] with z hz
  refine ⟨hz.1.sub_const _,hz.2.trans (congrArg exp ?_)⟩
  change k*H z+P z=k*(H z+P 0/k)+(P z-P 0)
  field_simp [kn]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.general_end_normalized_exponential_of_log_difference
