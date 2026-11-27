import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.AbsMax

namespace TwoAxisHelicoid
open Complex Set Filter Metric InnerProductSpace
open scoped Topology

theorem harmonic_eventually_constant_at_local_max {f : ℂ → ℝ} {z : ℂ}
    (hf : HarmonicAt f z) (hm : IsLocalMax f z) :
    ∀ᶠ w in 𝓝 z, f w = f z := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_setOfPred_harmonicAt f).mem_nhds hf)
  have hball : HarmonicOnNhd f (ball z r) := fun w hw => hsub hw
  obtain ⟨F,hF,he⟩ := hball.exists_analyticOnNhd_ball_re_eq
  have hz : z ∈ ball z r := mem_ball_self hr
  have hdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun v => exp (F v)) w := by
    filter_upwards [ball_mem_nhds z hr] with w hw
    exact (hF w hw).differentiableAt.cexp
  have hm' : IsLocalMax (norm ∘ fun w => exp (F w)) z := by
    filter_upwards [hm,ball_mem_nhds z hr] with w hw hwr
    simp only [Function.comp_def,Complex.norm_exp,he hwr,he hz]
    exact Real.exp_le_exp.mpr hw
  have hh := Complex.norm_eventually_eq_of_isLocalMax hdiff hm'
  filter_upwards [hh,ball_mem_nhds z hr] with w hw hwr
  simp only [Complex.norm_exp,he hwr,he hz] at hw
  exact Real.exp_injective hw

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_eventually_constant_at_local_max
