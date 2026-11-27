import TwoAxisHelicoid.EndCorrectionDecay
import TwoAxisHelicoid.CompactUniformParameter
import TwoAxisHelicoid.HelicoidGroundState

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

noncomputable def endPotentialKernel (α : ℝ) (q : ℝ × (ℂ × ℂ)) : ℝ :=
  2*‖I*(α : ℂ)+q.2.2‖^2*helicoidGroundState (-α*q.1+q.2.1.re)^2

theorem endPotentialKernel_continuous (α : ℝ) : Continuous (endPotentialKernel α) := by
  unfold endPotentialKernel helicoidGroundState
  fun_prop (disch := intros; positivity)

theorem endPotentialKernel_zero (α y : ℝ) :
    endPotentialKernel α (y,0) = 2*α^2*helicoidGroundState (α*y)^2 := by
  simp [endPotentialKernel,helicoidGroundState,Complex.norm_real,Real.norm_eq_abs,
    sq_abs,neg_mul,Real.cosh_neg]

noncomputable def helicoidEndPotential (α : ℝ) (F D : ℂ → ℂ) (p : ℝ × ℝ) : ℝ :=
  endPotentialKernel α (p.2,(F (planeComplex p),D (planeComplex p)))

/-- The exact potential in the manuscript's end coordinate converges to
the helicoid potential uniformly on every compact translated set. -/
theorem helicoidEndPotential_uniform_limit (α : ℝ) {F D : ℂ → ℂ}
    (hF : Tendsto F (cobounded ℂ) (𝓝 0)) (hD : Tendsto D (cobounded ℂ) (𝓝 0))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ s ≥ S, ∀ p ∈ K,
      |helicoidEndPotential α F D (p+(s,0))-2*α^2*helicoidGroundState (α*p.2)^2| ≤ ε := by
  obtain ⟨δ,hδ,hbound⟩ := continuous_compact_uniform_small_parameter
    (endPotentialKernel_continuous α) (hK.image continuous_snd) hε
  obtain ⟨S₁,hS₁⟩ := complex_decay_uniform_on_translates hF hK hδ
  obtain ⟨S₂,hS₂⟩ := complex_decay_uniform_on_translates hD hK hδ
  refine ⟨max S₁ S₂,?_⟩
  intro s hs p hp
  have hh := hbound p.2 ⟨p,hp,rfl⟩ (F (planeComplex p+s),D (planeComplex p+s))
    (norm_prod_le_iff.mpr ⟨hS₁ s ((le_max_left _ _).trans hs) p hp,
      hS₂ s ((le_max_right _ _).trans hs) p hp⟩)
  rw [endPotentialKernel_zero] at hh
  simpa only [Real.dist_eq,helicoidEndPotential,planeComplex_translate,Prod.snd_add,add_zero] using hh

theorem analytic_infinity_helicoid_potential_limit (α : ℝ) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ s ≥ S, ∀ p ∈ K,
      |helicoidEndPotential α (infinityCorrection f) (deriv (infinityCorrection f)) (p+(s,0))-
        2*α^2*helicoidGroundState (α*p.2)^2| ≤ ε :=
  helicoidEndPotential_uniform_limit α (infinityCorrection_tendsto_zero hf h0)
    (infinityCorrection_deriv_tendsto_zero hf) hK hε

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidEndPotential_uniform_limit
#print axioms TwoAxisHelicoid.analytic_infinity_helicoid_potential_limit
