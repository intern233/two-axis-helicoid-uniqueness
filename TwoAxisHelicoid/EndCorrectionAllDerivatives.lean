module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

public section

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

private theorem reciprocal_germ_decay {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    Tendsto (fun z : ℂ => f z⁻¹) (cobounded ℂ) (𝓝 0) := by
  simpa only [Function.comp_def,h0] using!
    hf.continuousAt.tendsto.comp (Filter.tendsto_inv₀_cobounded (α := ℂ))

private theorem uniform_on_compact_translates {F : ℂ → ℂ}
    (hF : Tendsto F (cobounded ℂ) (𝓝 0)) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∃ S : ℝ, ∀ s ≥ S, ∀ p ∈ K, ‖F ((p.1 : ℂ) + I*(p.2 : ℂ) + s)‖ ≤ ε := by
  have he : ∀ᶠ z in cobounded ℂ, ‖F z‖ < ε := by
    simpa only [Metric.mem_ball,dist_zero_right] using hF.eventually (Metric.ball_mem_nhds 0 hε)
  obtain ⟨R,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  obtain ⟨C,_,bound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R+C+1,?_⟩
  intro s hs p hp
  have first : |p.1| ≤ C := (norm_fst_le p).trans (bound p hp)
  have re : p.1+s ≤ ‖(p.1 : ℂ)+I*(p.2 : ℂ)+s‖ := by
    simpa using Complex.re_le_norm ((p.1 : ℂ)+I*(p.2 : ℂ)+s)
  have far : R ≤ ‖(p.1 : ℂ)+I*(p.2 : ℂ)+s‖ := by linarith [(abs_le.mp first).1]
  exact (hR far).le

/-- Differentiation in the exterior variable acts on its inverse-coordinate germ by
`g(w) ↦ -w² g'(w)`. Thus every complex derivative has an analytic germ vanishing
at the puncture, independently of how the correction is defined on the compact core. -/
theorem infinityCorrection_iteratedDeriv_germ {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (h0 : f 0 = 0) (n : ℕ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧
      iteratedDeriv n ((fun z : ℂ => f z⁻¹)) =ᶠ[cobounded ℂ] (fun z : ℂ => g z⁻¹) := by
  induction n with
  | zero =>
    refine ⟨f,hf,h0,?_⟩
    simpa only [iteratedDeriv_zero] using
      (Filter.EventuallyEq.rfl : (fun z : ℂ => f z⁻¹) =ᶠ[cobounded ℂ] (fun z : ℂ => f z⁻¹))
  | succ n ih =>
    obtain ⟨g,hg,_,agree⟩ := ih
    let d : ℂ → ℂ := fun w => deriv g w * (-(w ^ 2))
    refine ⟨d,hg.deriv.mul (analyticAt_id.pow 2).neg,by simp [d],?_⟩
    obtain ⟨R,_,onExterior⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp agree
    have hi := Filter.tendsto_inv₀_cobounded (α := ℂ)
    filter_upwards [hi.eventually hg.eventually_analyticAt,
      eventually_cobounded_le_norm (E := ℂ) (R+1),
      eventually_cobounded_le_norm (E := ℂ) (1 : ℝ)] with z analytic large nonzero
    have lt : R < ‖z‖ := lt_of_lt_of_le (lt_add_one R) large
    have localEq : iteratedDeriv n ((fun z : ℂ => f z⁻¹)) =ᶠ[𝓝 z] (fun z : ℂ => g z⁻¹) := by
      filter_upwards [continuous_norm.continuousAt.tendsto.eventually (lt_mem_nhds lt)] with w hw
      exact onExterior hw.le
    have nz : z ≠ 0 := by intro h; norm_num [h] at nonzero
    have chain := analytic.differentiableAt.hasDerivAt.comp z (hasDerivAt_inv nz)
    rw [iteratedDeriv_succ,localEq.deriv_eq]
    simpa only [d,Function.comp_def,inv_pow] using! chain.deriv

/-- On any fixed compact set translated to the right, the correction and
all its complex derivatives up to any prescribed order tend to zero uniformly. -/
theorem infinityCorrection_uniform_decay_through_order {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (h0 : f 0 = 0) {K : Set (ℝ × ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∃ S : ℝ, ∀ s ≥ S, ∀ p ∈ K, ∀ j ≤ n,
      ‖iteratedDeriv j ((fun z : ℂ => f z⁻¹)) ((p.1 : ℂ) + I*(p.2 : ℂ) + s)‖ ≤ ε := by
  have one (j : ℕ) : ∃ S : ℝ, ∀ s ≥ S, ∀ p ∈ K,
      ‖iteratedDeriv j ((fun z : ℂ => f z⁻¹)) ((p.1 : ℂ) + I*(p.2 : ℂ) + s)‖ ≤ ε := by
    obtain ⟨g,hg,hg0,agree⟩ := infinityCorrection_iteratedDeriv_germ hf h0 j
    exact uniform_on_compact_translates
      ((reciprocal_germ_decay hg hg0).congr' agree.symm) hK hε
  induction n with
  | zero =>
    obtain ⟨S,hs⟩ := one 0
    refine ⟨S,?_⟩
    intro s hS p hp j hj
    obtain rfl := Nat.le_zero.mp hj
    exact hs s hS p hp
  | succ n ih =>
    obtain ⟨S,hs⟩ := ih
    obtain ⟨T,ht⟩ := one (n+1)
    refine ⟨max S T,?_⟩
    intro s h p hp j hj
    rcases lt_or_eq_of_le hj with less | rfl
    · exact hs s ((le_max_left _ _).trans h) p hp j (Nat.le_of_lt_succ less)
    · exact ht s ((le_max_right _ _).trans h) p hp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.infinityCorrection_iteratedDeriv_germ
#print axioms TwoAxisHelicoid.infinityCorrection_uniform_decay_through_order
