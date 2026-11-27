import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

noncomputable def planeComplex (p : ℝ × ℝ) : ℂ := (p.1 : ℂ)+I*(p.2 : ℂ)

theorem planeComplex_re (p : ℝ × ℝ) : (planeComplex p).re = p.1 := by simp [planeComplex]
theorem planeComplex_im (p : ℝ × ℝ) : (planeComplex p).im = p.2 := by simp [planeComplex]
theorem planeComplex_translate (p : ℝ × ℝ) (s : ℝ) :
    planeComplex (p+(s,0)) = planeComplex p+s := by
  simp [planeComplex]
  ring

/-- A correction holomorphic in the inverse coordinate at the puncture. -/
noncomputable def infinityCorrection (f : ℂ → ℂ) (z : ℂ) : ℂ := f z⁻¹

theorem infinityCorrection_tendsto_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (h0 : f 0 = 0) : Tendsto (infinityCorrection f) (cobounded ℂ) (𝓝 0) := by
  simpa only [infinityCorrection,Function.comp_def,h0] using!
    hf.continuousAt.tendsto.comp (Filter.tendsto_inv₀_cobounded (α := ℂ))

theorem infinityCorrection_deriv_tendsto_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    Tendsto (deriv (infinityCorrection f)) (cobounded ℂ) (𝓝 0) := by
  have hi := Filter.tendsto_inv₀_cobounded (α := ℂ)
  have hd := hf.deriv.continuousAt.tendsto.comp hi
  have hp : Tendsto (fun z : ℂ => deriv f z⁻¹*(-(z⁻¹)^2)) (cobounded ℂ) (𝓝 0) := by
    simpa only [Function.comp_def,zero_pow (by decide : 2 ≠ 0),neg_zero,mul_zero] using!
      hd.mul ((hi.pow 2).neg)
  apply hp.congr'
  filter_upwards [hi.eventually hf.eventually_analyticAt,
    eventually_cobounded_le_norm (E := ℂ) (1 : ℝ)] with z hz hnorm
  have hnz : z ≠ 0 := by intro h; norm_num [h] at hnorm
  have h := hz.differentiableAt.hasDerivAt.comp z (hasDerivAt_inv hnz)
  simpa only [inv_pow,Function.comp_def,infinityCorrection] using! h.deriv.symm

/-- Decay at complex infinity is uniform under real translations of any
fixed compact set of planar coordinates. -/
theorem complex_decay_uniform_on_translates {F : ℂ → ℂ}
    (hF : Tendsto F (cobounded ℂ) (𝓝 0)) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ s ≥ S, ∀ p ∈ K, ‖F (planeComplex p+s)‖ ≤ ε := by
  have he : ∀ᶠ z in cobounded ℂ, ‖F z‖ < ε := by
    simpa only [Metric.mem_ball,dist_zero_right] using hF.eventually (Metric.ball_mem_nhds 0 hε)
  obtain ⟨R,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  obtain ⟨C,hC,hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R+C+1,?_⟩
  intro s hs p hp
  have hfirst : |p.1| ≤ C := (norm_fst_le p).trans (hbound p hp)
  have hr : R ≤ ‖planeComplex p+s‖ := by
    have hre := Complex.re_le_norm (planeComplex p+s)
    rw [Complex.add_re,Complex.ofReal_re,planeComplex_re] at hre
    have hlow := (abs_le.mp hfirst).1
    linarith
  exact (hR hr).le

theorem infinityCorrection_uniform_decay {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (h0 : f 0 = 0) {K : Set (ℝ × ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ s ≥ S, ∀ p ∈ K,
      ‖infinityCorrection f (planeComplex p+s)‖ ≤ ε ∧
      ‖deriv (infinityCorrection f) (planeComplex p+s)‖ ≤ ε := by
  obtain ⟨S₁,hS₁⟩ := complex_decay_uniform_on_translates
    (infinityCorrection_tendsto_zero hf h0) hK hε
  obtain ⟨S₂,hS₂⟩ := complex_decay_uniform_on_translates
    (infinityCorrection_deriv_tendsto_zero hf) hK hε
  refine ⟨max S₁ S₂,?_⟩
  intro s hs p hp
  exact ⟨hS₁ s ((le_max_left _ _).trans hs) p hp,hS₂ s ((le_max_right _ _).trans hs) p hp⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.infinityCorrection_deriv_tendsto_zero
#print axioms TwoAxisHelicoid.infinityCorrection_uniform_decay
