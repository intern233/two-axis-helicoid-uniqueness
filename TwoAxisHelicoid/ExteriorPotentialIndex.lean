import TwoAxisHelicoid.PlanarIndexAtInfinity
import TwoAxisHelicoid.HelicoidEndPotential
import Mathlib.Topology.TietzeExtension

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology ContDiff

theorem continuous_potential_extension_from_exterior {W : ℝ × ℝ → ℝ} {R : ℝ}
    (hW : ContinuousOn W {p | R ≤ ‖p‖}) :
    ∃ U : ℝ × ℝ → ℝ, Continuous U ∧ ∀ p, R ≤ ‖p‖ → U p = W p := by
  let K : Set (ℝ × ℝ) := {p | R ≤ ‖p‖}
  have hK : IsClosed K := isClosed_le continuous_const continuous_norm
  let f : C(K,ℝ) := ⟨fun p => W p,continuousOn_iff_continuous_domRestrict.mp hW⟩
  obtain ⟨U,hU⟩ := ContinuousMap.exists_restrict_eq hK f
  refine ⟨U,U.continuous,?_⟩
  intro p hp
  exact congrArg (fun g : C(K,ℝ) => g ⟨p,hp⟩) hU

theorem potential_uniform_limit_of_exterior_eq {W U : ℝ × ℝ → ℝ} {V : ℝ → ℝ} {R : ℝ}
    (he : ∀ p, R ≤ ‖p‖ → U p = W p)
    (hlimit : ∀ K : Set (ℝ × ℝ), IsCompact K → ∀ ε > 0, ∃ S : ℝ,
      ∀ s ≥ S, ∀ p ∈ K, |W (p+(s,0))-V p.2| ≤ ε) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → ∀ ε > 0, ∃ S : ℝ,
      ∀ s ≥ S, ∀ p ∈ K, |U (p+(s,0))-V p.2| ≤ ε := by
  intro K hK ε hε
  obtain ⟨S₁,hS₁⟩ := hlimit K hK ε hε
  obtain ⟨S₂,hS₂⟩ := compact_planar_translates_escape hK R
  refine ⟨max S₁ S₂,?_⟩
  intro s hs p hp
  rw [he (p+(s,0)) (hS₂ s ((le_max_right _ _).trans hs) p hp).le]
  exact hS₁ s ((le_max_left _ _).trans hs) p hp

/-- Interior singularities of the end-coordinate potential are harmless:
all negative test spaces can be supported outside any prescribed compact
set. A continuous extension is constructed and then removed from the result. -/
theorem infinite_planar_index_of_exterior_limit {W : ℝ × ℝ → ℝ} {V : ℝ → ℝ} {R : ℝ}
    (hW : ContinuousOn W {p | R ≤ ‖p‖}) (hV : Continuous V)
    (hn : ∀ y, 0 ≤ V y) (hp : 0 < V 0)
    (hlimit : ∀ K : Set (ℝ × ℝ), IsCompact K → ∀ ε > 0, ∃ S : ℝ,
      ∀ s ≥ S, ∀ p ∈ K, |W (p+(s,0))-V p.2| ≤ ε) :
    HasInfiniteCompactPlanarIndexAtInfinity W := by
  obtain ⟨U,hU,he⟩ := continuous_potential_extension_from_exterior hW
  have hi := infinite_planar_index_at_infinity_of_potential_limit hU hV hn hp
    (potential_uniform_limit_of_exterior_eq he hlimit)
  exact hi.congr_outside he

theorem planeComplex_continuous : Continuous planeComplex := by
  unfold planeComplex
  fun_prop

theorem norm_le_planeComplex_norm (p : ℝ × ℝ) : ‖p‖ ≤ ‖planeComplex p‖ := by
  rw [Prod.norm_def]
  apply max_le
  · simpa only [Real.norm_eq_abs,planeComplex_re] using Complex.abs_re_le_norm (planeComplex p)
  · simpa only [Real.norm_eq_abs,planeComplex_im] using Complex.abs_im_le_norm (planeComplex p)

theorem infinityCorrection_eventually_analytic {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∀ᶠ z in cobounded ℂ, AnalyticAt ℂ (infinityCorrection f) z := by
  filter_upwards [(Filter.tendsto_inv₀_cobounded (α := ℂ)).eventually hf.eventually_analyticAt,
    eventually_cobounded_le_norm (E := ℂ) (1 : ℝ)] with z hz hnorm
  have hnz : z ≠ 0 := by intro h; norm_num [h] at hnorm
  simpa only [infinityCorrection,Function.comp_def] using! hz.comp (analyticAt_inv hnz)

theorem helicoidEndPotential_continuous_exterior (α : ℝ) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) : ∃ R > 0,
    ContinuousOn (helicoidEndPotential α (infinityCorrection f) (deriv (infinityCorrection f)))
      {p | R ≤ ‖p‖} := by
  obtain ⟨R,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
    (infinityCorrection_eventually_analytic hf)
  refine ⟨max R 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro p hp
  have hz := hR ((le_max_left R 1).trans (hp.trans (norm_le_planeComplex_norm p)))
  have hF := hz.continuousAt.comp planeComplex_continuous.continuousAt
  have hD := hz.deriv.continuousAt.comp planeComplex_continuous.continuousAt
  have hc := (endPotentialKernel_continuous α).continuousAt.comp
    (continuous_snd.continuousAt.prodMk (hF.prodMk hD))
  exact hc.continuousWithinAt

/-- The actual end-coordinate potential associated with any holomorphic
correction vanishing at infinity has arbitrarily large negative compact
test spaces beyond every compact set. This is the analytic part of the
manuscript's Morse-index argument, before the geometric second variation. -/
theorem analytic_helicoid_end_potential_infinite_index {α : ℝ} (hα : α ≠ 0)
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    HasInfiniteCompactPlanarIndexAtInfinity
      (helicoidEndPotential α (infinityCorrection f) (deriv (infinityCorrection f))) := by
  obtain ⟨R,_hR,hcont⟩ := helicoidEndPotential_continuous_exterior α hf
  apply infinite_planar_index_of_exterior_limit
    (V := fun y => 2*α^2*helicoidGroundState (α*y)^2) hcont
  · unfold helicoidGroundState
    fun_prop (disch := intros; positivity)
  · intro y; positivity
  · have hp := sq_pos_of_ne_zero hα
    norm_num [helicoidGroundState]
    nlinarith
  · intro K hK ε hε
    exact analytic_infinity_helicoid_potential_limit α hf h0 hK hε

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.continuous_potential_extension_from_exterior
#print axioms TwoAxisHelicoid.analytic_helicoid_end_potential_infinite_index
