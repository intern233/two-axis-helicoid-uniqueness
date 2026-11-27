import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Set Metric Filter
open scoped Topology

/-- A locally real-analytic zero set in a connected parameter domain which
contains one open patch contains the entire domain. The defining function
may change charts. -/
theorem analytic_zero_locus_continues {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U P : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (hl : ∀ z ∈ U, ∃ f : ℂ → V, AnalyticAt ℝ f z ∧
      ∀ᶠ w in 𝓝 z, w ∈ P ↔ f w = 0)
    {b : ℂ} (hb : b ∈ U) (hpatch : P ∈ 𝓝 b) : U ⊆ P := by
  let R := U ∩ interior P
  let S := U \ interior P
  have hR : IsOpen R := hU.inter isOpen_interior
  have hS : IsOpen S := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨f,hf,he⟩ := hl z hz.1
    have ha : ∀ᶠ w in 𝓝 z, AnalyticAt ℝ f w := (isOpen_analyticAt ℝ f).mem_nhds hf
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((show ∀ᶠ w in 𝓝 z, w ∈ U from hU.mem_nhds hz.1).and (ha.and he))
    refine ⟨r,hr,?_⟩
    intro w hw
    refine ⟨(hsub hw).1,?_⟩
    intro hi
    have zero : f =ᶠ[𝓝 w] 0 := by
      filter_upwards [isOpen_ball.mem_nhds hw,mem_interior_iff_mem_nhds.mp hi] with v hv hp
      exact (hsub hv).2.2.mp hp
    have hall := (show AnalyticOnNhd ℝ f (ball z r) from fun v hv => (hsub hv).2.1
      ).eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball z r).isPreconnected hw zero
    apply hz.2
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [ball_mem_nhds z hr] with v hv
    exact (hsub hv).2.2.mpr (hall hv)
  have hdis : Disjoint R S := disjoint_left.mpr (fun _ hr hs => hs.2 hr.2)
  have hcov : U ⊆ R ∪ S := by
    intro z hz
    by_cases h : z ∈ interior P
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr ⟨hz,h⟩
  rcases hc.subset_or_subset hR hS hdis hcov with h | h
  · exact fun z hz => interior_subset (h hz).2
  · exact False.elim ((h hb).2 (mem_interior_iff_mem_nhds.mpr hpatch))

/-- Local coincidence with a closed embedded analytic hypersurface
propagates along the entire analytic parametrization. The defining
equations are local in the ambient space. -/
theorem analytic_image_continues_in_closed_hypersurface
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {Y : ℂ → E} (hY : AnalyticOnNhd ℝ Y U)
    {K : Set E} (hK : IsClosed K) (hlocal : ∀ p ∈ K, ∃ G : E → V, AnalyticAt ℝ G p ∧
      ∀ᶠ v in 𝓝 p, v ∈ K ↔ G v = 0)
    {b : ℂ} (hb : b ∈ U) (hpatch : ∀ᶠ w in 𝓝 b, Y w ∈ K) : MapsTo Y U K := by
  apply analytic_zero_locus_continues (V := V) hU hc (P := Y ⁻¹' K) _ hb hpatch
  intro z hz
  by_cases hp : Y z ∈ K
  · obtain ⟨G,hG,he⟩ := hlocal _ hp
    exact ⟨G ∘ Y,hG.comp (hY z hz),(hY z hz).continuousAt.eventually he⟩
  · obtain ⟨v,hv⟩ := exists_ne (0 : V)
    refine ⟨fun _ => v,analyticAt_const,?_⟩
    filter_upwards [(hY z hz).continuousAt.eventually (hK.isOpen_compl.mem_nhds hp)] with w hw
    exact iff_of_false hw hv

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_image_continues_in_closed_hypersurface
