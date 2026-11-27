import TwoAxisHelicoid.ProjectedHeightChart
import TwoAxisHelicoid.PointedTorusUniformization
import TwoAxisHelicoid.ActualTorusManifoldImmersion
import TwoAxisHelicoid.HeightInverseRegularity

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bornology
open scoped Topology ContDiff Manifold

/-- Mutually inverse analytic germs at the puncture and at infinity give a
biholomorphic exterior chart of the marked punctured torus with compact core.
Its radius may be chosen beyond any previously prescribed cutoff. -/
theorem marked_torus_exterior_height_chart (L : PeriodPair) (b : PuncturedPeriodTorus L)
    (H K : ℂ → ℂ) (hH : Tendsto H (𝓝[≠] 0) (cobounded ℂ)) (hK : Tendsto K (cobounded ℂ) (𝓝[≠] 0))
    (hleft : ∀ᶠ z in 𝓝[≠] (0:ℂ), K (H z) = z)
    (hright : ∀ᶠ ξ in cobounded ℂ, H (K ξ) = ξ)
    (hHa : ∀ᶠ z in 𝓝[≠] (0:ℂ), AnalyticAt ℂ H z)
    (hKa : ∀ᶠ ξ in cobounded ℂ, AnalyticAt ℂ K ξ) (B : ℝ) :
    ∃ (e : OpenPartialHomeomorph (PuncturedPeriodTorus L) ℂ) (R : ℝ), 0 < R ∧ B < R ∧
      e.target = {ξ : ℂ | R < ‖ξ‖} ∧ IsCompact e.sourceᶜ ∧
      e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (PuncturedPeriodTorus L) ∧
      ∀ ξ ∈ e.target, (e.symm ξ).1 = periodTorusProjection L (K ξ) := by
  let := periodTorus_compactSpace L
  obtain ⟨h,heH,heK,hs,ht⟩ := puncture_inverse_open_chart hH hK hleft hright
    (hHa.mono (fun _ ha => ha.continuousAt)) (hKa.mono (fun _ ha => ha.continuousAt))
  obtain ⟨P,hP₀,hP⟩ := periodTorusProjection_isLocalHomeomorph L (0:ℂ)
  have h0 : P 0 = 0 := by rw [← hP]; exact (periodTorusProjection_eq_zero L 0).mpr L.lattice.zero_mem
  have hop : IsOpenMap (P : ℂ → PeriodTorus L) := by rw [← hP]; exact QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap
  have hPmax : P.symm ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (PeriodTorus L) :=
    IsManifold.subset_maximalAtlas (show P.symm ∈ atlas ℂ (PeriodTorus L) from hP.symm)
  obtain ⟨d,htail,hinv⟩ := projected_puncture_height_chart ⟨b⟩ P hP₀ h0 hop h hs ht
    (heH.symm ▸ hH) (heK.symm ▸ hK)
  have hg := hinv.and (hKa.and (hright.and ((hK.eventually hHa).and
    (hK.eventually (nhdsWithin_le_nhds (P.open_source.mem_nhds hP₀))))))
  obtain ⟨r,_,hr⟩ := hasBasis_cobounded_norm.eventually_iff.mp hg
  let R := max (max B r) 0 + 1
  let T := {ξ : ℂ | R < ‖ξ‖}
  have hTo : IsOpen T := isOpen_lt continuous_const continuous_norm
  have hR : r < R := by dsimp [R]; linarith [le_max_right B r,le_max_left (max B r) 0]
  have hR' : B < R := by dsimp [R]; linarith [le_max_left B r,le_max_left (max B r) 0]
  have hR0 : 0 < R := by dsimp [R]; linarith [le_max_right (max B r) 0]
  let e := d.trans (OpenPartialHomeomorph.ofSet T hTo)
  have hsmall {ξ : ℂ} (hx : ξ ∈ T) := hr (hR.trans hx).le
  have htarget : e.target = T := by
    ext ξ
    change ξ ∈ T ∧ ξ ∈ d.target ↔ ξ ∈ T
    exact ⟨And.left,fun hx => ⟨hx,(hsmall hx).1.1⟩⟩
  have hinverse (ξ : ℂ) (hx : ξ ∈ T) : (e.symm ξ).1 = P (K ξ) := by
    change (d.symm ξ).1 = P (K ξ)
    simpa only [heK] using (hsmall hx).1.2
  have hforward (x) (hx : x ∈ e.source) : x.1 ∈ P.target ∧ P.symm x.1 = K (e x) ∧ H (P.symm x.1) = e x := by
    have ht' : e x ∈ T := htarget ▸ e.map_source hx
    have hxe := congrArg Subtype.val (e.left_inv hx)
    have hp : P (K (e x)) = x.1 := (hinverse _ ht').symm.trans hxe
    have hz := (hsmall ht').2.2.2.2
    have heq : P.symm x.1 = K (e x) := by rw [← hp,P.left_inv hz]
    exact ⟨hp ▸ P.map_source hz,heq,heq ▸ (hsmall ht').2.2.1⟩
  obtain ⟨C,hC,hCt⟩ := htail R
  have hcore : IsCompact e.sourceᶜ := hC.of_isClosed_subset e.open_source.isClosed_compl (by
    intro x hx
    by_contra hn
    have hh := hCt x hn
    exact hx ⟨hh.1,hh.2⟩)
  refine ⟨e,R,hR0,hR',htarget,hcore,?_,fun ξ hξ => (hinverse ξ (htarget ▸ hξ)).trans (congrFun hP (K ξ)).symm⟩
  apply e.mem_maximalAtlas_of_contMDiffOn
  · intro x hx
    obtain ⟨hp,hxK,_⟩ := hforward x hx
    have ha : AnalyticAt ℂ H (P.symm x.1) := hxK.symm ▸ (hsmall (htarget ▸ e.map_source hx)).2.2.2.1
    have hA : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H (P.symm x.1) := contMDiffAt_iff_contDiffAt.mpr ha.contDiffAt
    have hs' := (contMDiffAt_of_mem_maximalAtlas hPmax hp).comp x
      (contMDiff_subtype_val (U := puncturedPeriodTorusOpen L)).contMDiffAt
    apply ContMDiffAt.contMDiffWithinAt
    apply (hA.comp x hs').congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact (hforward y hy).2.2.symm
  · intro ξ hξ
    have ht' := htarget ▸ hξ
    have hKa' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω K ξ := contMDiffAt_iff_contDiffAt.mpr (hsmall ht').2.1.contDiffAt
    have hg' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun ζ => (e.symm ζ).1) ξ := by
      apply ((periodTorusProjection_contMDiff L).contMDiffAt.comp ξ hKa').congr_of_eventuallyEq
      filter_upwards [hTo.mem_nhds ht'] with η hη
      exact (hinverse η hη).trans (congrFun hP (K η)).symm
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := puncturedPeriodTorusOpen L) e.symm e.target ξ).mp
    exact hg'.contMDiffWithinAt

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_torus_exterior_height_chart
