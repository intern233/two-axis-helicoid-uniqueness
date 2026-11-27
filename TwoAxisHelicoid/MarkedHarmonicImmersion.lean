import TwoAxisHelicoid.MarkedPuncturedUniformization
import TwoAxisHelicoid.TorusMarkingChartGerm
import TwoAxisHelicoid.OrientedMinimalHarmonicAtlas
import TwoAxisHelicoid.HarmonicImmersionReparametrization

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Manifold ContDiff Topology OnePoint

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [T2Space M]

/-- The marked torus carries exactly the original parametrized immersion
away from its marked point, with all three harmonic, regular conformal
coordinate conditions on the full lattice complement. -/
theorem marked_harmonic_immersion_coordinates (E : PuncturedComplexEnd M)
    (F : M → Fin 3 → ℝ) (a : Fin 3 → ℝ)
    (hF : ∀ e ∈ atlas ℂ M, HarmonicImmersionChart F e)
    (hM : let _ := compactifiedEndAtlas E; IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M))
    {L : PeriodPair} (H : OnePoint M ≃ₜ PeriodTorus L) (h0 : H OnePoint.infty = 0)
    (hH : let _ := compactifiedEndAtlas E; ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H)
    (hi : let _ := compactifiedEndAtlas E; ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm) :
    let X := fun q : PeriodTorus L => (H.symm q).elim a F
    ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z) := by
  let _ := compactifiedEndAtlas E
  have hm : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := hM
  let X := fun q : PeriodTorus L => (H.symm q).elim a F
  let π := periodTorusProjection L
  dsimp only
  intro z hz
  have hn : H.symm (π z) ≠ OnePoint.infty := by
    intro he
    apply hz
    apply (periodTorusProjection_eq_zero L z).mp
    exact (H.apply_symm_apply (π z)).symm.trans ((congrArg H he).trans h0)
  obtain ⟨x,hx⟩ := OnePoint.ne_infty_iff_exists.mp hn
  let e := chartAt ℂ x
  let χ := finiteOnePointChart e
  have hχ : χ ∈ atlas ℂ (OnePoint M) := Or.inl ⟨e,chart_mem_atlas ℂ x,rfl⟩
  have hs : H.symm (π z) ∈ χ.source := by
    rw [← hx]
    exact (finiteOnePointChart_coe_source _ _).mpr (mem_chart_source ℂ x)
  obtain ⟨u,hu,hu0,hd,he⟩ := torus_marking_local_coordinate H hH hi χ
    (IsManifold.subset_maximalAtlas hχ) z hs
  have htarget : u z ∈ e.target := hu0.symm ▸ χ.map_source hs
  obtain ⟨hh,hc,hr⟩ := hF e (chart_mem_atlas ℂ x) _ htarget
  obtain ⟨hh',hc',hr'⟩ := harmonic_immersion_reparametrization hh hc hr hu hd
  have hY : (X ∘ π) =ᶠ[𝓝 z] (F ∘ e.symm) ∘ u := by
    filter_upwards [he] with w hw
    change (H.symm (π w)).elim a F = _
    rw [← hw]
    rfl
  have hj (j : Fin 3) : (fun w => X (π w) j) =ᶠ[𝓝 z] (fun w => F (e.symm (u w)) j) :=
    hY.fun_comp (fun A => A j)
  have hD : DifferentiableAt ℝ ((F ∘ e.symm) ∘ u) z :=
    (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hh' j))).differentiableAt
  have hfd := hY.fderiv_eq (𝕜 := ℝ)
  refine ⟨fun j => (harmonicAt_congr_nhds (hj j)).mpr (hh' j),?_,?_⟩
  · change ConformalCoordinateDerivatives (X ∘ π) z
    apply (conformalCoordinateDerivatives_iff_dot (hD.congr_of_eventuallyEq hY)).mpr
    rw [hfd]
    exact (conformalCoordinateDerivatives_iff_dot hD).mp hc'
  · change Function.Injective (fderiv ℝ (X ∘ π) z)
    rw [hfd]
    exact hr'

omit [ChartedSpace ℂ M] [T2Space M] in
/-- The finite torus parametrization has the image and closed-embedding
property of the original surface. -/
theorem marked_immersion_closedEmbedding_range {L : PeriodPair}
    (H : OnePoint M ≃ₜ PeriodTorus L) (h0 : H OnePoint.infty = 0)
    (F : M → Fin 3 → ℝ) (hF : IsClosedEmbedding F) (a : Fin 3 → ℝ) :
    let X := fun q : PeriodTorus L => (H.symm q).elim a F
    IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1) ∧
      range (fun q : PuncturedPeriodTorus L => X q.1) = range F := by
  let f := markedPuncturedUniformization H h0
  let X := fun q : PuncturedPeriodTorus L => (H.symm q.1).elim a F
  have he : X = F ∘ f.symm := by
    funext q
    obtain ⟨x,rfl⟩ := f.surjective q
    change (H.symm (H (x:OnePoint M))).elim a F = F (f.symm (f x))
    rw [H.symm_apply_apply,f.symm_apply_apply]
    rfl
  change IsClosedEmbedding X ∧ range X = range F
  rw [he]
  exact ⟨hF.comp f.symm.isClosedEmbedding,f.symm.surjective.range_comp _⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_harmonic_immersion_coordinates
#print axioms TwoAxisHelicoid.marked_immersion_closedEmbedding_range
