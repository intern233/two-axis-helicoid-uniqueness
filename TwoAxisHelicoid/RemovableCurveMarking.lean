import TwoAxisHelicoid.MarkedPuncturedUniformization
import TwoAxisHelicoid.ActualTorusManifoldImmersion
import Mathlib.Analysis.Complex.RemovableSingularity

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold OnePoint

/-- A continuous map between Riemann surfaces which is holomorphic off
one point is holomorphic in the given complex structures at that point. -/
theorem complex_curve_holomorphic_of_continuous_off_point
    {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ,ℂ) ω N]
    {f : M → N} (p : M) (cf : Continuous f) (off : ∀ y≠p, ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f y) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f := by
  intro x
  by_cases eq : x=p
  · subst x
    let d := chartAt ℂ p
    let e := chartAt ℂ (f p)
    let g := e ∘ f ∘ d.symm
    have dp : p∈d.source := mem_chart_source ℂ p
    have ep : f p∈e.source := mem_chart_source ℂ (f p)
    have target := d.map_source dp
    have cd := d.symm.continuousAt target
    have ce : f (d.symm (d p))∈e.source := by rw [d.left_inv dp]; exact ep
    have arg := cf.continuousAt.comp cd
    have cg : ContinuousAt g (d p) := by
      change ContinuousAt ((e : N → ℂ) ∘ (f ∘ (d.symm : ℂ → M))) (d p)
      exact ContinuousAt.comp (f := f ∘ (d.symm : ℂ → M)) (e.continuousAt ce) arg
    have analytic : AnalyticAt ℂ g (d p) := by
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ cg
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (d.open_target.mem_nhds target),
        mem_nhdsWithin_of_mem_nhds (arg.eventually (e.open_source.mem_nhds ce))] with z hn hz hf
      have ne : d.symm z≠p := fun h => hn ((d.right_inv hz).symm.trans (congrArg d h))
      have ds : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (d.symm : ℂ → M) z := contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ p)) hz
      have de : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (e : N → ℂ) (f (d.symm z)) := contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ (f p))) hf
      have reg : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g z := de.comp z ((off _ ne).comp z ds)
      exact (contMDiffAt_iff_contDiffAt.mp reg).differentiableAt (by simp)
    exact contMDiffAt_iff.mpr ⟨cf.continuousAt,analytic.contDiffAt.contDiffWithinAt⟩
  · exact off x eq

/-- A preassigned biholomorphic marking extends to the holomorphic
filling of an actual puncture. The extended homeomorphism and its
inverse are analytic in the specified compact atlases. -/
theorem existing_marking_fills_actual_puncture {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L : PeriodPair} (E : PuncturedComplexEnd M)
    (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (f : M ≃ₜ PuncturedPeriodTorus L)
    (hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) (hi : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm) :
    let _ := compactifiedEndAtlas E
    let H := f.onePointCongr.trans (punctureCompactification (0:PeriodTorus L))
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm := by
  let _ := compactifiedEndAtlas E
  have hm : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := compactifiedEndAtlas_isManifold E hol
  let H := f.onePointCongr.trans (punctureCompactification (0:PeriodTorus L))
  have point (x : M) : H (x:OnePoint M)=(f x).1 := rfl
  have inv (q : PuncturedPeriodTorus L) : H.symm q.1=(f.symm q:OnePoint M) :=
    H.symm_apply_eq.mpr ((point (f.symm q)).trans (congrArg Subtype.val (f.apply_symm_apply q))).symm
  constructor
  · apply complex_curve_holomorphic_of_continuous_off_point OnePoint.infty H.continuous
    intro y hy
    obtain ⟨x,rfl⟩ := OnePoint.ne_infty_iff_exists.mp hy
    have d := (contMDiff_subtype_val (U := puncturedPeriodTorusOpen L)).comp hf
    apply (d.contMDiffAt.comp _ (compactifiedEnd_finite_inverse_contMDiffAt E x x)).congr_of_eventuallyEq
    filter_upwards [OnePoint.isOpenEmbedding_coe.isOpen_range.mem_nhds (mem_range_self x)] with z hz
    obtain ⟨y,rfl⟩ := hz
    rfl
  · apply complex_curve_holomorphic_of_continuous_off_point 0 H.symm.continuous
    intro y hy
    let q : PuncturedPeriodTorus L := ⟨y,hy⟩
    apply (contMDiffAt_subtype_iff (U := puncturedPeriodTorusOpen L) (x := q)).mp
    have finite : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some ∘ f.symm) q :=
      ((compactifiedEnd_inclusion_contMDiff E).comp hi).contMDiffAt
    exact finite.congr_of_eventuallyEq (Eventually.of_forall inv)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complex_curve_holomorphic_of_continuous_off_point
#print axioms TwoAxisHelicoid.existing_marking_fills_actual_puncture
