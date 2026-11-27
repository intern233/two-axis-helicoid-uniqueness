import TwoAxisHelicoid.ActualTorusManifoldImmersion
import TwoAxisHelicoid.CompactPunctureHomeomorphism
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- The covering map to the period torus is holomorphic at every plane point. -/
theorem periodTorusProjection_contMDiff (L : PeriodPair) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (periodTorusProjection L) := by
  intro z
  obtain ⟨e,hz,he⟩ := periodTorusProjection_isLocalHomeomorph L z
  have ha : e.symm ∈ atlas ℂ (PeriodTorus L) := he.symm
  have hc := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω)
    (IsManifold.subset_maximalAtlas ha) hz
  rw [he]
  exact hc

/-- All translations of the quotient are actual complex-analytic manifold maps. -/
theorem periodTorus_translation_contMDiff (L : PeriodPair) (b : PeriodTorus L) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun q : PeriodTorus L => q+b) := by
  obtain ⟨v,hv⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) b
  intro q
  let e := chartAt ℂ q
  have he : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e q :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ q))
      (mem_chart_source ℂ q)
  have hadd : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z : ℂ => z+v) (e q) :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_id.add contDiffAt_const)
  have hc := (periodTorusProjection_contMDiff L).contMDiffAt.comp q (hadd.comp q he)
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds (mem_chart_source ℂ q)] with x hx
  change x+b = periodTorusProjection L (e x+v)
  change x+b = (↑(e x): PeriodTorus L)+(↑v:PeriodTorus L)
  rw [← hv]
  exact congrArg (· + periodTorusProjection L v) (by
    change x = periodTorusProjection L (e x)
    rw [← periodTorus_chart_symm_eq_projection L q]
    exact (e.left_inv hx).symm)

/-- A concrete type for the classical, unmarked genus-one uniformization
input. Both directions refer to the specified complex manifold structures. -/
def AdmitsPeriodTorusUniformization (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M] : Prop :=
  ∃ (L : PeriodPair) (H : M ≃ₜ PeriodTorus L),
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm

/-- The point added at an end can always be made the origin of the complex
torus. The change of marking is holomorphic in both directions. -/
theorem compact_uniformization_mark_point {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (hm : AdmitsPeriodTorusUniformization M) (p : M) :
    ∃ (L : PeriodPair) (H : M ≃ₜ PeriodTorus L), H p = 0 ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm := by
  obtain ⟨L,e,he,hie⟩ := hm
  let a := e p
  let T := Homeomorph.addRight (-a)
  refine ⟨L,e.trans T,?_,(periodTorus_translation_contMDiff L (-a)).comp he,?_⟩
  · change e p + -e p = 0
    exact add_neg_cancel _
  · have hT : (T.symm : PeriodTorus L → PeriodTorus L) = fun q => q+a := by
      funext q
      apply T.injective
      rw [T.apply_symm_apply]
      change q = q+a+ -a
      abel
    have hTi : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω T.symm :=
      (periodTorus_translation_contMDiff L a).congr (fun q => congrFun hT q)
    exact hie.comp hTi

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_uniformization_mark_point
