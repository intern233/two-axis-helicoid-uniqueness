import TwoAxisHelicoid.OrientedHarmonicNormal
import TwoAxisHelicoid.HarmonicChartJacobiOperator
import TwoAxisHelicoid.ImmersionAtlas
import Mathlib.LinearAlgebra.StdBasis

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology InnerProductSpace Laplacian
open scoped Topology ContDiff Manifold

/-- The seven normal components as actual scalar functions on the
original carrier. -/
noncomputable def geometricSimilarityNormalMap {M : Type*} (X N : M → Fin 3 → ℝ) :
    (Fin 7 → ℝ) →ₗ[ℝ] (M → ℝ) where
  toFun p := similarityNormal X N ![p 0,p 1,p 2] ![p 3,p 4,p 5] (p 6)
  map_add' p q := by
    funext z
    unfold similarityNormal similarityField
    simp [Fin.sum_univ_succ,cross_apply]
    ring
  map_smul' t p := by
    funext z
    unfold similarityNormal similarityField
    simp [Fin.sum_univ_succ,cross_apply]
    ring

/-- The Jacobi equation for the global scalar field is checked in a
genuine local chart. The factor from the induced metric is included in
the operator. -/
theorem harmonic_atlas_similarity_jacobi {M : Type*} [TopologicalSpace M]
    {X N : M → Fin 3 → ℝ} (a b : Fin 3 → ℝ) (d : ℝ) (e : OpenPartialHomeomorph M ℂ)
    (reg : HarmonicImmersionChart X e) (hn : ∀ w ∈ e.target, N (e.symm w)=harmonicChartNormal (X ∘ e.symm) w)
    {z : ℂ} (hz : z ∈ e.target) :
    AnalyticAt ℝ (similarityNormal X N a b d ∘ e.symm) z ∧
      conformalSurfaceJacobi (X ∘ e.symm) (similarityNormal X N a b d ∘ e.symm) z=0 := by
  let Y := X ∘ e.symm
  let n := harmonicChartNormal Y
  let u := similarityNormal Y n a b d
  have germ : similarityNormal X N a b d ∘ e.symm =ᶠ[𝓝 z] u := by
    filter_upwards [e.open_target.mem_nhds hz] with w hw
    change similarityField a b d (Y w) ⬝ᵥ N (e.symm w)=similarityField a b d (Y w) ⬝ᵥ harmonicChartNormal Y w
    rw [hn w hw]
  obtain ⟨h,c,i⟩ := reg z hz
  have hy : AnalyticAt ℝ Y z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (h j)
  have an : AnalyticAt ℝ n z := (harmonicChartNormal_data hy c i).1
  let L := similarityLinear b d
  have field : AnalyticAt ℝ (fun w => a+L (Y w)) z := analyticAt_const.add ((L.analyticAt _).comp hy)
  have hu : AnalyticAt ℝ u z := by
    have hp := (spatialDotBilinear.analyticAt_bilinear (a+L (Y z),n z)).comp₂ field an
    convert hp using 1
    funext w
    change (a+b ⨯₃ Y w+d • Y w) ⬝ᵥ n w=(a+(b ⨯₃ Y w+d • Y w)) ⬝ᵥ n w
    rw [add_assoc]
  refine ⟨hu.congr germ.symm,?_⟩
  have heq := similarity_normal_solves_jacobi (X := Y)
    (Filter.mem_of_superset (e.open_target.mem_nhds hz) reg) a b d
  change conformalSurfaceJacobi Y u z=0 at heq
  unfold conformalSurfaceJacobi at heq ⊢
  rw [(laplacian_congr_nhds germ).self_of_nhds,germ.self_of_nhds]
  exact heq

/-- A smooth scalar function in local regular immersion charts is smooth
also in the original real manifold atlas. Transition smoothness follows
from the two common spatial parametrizations. -/
theorem smooth_of_regular_immersion_chart_germs {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) (old : ∀ p, RegularImmersionChart X (chartAt ℂ p))
    (u : M → ℝ) (smooth : ∀ p, ∃ e : OpenPartialHomeomorph M ℂ, p ∈ e.source ∧ RegularImmersionChart X e ∧
      ContDiffAt ℝ ∞ (u ∘ e.symm) (e p)) : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ u := by
  intro p
  obtain ⟨e,hp,he,hu⟩ := smooth p
  let k := chartAt ℂ p
  have kp : p ∈ k.source := mem_chart_source ℂ p
  let tr := k.symm.trans e
  have st : k p ∈ tr.source := ⟨k.map_source kp,by change k.symm (k p) ∈ e.source; rwa [k.left_inv kp]⟩
  have tt : tr (k p)=e p := congrArg e (k.left_inv kp)
  have comp := (show ContDiffAt ℝ ∞ (u ∘ e.symm) (tr (k p)) from tt.symm ▸ hu).comp (k p)
    (regularImmersionChart_transition (old p) he st)
  have same : u ∘ k.symm =ᶠ[𝓝 (k p)] (u ∘ e.symm) ∘ tr := by
    filter_upwards [tr.open_source.mem_nhds st] with w hw
    exact congrArg u (e.left_inv hw.2).symm
  have ch : ContDiffAt ℝ ∞ (u ∘ k.symm) (k p) := comp.congr_of_eventuallyEq same
  apply contMDiffAt_iff.mpr
  refine ⟨?_,?_⟩
  · apply (hu.continuousAt.comp (f := (e : M → ℂ)) (e.continuousAt hp)).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact congrArg u (e.left_inv hq).symm
  · simpa only [mfld_simps] using! ch.contDiffWithinAt (s := range 𝓘(ℝ,ℂ))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_atlas_similarity_jacobi
#print axioms TwoAxisHelicoid.smooth_of_regular_immersion_chart_germs
