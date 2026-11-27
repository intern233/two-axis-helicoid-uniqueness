import TwoAxisHelicoid.OrientedMinimalHarmonicAtlas
import TwoAxisHelicoid.TangentPlaneGramMembership
import TwoAxisHelicoid.HarmonicChartUnitNormal

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology InnerProductSpace
open scoped Topology ContDiff Manifold

variable {M : Type*} [TopologicalSpace M]

/-- The Euclidean unit normals obtained from two oriented harmonic immersion
charts agree on their overlap. The positive scale is computed from the
actual transition derivative and the common transverse field. -/
theorem oriented_harmonic_normals_agree {X V : M → Fin 3 → ℝ} {e d : OpenPartialHomeomorph M ℂ}
    (oe : OrientedIsothermalChart X V e) (od : OrientedIsothermalChart X V d)
    (he : HarmonicImmersionChart X e) (hd : HarmonicImmersionChart X d)
    {p : M} (ep : p ∈ e.source) (dp : p ∈ d.source) :
    harmonicChartNormal (X ∘ e.symm) (e p)=harmonicChartNormal (X ∘ d.symm) (d p) := by
  let k := e.symm.trans d
  let z := e p
  have src : z ∈ k.source := ⟨e.map_source ep,by change e.symm (e p) ∈ d.source; rwa [e.left_inv ep]⟩
  have kz : k z=d p := congrArg d (e.left_inv ep)
  have germ : (X ∘ e.symm) =ᶠ[𝓝 z] (X ∘ d.symm) ∘ k := by
    filter_upwards [k.open_source.mem_nhds src] with w hw
    exact congrArg X (d.left_inv hw.2).symm
  have dd := (od.1 _ (d.map_source dp)).1.differentiableAt (by simp)
  have dk := (regularImmersionChart_transition oe.1 od.1 src).differentiableAt (by simp)
  have cross := surfaceTangentCross_coordinate_change germ (kz.symm ▸ dd) dk
  rw [kz] at cross
  have pe := (oe.2 _ (e.map_source ep)).2
  have pd := (od.2 _ (d.map_source dp)).2
  rw [e.left_inv ep,cross,smul_dotProduct,smul_eq_mul] at pe
  rw [d.left_inv dp] at pd
  have pos := pos_of_mul_pos_left pe pd.le
  have canonical {q : OpenPartialHomeomorph M ℂ} (hq : HarmonicImmersionChart X q) (sp : p ∈ q.source) :
      harmonicChartNormal (X ∘ q.symm) (q p)=spatialUnitVector (surfaceTangentCross (X ∘ q.symm) (q p)) := by
    obtain ⟨h,c,i⟩ := hq _ (q.map_source sp)
    exact (harmonicChartNormal_data (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (h j)) c i).2.2.2.2.1
  rw [canonical he ep,canonical hd dp,cross,spatialUnitVector_pos_smul pos]

/-- A normal field on the original carrier, with the actual Euclidean unit
normal formula in every chart of its oriented harmonic atlas. -/
theorem oriented_harmonic_atlas_unit_normal [ChartedSpace ℂ M] {X V : M → Fin 3 → ℝ}
    (charts : ∀ e ∈ atlas ℂ M, OrientedIsothermalChart X V e ∧ HarmonicImmersionChart X e) :
    ∃ N : M → Fin 3 → ℝ, (∀ e ∈ atlas ℂ M, ∀ z ∈ e.target, N (e.symm z)=harmonicChartNormal (X ∘ e.symm) z) ∧
      (∀ p, N p ⬝ᵥ N p=1) ∧ Continuous N := by
  let N := fun p : M => harmonicChartNormal (X ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
  have formula (e : OpenPartialHomeomorph M ℂ) (he : e ∈ atlas ℂ M) (z : ℂ) (hz : z ∈ e.target) :
      N (e.symm z)=harmonicChartNormal (X ∘ e.symm) z := by
    let p := e.symm z
    have h := charts (chartAt ℂ p) (chart_mem_atlas ℂ p)
    exact (oriented_harmonic_normals_agree h.1 (charts e he).1 h.2 (charts e he).2
      (mem_chart_source ℂ p) (e.map_target hz)).trans (congrArg _ (e.right_inv hz))
  refine ⟨N,formula,?_,continuous_iff_continuousAt.mpr ?_⟩
  · intro p
    let e := chartAt ℂ p
    have reg := (charts e (chart_mem_atlas ℂ p)).2 _ (e.map_source (mem_chart_source ℂ p))
    exact (harmonicChartNormal_data (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (reg.1 j)) reg.2.1 reg.2.2).2.2.2.2.2.1
  · intro p
    let e := chartAt ℂ p
    have ep : p ∈ e.source := mem_chart_source ℂ p
    have reg := (charts e (chart_mem_atlas ℂ p)).2 _ (e.map_source ep)
    have an := (harmonicChartNormal_data (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (reg.1 j)) reg.2.1 reg.2.2).1
    apply (an.continuousAt.comp (f := (e : M → ℂ)) (e.continuousAt ep)).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds ep] with q hq
    exact (congrArg N (e.left_inv hq)).symm.trans (formula e (chart_mem_atlas ℂ p) (e q) (e.map_source hq))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.oriented_harmonic_atlas_unit_normal
