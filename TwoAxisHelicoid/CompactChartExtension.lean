import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

namespace TwoAxisHelicoid
open Complex Set Filter Function
open scoped Topology ContDiff Manifold

noncomputable def compactChartExtend {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) (u : ℂ → ℝ) (x : M) : ℝ := by
  classical
  exact if x ∈ e.source then u (e x) else 0

theorem compactChartExtend_symm {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ) (u : ℂ → ℝ)
    {z : ℂ} (hz : z ∈ e.target) : compactChartExtend e u (e.symm z) = u z := by
  simp [compactChartExtend,e.map_target hz,e.right_inv hz]

/-- Extending a scalar test by zero yields a global function supported
on the image of the common compact integration patch. -/
theorem compactChartExtend_support {M : Type*} [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph M ℂ) {u : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (ht : K ⊆ e.target) (hs : tsupport u ⊆ K) :
    IsCompact (e.symm '' K) ∧ tsupport (compactChartExtend e u) ⊆ e.symm '' K := by
  have hk := hK.image_of_continuousOn (e.symm.continuousOn.mono ht)
  refine ⟨hk,closure_minimal ?_ hk.isClosed⟩
  intro x hx
  have hne : compactChartExtend e u x ≠ 0 := hx
  by_cases he : x ∈ e.source
  · have hu : u (e x) ≠ 0 := by simpa [compactChartExtend,he] using hne
    exact ⟨e x,hs (subset_closure (show e x ∈ support u from hu)),e.left_inv he⟩
  · simp [compactChartExtend,he] at hne

/-- A holomorphic chart of a complex curve is smooth as a real coordinate
map on its actual source, in the same underlying charted space. -/
theorem holomorphic_chart_real_contMDiffAt {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) {x : M} (hx : x ∈ e.source) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ e x := by
  have h := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω) he hx
  obtain ⟨hc,hd⟩ := contMDiffAt_iff.mp h
  refine contMDiffAt_iff.mpr ⟨hc,?_⟩
  simpa only [mfld_simps] using! (hd.restrict_scalars ℝ).of_le (show (∞ : WithTop ℕ∞) ≤ ω by simp)

theorem compactChartExtend_smooth {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    (e : OpenPartialHomeomorph M ℂ) {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u)
    (he : ∀ x ∈ e.source, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ e x)
    {K : Set ℂ} (hK : IsCompact K) (ht : K ⊆ e.target) (hs : tsupport u ⊆ K) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (compactChartExtend e u) := by
  intro x
  by_cases hx : x ∈ e.source
  · apply (hu.contMDiff.contMDiffAt.comp x (he x hx)).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [compactChartExtend,hy]
  · obtain ⟨hk,hsub⟩ := compactChartExtend_support e hK ht hs
    have hn : x ∉ e.symm '' K := by
      rintro ⟨z,hz,rfl⟩
      exact hx (e.map_target (ht hz))
    apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hk.isClosed.isOpen_compl.mem_nhds hn] with y hy
    by_contra! h
    exact hy (hsub (subset_closure h))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compactChartExtend_smooth
