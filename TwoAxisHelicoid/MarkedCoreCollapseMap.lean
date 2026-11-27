import TwoAxisHelicoid.CompactCoreChartPinch

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

/-- A chart disk at the puncture can be chosen disjoint from any prescribed
compact collection of generator curves. -/
theorem chart_disk_away_from_compact {T : Type*} [TopologicalSpace T] [T2Space T]
    (e : OpenPartialHomeomorph T ℂ) {p : T} (hp : p ∈ e.source) {K : Set T} (hK : IsCompact K)
    (hsep : p ∉ K) : ∃ r : ℝ, 0 < r ∧ closedBall (e p) (2*r) ⊆ e.target ∧
      ∀ x ∈ K, x ∉ e.symm '' closedBall (e p) (2*r) := by
  have h : e.symm (e p) ∉ K := by rwa [e.left_inv hp]
  have hn := (e.symm.continuousAt (e.map_source hp)).eventually (hK.isClosed.isOpen_compl.mem_nhds h)
  obtain ⟨R,hR,hB⟩ := Metric.mem_nhds_iff.mp (inter_mem (e.open_target.mem_nhds (e.map_source hp)) hn)
  let r := R/4
  have hsub : closedBall (e p) (2*r) ⊆ ball (e p) R := closedBall_subset_ball (by dsimp [r]; linarith)
  refine ⟨r,by dsimp [r]; positivity,fun z hz => (hB (hsub hz)).1,?_⟩
  rintro x hx ⟨z,hz,rfl⟩
  exact (hB (hsub hz)).2 hx

/-- The open part of the compact torus after removing one small closed
chart disk, before it is transported into the approximating surface. -/
def openChartCore {T : Type*} [TopologicalSpace T] (e : OpenPartialHomeomorph T ℂ) (p : T) (r : ℝ) : Set T :=
  (e.symm '' closedBall (e p) (r/2))ᶜ

/-- An open embedding of a full genus core into an ambient surface gives a
continuous collapse back to the marked reference surface. It acts as the
identity on its outer region and is constant on the other sheets. -/
theorem chart_core_admits_detecting_map {T M : Type*} [TopologicalSpace T] [T2Space T] [CompactSpace T]
    [TopologicalSpace M] [T2Space M] (e : OpenPartialHomeomorph T ℂ) {p : T} (hp : p ∈ e.source)
    {r : ℝ} (hr : 0 < r) (hB : closedBall (e p) (2*r) ⊆ e.target)
    (f : openChartCore e p r → M) (hf : IsOpenEmbedding f) :
    ∃ F : C(M,T), (∀ x : openChartCore e p r, x.1 ∉ e.symm '' ball (e p) (2*r) → F (f x) = x.1) ∧
      ∀ x ∉ range f, F x = p := by
  classical
  let V := e.symm '' ball (e p) r
  let K : Set (openChartCore e p r) := {x | x.1 ∉ V}
  have hV : IsOpen V := e.isOpen_image_symm_of_subset_target isOpen_ball
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : r ≤ 2*r))).trans hB)
  have hinc : e.symm '' closedBall (e p) (r/2) ⊆ V := image_mono (closedBall_subset_ball (half_lt_self hr))
  have hKV : Subtype.val '' K = Vᶜ := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩; exact hx
    · intro hy; exact ⟨⟨y,fun h => hy (hinc h)⟩,hy,rfl⟩
  have hK : IsCompact K := IsEmbedding.subtypeVal.isCompact_iff.mpr (hKV ▸ hV.isClosed_compl.isCompact)
  let P : C(openChartCore e p r,T) := ⟨fun x => chartPinchMap e p r x.1,(chartPinchMap_continuous hr hB).comp continuous_subtype_val⟩
  have hzero (x : openChartCore e p r) (hx : x ∉ K) : P x = p := by
    have hx' : x.1 ∈ V := not_not.mp hx
    exact chartPinchMap_inner hp hr hB ((image_mono ball_subset_closedBall) hx')
  obtain ⟨F,hF,hout⟩ := extend_map_from_open_core hf P p hK hzero
  exact ⟨F,fun x hx => (hF x).trans (chartPinchMap_outer hr hx),fun y hy => hout y (fun h => hy (image_subset_range _ _ h))⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.chart_core_admits_detecting_map
