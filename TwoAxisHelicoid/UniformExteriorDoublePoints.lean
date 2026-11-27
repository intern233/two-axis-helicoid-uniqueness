import TwoAxisHelicoid.CompactHelicoidEndFamily
import TwoAxisHelicoid.CertifiedCompactDoublePoints

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bornology
open scoped Topology

/-- The compact core obtained by cutting off a true exterior chart at radius R. -/
def exteriorChartCore {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ) (R : ℝ) : Set M :=
  (e.source ∩ e ⁻¹' {z : ℂ | R < ‖z‖})ᶜ

theorem isCompact_exteriorChartCore {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ)
    (core : IsCompact e.sourceᶜ) (esc : Tendsto (fun x => ‖e x‖) (cocompact M) atTop) (R : ℝ) :
    IsCompact (exteriorChartCore e R) := by
  have op : IsOpen (e.source ∩ e ⁻¹' {z : ℂ | R < ‖z‖}) := e.continuousOn.isOpen_inter_preimage e.open_source (isOpen_lt continuous_const continuous_norm)
  have source : e.source ∈ cocompact M := by simpa using core.compl_mem_cocompact
  have both := inter_mem source (esc.eventually (eventually_gt_atTop R))
  obtain ⟨K,hK,hsub⟩ := mem_cocompact.mp both
  exact hK.of_isClosed_subset op.isClosed_compl (fun x hx => by
    by_contra h
    exact hx (hsub h))

/-- Uniform end injectivity, uniform escape of points with bounded
spatial position, and continuity on the compact parameter/core product
confine every double point of every member to one compact set of pairs. -/
theorem compact_family_exterior_double_points {T M : Type*} [TopologicalSpace T] [TopologicalSpace M]
    {K : Set T} (hK : IsCompact K) (e : OpenPartialHomeomorph M ℂ) (core : IsCompact e.sourceᶜ)
    (esc : Tendsto (fun x => ‖e x‖) (cocompact M) atTop) (X : T → M → Fin 3 → ℝ)
    (cont : ∀ k ∈ K, ∀ x, ContinuousAt (fun p : T × M => X p.1 p.2) (k,x)) {R₀ R : ℝ} (hr : R₀ < R)
    (inj : ∀ k ∈ K, InjOn (X k ∘ e.symm) {z : ℂ | R ≤ ‖z‖})
    (bounded : ∀ B : ℝ, 0 ≤ B → ∃ D : ℝ, 0 < D ∧ ∀ k ∈ K, ∀ z : ℂ, R₀ < ‖z‖ → ‖X k (e.symm z)‖ ≤ B → ‖z‖ ≤ D) :
    ∃ C : Set M, IsCompact C ∧ ∀ k ∈ K, immersionDoublePoints (X k) ⊆ C ×ˢ C := by
  have hcore := isCompact_exteriorChartCore e core esc
  have hprod := hK.prod (hcore R)
  have cc : ContinuousOn (fun p : T × M => X p.1 p.2) (K ×ˢ exteriorChartCore e R) :=
    fun p hp => (cont p.1 hp.1 _).continuousWithinAt
  obtain ⟨B,hB,bound⟩ := (hprod.image_of_continuousOn cc).isBounded.exists_pos_norm_le
  obtain ⟨D,_,hD⟩ := bounded B hB.le
  let C := exteriorChartCore e (max R D)
  refine ⟨C,hcore _,?_⟩
  intro k hk pair hp
  obtain ⟨x,y⟩ := pair
  obtain ⟨same,neq⟩ := hp
  have get (x : M) (hx : x ∉ exteriorChartCore e R) : x ∈ e.source ∧ R < ‖e x‖ := by
    simpa only [exteriorChartCore,mem_compl_iff,not_not,mem_inter_iff,mem_preimage,mem_ofPred_eq] using hx
  have one : x ∈ exteriorChartCore e R ∨ y ∈ exteriorChartCore e R := by
    by_contra! outside
    obtain ⟨xs,xr⟩ := get x outside.1
    obtain ⟨ys,yr⟩ := get y outside.2
    apply neq
    apply e.injOn xs ys
    apply inj k hk xr.le yr.le
    simpa only [Function.comp_apply,e.left_inv xs,e.left_inv ys] using same
  have hb : ‖X k x‖ ≤ B := by
    rcases one with h | h
    · exact bound _ ⟨(k,x),⟨hk,h⟩,rfl⟩
    · rw [same]
      exact bound _ ⟨(k,y),⟨hk,h⟩,rfl⟩
  have member (p : M) (bnd : ‖X k p‖ ≤ B) : p ∈ C := by
    intro no
    obtain ⟨hs,large⟩ := no
    change max R D < ‖e p‖ at large
    have estimate := hD k hk (e p) (hr.trans ((le_max_left R D).trans_lt large))
      (by rwa [e.left_inv hs])
    exact ((le_max_right R D).trans_lt large).not_ge estimate
  exact ⟨member x hb,member y (same ▸ hb)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_family_exterior_double_points
