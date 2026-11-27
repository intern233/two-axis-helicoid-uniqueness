import TwoAxisHelicoid.HelicoidExteriorGraph

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

noncomputable def extendOpenScalar {B : Set (ℝ × ℝ)} (u : B → ℝ) : (ℝ × ℝ) → ℝ := by
  classical
  exact fun x => if h : x ∈ B then u ⟨x,h⟩ else 0

/-- The global graph inverse agrees locally with the actual smooth
spatial inverse of the normal projection. -/
theorem helicoid_graph_height_has_smooth_germs {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} {S : Set M} {B : Set (ℝ × ℝ)}
    (e : S ≃ₜ B) (he : ∀ q : S, (e q).1 = helicoidBaseCoordinates (X q.1))
    {u : B → ℝ} (hu : ∀ b, u b = helicoidSignedDistance (X (e.symm b).1))
    (hTube : ∀ q : S, X q.1 ∈ helicoidTubeEquiv.target)
    (hlocal : ∀ q : S, ∃ φ : OpenPartialHomeomorph M (ℝ × ℝ), q.1 ∈ φ.source ∧
      EqOn (fun x => helicoidBaseCoordinates (X x)) φ φ.source ∧
      ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ φ.symm) (e q).1) :
    ∀ b : B, ∃ v : (ℝ × ℝ) → ℝ, ContDiffAt ℝ (∞ : WithTop ℕ∞) v b.1 ∧
      (fun a : B => u a) =ᶠ[𝓝 b] (fun a => v a.1) := by
  intro b
  obtain ⟨φ,hφ,hmap,hXs⟩ := hlocal (e.symm b)
  have hbase (a : B) : helicoidBaseCoordinates (X (e.symm a).1) = a.1 := by
    rw [← he,e.apply_symm_apply]
  have hval : φ (e.symm b).1 = b.1 := (hmap hφ).symm.trans (hbase b)
  have hback : φ.symm b.1 = (e.symm b).1 := by rw [← hval]; exact φ.left_inv hφ
  have htarget : (X ∘ φ.symm) b.1 ∈ helicoidTubeEquiv.target := by
    simpa only [Function.comp_apply,hback] using hTube (e.symm b)
  rw [e.apply_symm_apply] at hXs
  let v := helicoidSignedDistance ∘ X ∘ φ.symm
  have hv : ContDiffAt ℝ (∞ : WithTop ℕ∞) v b.1 :=
    (helicoidSignedDistance_contDiffAt htarget).comp b.1 hXs
  refine ⟨v,hv,?_⟩
  have hY : Continuous (fun a : B => (e.symm a).1) := continuous_subtype_val.comp e.symm.continuous
  filter_upwards [hY.continuousAt.eventually (φ.open_source.mem_nhds hφ)] with a ha
  have hφa : φ (e.symm a).1 = a.1 := (hmap ha).symm.trans (hbase a)
  have hbacka : φ.symm a.1 = (e.symm a).1 := by rw [← hφa]; exact φ.left_inv ha
  simp only [v,Function.comp_apply,hbacka,hu]

theorem contDiffOn_extendOpenScalar_of_smooth_germs {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    {u : B → ℝ}
    (hgerm : ∀ b : B, ∃ v : (ℝ × ℝ) → ℝ, ContDiffAt ℝ (∞ : WithTop ℕ∞) v b.1 ∧
      (fun a : B => u a) =ᶠ[𝓝 b] (fun a => v a.1)) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) B := by
  intro x hx
  let b : B := ⟨x,hx⟩
  obtain ⟨v,hv,he⟩ := hgerm b
  have heq : extendOpenScalar u =ᶠ[𝓝 x] v := by
    rw [← hB.isOpenEmbedding_subtypeVal.isLocalHomeomorph.map_nhds_eq b]
    change ∀ᶠ a : B in 𝓝 b, extendOpenScalar u a.1 = v a.1
    filter_upwards [he] with a ha
    simpa only [extendOpenScalar,dite_eq_left a.2] using ha
  exact (hv.congr_of_eventuallyEq heq).contDiffWithinAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_graph_height_has_smooth_germs
#print axioms TwoAxisHelicoid.contDiffOn_extendOpenScalar_of_smooth_germs
