import TwoAxisHelicoid.HelicoidGraphSmoothness
import TwoAxisHelicoid.HelicoidGraphDerivative

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology ContDiff

/-- A global graph and any actual local projection inverse agree on an
ordinary open neighborhood in the base. This transfers actual derivatives,
not merely values of abstract graph data. -/
theorem helicoid_graphMap_eventuallyEq_local_inverse {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} {S : Set M} {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    (e : S ≃ₜ B) (he : ∀ q : S, (e q).1 = helicoidBaseCoordinates (X q.1))
    {u : B → ℝ} (hgraph : ∀ b, X (e.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2))
    (b : B) (φ : OpenPartialHomeomorph M (ℝ × ℝ)) (hφ : (e.symm b).1 ∈ φ.source)
    (hmap : EqOn (fun x => helicoidBaseCoordinates (X x)) φ φ.source) :
    helicoidGraphMap (extendOpenScalar u) =ᶠ[𝓝 b.1] (X ∘ φ.symm) := by
  rw [← hB.isOpenEmbedding_subtypeVal.isLocalHomeomorph.map_nhds_eq b]
  change ∀ᶠ a : B in 𝓝 b,
    helicoidGraphMap (extendOpenScalar u) a.1 = X (φ.symm a.1)
  have hY : Continuous (fun a : B => (e.symm a).1) := continuous_subtype_val.comp e.symm.continuous
  filter_upwards [hY.continuousAt.eventually (φ.open_source.mem_nhds hφ)] with a ha
  have hbase : helicoidBaseCoordinates (X (e.symm a).1) = a.1 := by
    rw [← he,e.apply_symm_apply]
  have hφa : φ (e.symm a).1 = a.1 := (hmap ha).symm.trans hbase
  have hbacka : φ.symm a.1 = (e.symm a).1 := by rw [← hφa]; exact φ.left_inv ha
  rw [hbacka,hgraph a]
  simp only [helicoidGraphMap,extendOpenScalar,dite_eq_left a.2]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_graphMap_eventuallyEq_local_inverse
