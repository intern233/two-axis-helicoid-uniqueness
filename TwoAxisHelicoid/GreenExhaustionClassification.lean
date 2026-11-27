import TwoAxisHelicoid.DiskGreenModulus
import TwoAxisHelicoid.CompactPlanarRealization
import TwoAxisHelicoid.OneSidedDiskClassification

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

universe u

/-- A cofinal collection of open disks on the given surface, with
one Dirichlet Green function on each disk. No agreement of their
poles, Green functions or topological markings is assumed. -/
def HasGreenDiskNeighborhoods (M : Type u) [TopologicalSpace M] [ChartedSpace ℂ M] : Prop :=
  ∀ K : Set M, IsCompact K → ∃ V : Opens M, K⊆V ∧ Nonempty (ℂ ≃ₜ V) ∧
    ∃ (p : V) (ρ : V → ℝ), IsDiskGreenModulus p ρ

theorem compact_planar_charts_of_green_disks {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (green : HasGreenDiskNeighborhoods M) : HasPlanarCoordinatesOnCompacts M := by
  classical
  intro K ck
  obtain ⟨V,kv,⟨t⟩,p,ρ,hρ⟩ := green K ck
  obtain ⟨f,hf,inj,_,_⟩ := disk_coordinate_from_green_modulus t hρ
  obtain ⟨S,E,_⟩ := biholomorphic_coordinate_range inj (univalent_surface_local_biholomorphism hf inj)
  obtain ⟨e,src,_,hm⟩ := holomorphic_subdomain_coordinate V S ⟨p⟩ E
  refine ⟨V,e,V.isOpen,kv,?_,?_⟩
  · rw [← src]
    exact fun x hx => (contMDiffAt_of_mem_maximalAtlas hm hx).contMDiffWithinAt
  · rw [← src]
    exact e.injOn

/-- The annular conformal classification required by the geometric
argument follows from potential theory only on relatively compact
neighborhoods of compact subsets of a topological plane. -/
theorem annular_uniformization_of_green_disks
    (green : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M],
      Nonempty (M ≃ₜ ℂ) → HasGreenDiskNeighborhoods M) : AnnularRiemannSurfaceUniformization.{u} :=
  annular_uniformization_of_compact_coordinates fun M _ _ _ h => compact_planar_charts_of_green_disks (green M h)

/-- Original theorem 1.1, including embeddedness of the certified
immersion, under the stated disk estimate, planar topology, existence
and Green-disk exhaustion inputs. -/
theorem positional_classification_of_green_disks (schoen : PlanarSchoenfliesTheorem)
    (cm : OneSidedEmbeddedMinimalDiskEstimate)
    (green : ∀ (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M],
      Nonempty (M ≃ₜ ℂ) → HasGreenDiskNeighborhoods M)
    (existence : Nonempty OriginalPositionallyAsymptoticHelicoid) :
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧ IsClosedEmbedding certifiedTorusImmersion :=
  positional_unique_class_of_one_sided_disks schoen cm (annular_uniformization_of_green_disks green) existence

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_classification_of_green_disks
