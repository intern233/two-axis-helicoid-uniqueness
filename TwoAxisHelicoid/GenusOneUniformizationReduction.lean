import TwoAxisHelicoid.CompactTorusNoDiskCover
import TwoAxisHelicoid.HolomorphicCoverPullback
import TwoAxisHelicoid.CompactPlaneCoverUniformization

namespace TwoAxisHelicoid
open Complex Set Function Filter Topology
open scoped Manifold ContDiff Topology

universe u

/-- The noncompact simply connected case of classical uniformization,
restricted to Riemann surfaces whose underlying space is the topological
plane. Both alternatives are actual global biholomorphisms. -/
def TopologicalPlaneUniformization : Prop :=
  ∀ (P : Type u) [TopologicalSpace P] [ChartedSpace ℂ P] [IsManifold 𝓘(ℂ,ℂ) ω P],
    Nonempty (P ≃ₜ ℂ) →
      Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) P ℂ ω) ∨
      Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) P RiemannUnitDisk ω)

theorem holomorphic_plane_cover_of_localDiffeomorph {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {p : ℂ → M} (hp : IsCoveringMap p) (hs : Surjective p)
    (hd : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p) : HolomorphicPlaneCover p := by
  refine ⟨hp,hs,?_⟩
  intro x
  obtain ⟨D,hx,hD⟩ := hd x
  let e := D.toOpenPartialHomeomorph.symm
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M :=
    e.mem_maximalAtlas_of_contMDiffOn D.contMDiffOn_invFun D.contMDiffOn_toFun
  refine ⟨e,he,hx,?_⟩
  filter_upwards [D.open_source.mem_nhds hx] with y hy
  exact (hD hy).symm

/-- Topological genus one and the classical plane/disk dichotomy imply
a compact complex torus uniformization. The covering complex structure,
exclusion of the disk, integer lattice, and quotient marking are constructed. -/
theorem compact_genus_one_uniformization_of_plane_dichotomy {M : Type u} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L₀ : PeriodPair} (H : M ≃ₜ PeriodTorus L₀) (uni : TopologicalPlaneUniformization.{u}) :
    AdmitsPeriodTorusUniformization M := by
  let Q := ULift.{u} ℂ
  let E : Q ≃ₜ ℂ := Homeomorph.ulift
  let p : Q → M := H.symm ∘ periodTorusProjection L₀ ∘ E
  have hp : IsCoveringMap p := ((periodTorusProjection_isCoveringMap L₀).comp_homeomorph E).homeomorph_comp H.symm
  have hs : Surjective p := H.symm.surjective.comp ((Quotient.mk_surjective :
    Surjective (periodTorusProjection L₀)).comp E.surjective)
  let _ := holomorphicCoverAtlas hp.isLocalHomeomorph
  have hman : IsManifold 𝓘(ℂ,ℂ) ω Q := holomorphicCoverAtlas_isManifold hp.isLocalHomeomorph
  have hD := holomorphicCoverAtlas_localDiffeomorph hp.isLocalHomeomorph
  rcases uni Q ⟨E⟩ with hplane | hdisk
  · obtain ⟨Φ⟩ := hplane
    apply compact_surface_uniformizes_of_holomorphic_plane_cover
      (p := p ∘ Φ.symm) (holomorphic_plane_cover_of_localDiffeomorph (hp.comp_homeomorph Φ.symm.toHomeomorph)
        (hs.comp Φ.symm.surjective) (fun x => IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := M) (Φ.symm.isLocalDiffeomorph x) (hD (Φ.symm x))))
  · obtain ⟨Φ⟩ := hdisk
    exact (compact_topological_torus_no_disk_cover H (hp.comp_homeomorph Φ.symm.toHomeomorph)
      (hs.comp Φ.symm.surjective) (fun x => IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := M) (Φ.symm.isLocalDiffeomorph x) (hD (Φ.symm x)))).elim

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_genus_one_uniformization_of_plane_dichotomy
