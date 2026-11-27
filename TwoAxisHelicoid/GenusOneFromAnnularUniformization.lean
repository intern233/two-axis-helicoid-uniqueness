import TwoAxisHelicoid.TorusIntermediateCylinder
import TwoAxisHelicoid.RoundCylinderUniversalModels
import TwoAxisHelicoid.PhysicalAnnulusFilling

namespace TwoAxisHelicoid
open Complex Set Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

/-- Classifying one cyclic covering cylinder suffices for a compact
genus-one Riemann surface. A disk covering is ruled out by the actual
torus deck action; in the plane case the translation lattice and
the quotient biholomorphism are constructed. -/
theorem compact_torus_uniformization_from_an_annulus {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L : PeriodPair} (mark : M ≃ₜ PeriodTorus L) (ann : AnnularRiemannSurfaceUniformization.{0}) :
    AdmitsPeriodTorusUniformization M := by
  let C := {z : ℂ // 0<‖z‖ ∧ ‖z‖<1}
  obtain ⟨a,b,cov,onto,loc,full,allPoints⟩ := topological_torus_intermediate_annulus mark
  let _ := holomorphicCoverAtlas loc
  let _ := holomorphicCoverAtlas_isManifold loc
  have hol := holomorphicCoverAtlas_localDiffeomorph loc
  obtain ⟨T,round,⟨U⟩⟩ := ann C 1 one_pos ⟨Homeomorph.refl _⟩
  have transfer {E : Type} [TopologicalSpace E] [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
      [ChartedSpace ℂ E] (x : E) (p : E → T) (pc : IsCoveringMap p)
      (ph : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p) :
      ∃ f : E → M, IsCoveringMap f ∧ Surjective f ∧ IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f := by
    let q := U.symm ∘ p
    have qc : IsCoveringMap q := pc.homeomorph_comp U.symm.toHomeomorph
    obtain ⟨y,hy⟩ := onto (q x)
    obtain ⟨H,eq⟩ := replace_simply_connected_cover qc cov x y hy.symm
    have same : (b ∘ a) ∘ H=b ∘ q := by rw [Function.comp_assoc,eq]
    refine ⟨b ∘ q,same ▸ full.comp_homeomorph H,same ▸ allPoints.comp H.surjective,?_⟩
    intro w
    have hq := IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := C) (ph w) (U.symm.isLocalDiffeomorph (p w))
    exact IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := M) hq (hol _)
  rcases round_cylinder_holomorphic_universal_cover T round with ⟨p,cover,_,reg⟩|⟨p,cover,_,reg⟩
  · obtain ⟨f,fc,fs,fh⟩ := transfer (0:ℂ) p cover reg
    exact compact_surface_uniformizes_of_holomorphic_plane_cover (holomorphic_plane_cover_of_localDiffeomorph fc fs fh)
  · let o : RiemannUnitDisk := ⟨0,Metric.mem_ball_self one_pos⟩
    let _ : ContractibleSpace RiemannUnitDisk := (convex_ball (0:ℂ) 1).contractibleSpace ⟨o.1,o.2⟩
    let _ : LocallyPathConnectedSpace RiemannUnitDisk := unitDiskOpen.isOpen.locallyPathConnectedSpace
    obtain ⟨f,fc,fs,fh⟩ := transfer o p cover reg
    exact (compact_topological_torus_no_disk_cover mark fc fs fh).elim

universe u

theorem compact_genus_one_uniformization_of_annular_classification (ann : AnnularRiemannSurfaceUniformization.{0})
    (L : PeriodPair) : CompactGenusOneUniformization.{u} L := by
  intro M top sep cpt atlas man marking
  obtain ⟨mark⟩ := marking
  exact compact_torus_uniformization_from_an_annulus mark ann

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_torus_uniformization_from_an_annulus
#print axioms TwoAxisHelicoid.compact_genus_one_uniformization_of_annular_classification
