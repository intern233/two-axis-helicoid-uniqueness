import TwoAxisHelicoid.SimplyConnectedPlaneRiemannMap
import TwoAxisHelicoid.ClassicalRiemannUniformizationSpecialization
import TwoAxisHelicoid.PhysicalAnnulusFilling
import TwoAxisHelicoid.OpenSubdomainLocalBiholomorphism

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

universe u

/-- A single global injective holomorphic local coordinate is sufficient;
its range can be an arbitrary open domain in the plane. -/
def PlanarHolomorphicRealization : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M],
    Nonempty (M ≃ₜ ℂ) → ∃ f : M → ℂ, Injective f ∧ IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f

/-- An injective holomorphic local diffeomorphism realizes the given
complex atlas biholomorphically on its actual planar image. -/
theorem biholomorphic_coordinate_range {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {f : M → ℂ} (inj : Injective f) (ld : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) :
    ∃ (S : Opens ℂ) (D : Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M S ω), ∀ x, (D x).1=f x := by
  classical
  let S := ld.image
  let g : M → S := fun x => ⟨f x,mem_range_self x⟩
  have bij : Bijective g := ⟨fun _ _ e => inj (congrArg Subtype.val e),by
    rintro ⟨v,x,rfl⟩
    exact ⟨x,rfl⟩⟩
  let E := Equiv.ofBijective g bij
  have forward : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω E := by
    intro x
    rw [← contMDiffWithinAt_univ]
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U:=S) E univ x).mp (ld x).contMDiffAt.contMDiffWithinAt
  have inverse : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω E.symm := by
    intro y
    obtain ⟨x,rfl⟩ := E.surjective y
    let h := ld x
    have reg : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (h.localInverse ∘ (Subtype.val : S → ℂ)) (E x) :=
      h.contMDiffAt_localInverse.comp (E x) contMDiff_subtype_val.contMDiffAt
    apply reg.congr_of_eventuallyEq
    filter_upwards [(continuous_subtype_val.continuousAt (x:=E x)).eventually
      (h.localInverse_open_source.mem_nhds h.localInverse_mem_source)] with z hz
    apply inj
    exact (congrArg Subtype.val (E.apply_symm_apply z)).trans (h.localInverse_right_inv hz).symm
  exact ⟨S,⟨E,forward,inverse⟩,fun _ => rfl⟩

/-- The analytic classification of every simply connected planar
domain turns one global injective coordinate into the plane-or-disk
dichotomy for an abstract topological-plane surface. -/
theorem plane_uniformization_of_holomorphic_realization (realize : PlanarHolomorphicRealization.{u}) :
    TopologicalPlaneUniformization.{u} := by
  intro M _ _ _ top
  obtain ⟨f,inj,ld⟩ := realize M top
  obtain ⟨S,D,_⟩ := biholomorphic_coordinate_range inj ld
  by_cases entire : (S : Set ℂ)=univ
  · have sur : Surjective (Subtype.val : S → ℂ) := fun z => ⟨⟨z,by change z∈(S : Set ℂ); rw [entire]; exact mem_univ z⟩,rfl⟩
    exact Or.inl ⟨D.trans ((open_complex_subdomain_local_biholomorphism S).diffeomorphOfBijective ⟨Subtype.val_injective,sur⟩)⟩
  · let _ : ContractibleSpace S := (D.toHomeomorph.symm.trans top.some).contractibleSpace
    let p := Classical.arbitrary S
    obtain ⟨H,_⟩ := simply_connected_plane_disk_biholomorphism S (inferInstance : SimplyConnectedSpace S) entire p
    exact Or.inr ⟨D.trans H⟩

theorem annular_uniformization_of_holomorphic_realization (realize : PlanarHolomorphicRealization.{u}) :
    AnnularRiemannSurfaceUniformization.{u} :=
  annular_classification_of_plane_uniformization (plane_uniformization_of_holomorphic_realization realize)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.annular_uniformization_of_holomorphic_realization
