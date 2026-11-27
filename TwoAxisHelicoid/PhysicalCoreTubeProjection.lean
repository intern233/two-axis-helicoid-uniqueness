import TwoAxisHelicoid.CompactHeightSlabSheets
import TwoAxisHelicoid.OrderedGenusOneCoreMultiplicity
import Mathlib.Topology.LocalAtTarget

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- The part of an embedded surface cut out by an open physical tube
embeds openly in that surface's own parameter domain. The marking
recovers the actual spatial position of every point of the tube. -/
theorem physical_tube_slice_open_marking {B M E : Type*} [TopologicalSpace B]
    [TopologicalSpace M] [TopologicalSpace E] {T : B × ℝ → E} {Y : M → E} {r : ℝ}
    (tube : IsOpenEmbedding (({q : B × ℝ | |q.2|<r}).domRestrict T))
    (embedded : IsEmbedding Y) :
    ∃ j : spatialTubeSlice T (range Y) r → M, IsOpenEmbedding j ∧ ∀ q, Y (j q)=T q.1 := by
  let W := {q : B × ℝ | |q.2|<r}
  let J := W.domRestrict T
  let D := J ⁻¹' range Y
  let h : spatialTubeSlice T (range Y) r ≃ₜ D := {
    toFun := fun q => ⟨⟨q.1,q.2.1⟩,q.2.2⟩
    invFun := fun q => ⟨q.1.1,q.1.2,q.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let F := (range Y).restrictPreimage J
  let j := embedded.toHomeomorph.symm ∘ F ∘ h
  exact ⟨j,embedded.toHomeomorph.symm.isOpenEmbedding.comp ((tube.restrictPreimage _).comp h.isOpenEmbedding),
    fun q => congrArg Subtype.val (embedded.toHomeomorph.apply_symm_apply (F (h q)))⟩

/-- Open partial coordinates and an ordinary local inverse for the
coordinate expression give a local homeomorphism of the actual domains. -/
theorem local_homeomorph_of_surface_chart_germs {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {p : A → B} (cp : Continuous p)
    (germs : ∀ x, ∃ (a : OpenPartialHomeomorph A ℂ) (b : OpenPartialHomeomorph B ℂ)
        (g : OpenPartialHomeomorph ℂ ℂ), x∈a.source ∧ p x∈b.source ∧ a x∈g.source ∧
        (b ∘ p ∘ a.symm) =ᶠ[𝓝 (a x)] g) : IsLocalHomeomorph p := by
  apply IsLocalHomeomorph.mk
  intro x
  obtain ⟨a,b,g,xa,xb,xg,germ⟩ := germs x
  have atx : b (p x)=g (a x) := by simpa only [Function.comp_apply,a.left_inv xa] using germ.self_of_nhds
  let e := (a.trans g).trans b.symm
  have gx : g (a x)∈b.target := (atx ▸ b.map_source xb : g (a x)∈b.target)
  have xe : x∈e.source := ⟨⟨xa,xg⟩,gx⟩
  have near : p =ᶠ[𝓝 x] e := by
    filter_upwards [(a.continuousAt xa).tendsto.eventually germ,a.open_source.mem_nhds xa,
      cp.continuousAt.preimage_mem_nhds (b.open_source.mem_nhds xb)] with y eq ya yb
    change b (p (a.symm (a y)))=g (a y) at eq
    rw [a.left_inv ya] at eq
    change p y=b.symm (g (a y))
    rw [← eq,b.left_inv yb]
  obtain ⟨U,sub,op,xu⟩ := mem_nhds_iff.mp near
  exact ⟨e.restrOpen U op,⟨xe,xu⟩,fun y hy => sub hy.2⟩

/-- A transverse physical slice over a genus-one generating core is
one sheet. Only the true spatial embedding and the two torus
markings are used to exclude separate sheets. -/
theorem physical_genus_one_tube_single_sheet {A L : PeriodPair} (C : TorusGeneratingCoreModel A)
    {B M E : Type*} [TopologicalSpace B] [T2Space B] [TopologicalSpace M] [TopologicalSpace E]
    (base : B ≃ₜ C.carrier) (mark : M ≃ₜ PuncturedPeriodTorus L)
    {T : B × ℝ → E} {Y : M → E} {r : ℝ}
    (tube : IsOpenEmbedding (({q : B × ℝ | |q.2|<r}).domRestrict T)) (embedded : IsEmbedding Y)
    (hit : (spatialTubeSlice T (range Y) r).Nonempty) :
    let p := fun q : spatialTubeSlice T (range Y) r => q.1.1
    IsProperMap p → IsLocalHomeomorph p → IsHomeomorph p := by
  intro p proper loc
  let _ := C.pathConnected
  let _ : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  let _ : PreconnectedSpace B := (base.symm.surjective.connectedSpace base.symm.continuous).toPreconnectedSpace
  let _ := hit.to_subtype
  have onto := proper_local_homeomorph_surjective proper loc
  obtain ⟨j,openj,_⟩ := physical_tube_slice_open_marking tube embedded
  let m := (Subtype.val : PuncturedPeriodTorus L → PeriodTorus L) ∘ mark ∘ j
  have em : IsOpenEmbedding m := isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp
    (mark.isOpenEmbedding.comp openj)
  have one := ordered_normal_cover_of_genus_one_core_is_homeomorphism C m em
    (base.isProperMap.comp proper) (base.isLocalHomeomorph.comp loc) (base.surjective.comp onto)
    (continuous_snd.comp continuous_subtype_val) (fun a b same h => Subtype.ext (Prod.ext (base.injective same) h))
  have eq : base.symm ∘ (base ∘ p)=p := funext (fun q => base.symm_apply_apply (p q))
  exact eq ▸ base.symm.isHomeomorph.comp one

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_tube_slice_open_marking
#print axioms TwoAxisHelicoid.local_homeomorph_of_surface_chart_germs
#print axioms TwoAxisHelicoid.physical_genus_one_tube_single_sheet
