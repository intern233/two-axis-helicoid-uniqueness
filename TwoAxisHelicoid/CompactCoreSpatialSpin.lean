import TwoAxisHelicoid.CompactCoreCoverTransport
import TwoAxisHelicoid.SpatialTangentSpinCover

namespace TwoAxisHelicoid
open Set Topology

variable {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]

/-- Keep the auxiliary coordinate fixed while retracting the first factor. -/
def CoverCoreRetraction.prod (K : Set B) (R : CoverCoreRetraction K) (C : Type*) [TopologicalSpace C] :
    CoverCoreRetraction {z : B × C | z.1 ∈ K} where
  flow := ⟨fun z => (R.flow (z.1,z.2.1),z.2.2),
    (R.flow.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd⟩
  initial b := Prod.ext (R.initial b.1) rfl
  terminal b := R.terminal b.1
  fixed s b hb := Prod.ext (R.fixed s b.1 hb) rfl

/-- The ambient spatial spin cover in the angle coordinates of an
oriented orthonormal reference frame field. -/
noncomputable def spatialSpinMarkedProjection (f : C(B,OrthonormalTangentPair)) :
    SpatialPlaneSpin f → B × Circle :=
  (orientedPlaneFrameHomeomorph f f.continuous).symm ∘ spatialPlaneSpinProjection f

theorem spatialSpinMarkedProjection_isCoveringMap [T2Space B] (f : C(B,OrthonormalTangentPair)) :
    IsCoveringMap (spatialSpinMarkedProjection f) :=
  (spatialPlaneSpinProjection_isCoveringMap f).homeomorph_comp (orientedPlaneFrameHomeomorph f f.continuous).symm

/-- Over an unchanged subset the spinor itself can be left unchanged. -/
noncomputable def spatialSpinCoreMap (K : Set B) (f g : C(B,OrthonormalTangentPair))
    (h : EqOn f g K) :
    {e : SpatialPlaneSpin f // e.1.1 ∈ K} → {e : SpatialPlaneSpin g // e.1.1 ∈ K} :=
  fun e => ⟨⟨e.1.1,by rw [← h e.2]; exact e.1.2⟩,e.2⟩

noncomputable def spatialSpinCoreHomeomorph (K : Set B) (f g : C(B,OrthonormalTangentPair))
    (h : EqOn f g K) :
    {e : SpatialPlaneSpin f // e.1.1 ∈ K} ≃ₜ {e : SpatialPlaneSpin g // e.1.1 ∈ K} where
  toFun := spatialSpinCoreMap K f g h
  invFun := spatialSpinCoreMap K g f h.symm
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem spatialSpinCoreHomeomorph_proj (K : Set B) (f g : C(B,OrthonormalTangentPair))
    (h : EqOn f g K) (e : {e : SpatialPlaneSpin f // e.1.1 ∈ K}) :
    spatialSpinMarkedProjection g (spatialSpinCoreHomeomorph K f g h e).1 = spatialSpinMarkedProjection f e.1 := by
  apply Prod.ext
  · rfl
  apply Circle.ext
  change tangentPairPhase (g e.1.1.1) (unitQuaternionFrame e.1.1.2) =
    tangentPairPhase (f e.1.1.1) (unitQuaternionFrame e.1.1.2)
  rw [h e.2]

/-- On a strong deformation retract, equality of actual reference frames
identifies the full spatial spin structures everywhere. The isomorphism is
uniquely determined by fixing the quaternion on the given retract. -/
theorem spatial_spin_identified_by_core [T2Space B] {K : Set B} (R : CoverCoreRetraction K)
    (f g : C(B,OrthonormalTangentPair)) (h : EqOn f g K) :
    ∃! G : SpatialPlaneSpin f ≃ₜ SpatialPlaneSpin g,
      (∀ e, spatialSpinMarkedProjection g (G e) = spatialSpinMarkedProjection f e) ∧
      ∀ e : {e : SpatialPlaneSpin f // e.1.1 ∈ K},
        G e.1 = (spatialSpinCoreHomeomorph K f g h e).1 :=
  (CoverCoreRetraction.prod K R Circle).cover_isomorphism_extends
    (spatialSpinMarkedProjection_isCoveringMap f) (spatialSpinMarkedProjection_isCoveringMap g)
    (spatialSpinCoreHomeomorph K f g h) (spatialSpinCoreHomeomorph_proj K f g h)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatial_spin_identified_by_core
