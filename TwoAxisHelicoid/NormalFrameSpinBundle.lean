import TwoAxisHelicoid.TangentPairNormalRotation
import TwoAxisHelicoid.WeierstrassFrameSpinBundle

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped Matrix

theorem tangentPairPhase_continuous :
    Continuous (fun w : OrthonormalTangentPair × OrthonormalTangentPair => tangentPairPhase w.1 w.2) := by
  unfold tangentPairPhase dotProduct
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop

variable {B : Type*} [TopologicalSpace B]

/-- All spatial frames tangent to the same oriented plane at each point. -/
abbrev OrientedPlaneFrames (f : B → OrthonormalTangentPair) :=
  {w : B × OrthonormalTangentPair // tangentPairNormal (f w.1) = tangentPairNormal w.2}

noncomputable def frameAngle (f : B → OrthonormalTangentPair) (w : OrientedPlaneFrames f) :
    Circle :=
  ⟨tangentPairPhase (f w.1.1) w.1.2,by
    obtain ⟨u,hu⟩ := tangentPair_same_normal_rotate (f w.1.1) w.1.2 w.2
    rw [← hu,tangentPairPhase_rotate]
    exact u.2⟩

theorem frameAngle_continuous (f : B → OrthonormalTangentPair) (hf : Continuous f) :
    Continuous (frameAngle f) := by
  apply Continuous.subtype_mk
  exact tangentPairPhase_continuous.comp
    ((hf.comp continuous_subtype_val.fst).prodMk continuous_subtype_val.snd)

omit [TopologicalSpace B] in
theorem frameAngle_rotates (f : B → OrthonormalTangentPair) (w : OrientedPlaneFrames f) :
    rotateTangentPair (frameAngle f w) (f w.1.1) = w.1.2 := by
  obtain ⟨u,hu⟩ := tangentPair_same_normal_rotate (f w.1.1) w.1.2 w.2
  have heu : frameAngle f w = u := by
    apply Circle.ext
    change tangentPairPhase (f w.1.1) w.1.2 = _
    rw [← hu,tangentPairPhase_rotate]
  rw [heu,hu]

/-- The angle parameter gives a homeomorphism onto the entire oriented
orthonormal frame bundle of the spatial tangent planes. -/
noncomputable def orientedPlaneFrameHomeomorph (f : B → OrthonormalTangentPair) (hf : Continuous f) :
    B × Circle ≃ₜ OrientedPlaneFrames f where
  toFun w := ⟨(w.1,rotateTangentPair w.2 (f w.1)),(rotateTangentPair_same_normal _ _).symm⟩
  invFun w := (w.1.1,frameAngle f w)
  left_inv w := by
    refine Prod.ext rfl (Circle.ext ?_)
    exact tangentPairPhase_rotate _ _
  right_inv w := Subtype.ext (Prod.ext rfl (frameAngle_rotates f w))
  continuous_toFun := (continuous_fst.prodMk (rotatedFrameFamily_continuous f hf)).subtype_mk _
  continuous_invFun := continuous_subtype_val.fst.prodMk (frameAngle_continuous f hf)

/-- Restriction of the Euclidean spin-frame double cover to every
oriented tangent frame, with the subspace topology. -/
abbrev SpatialPlaneSpin (f : B → OrthonormalTangentPair) :=
  {w : B × UnitQuaternion // tangentPairNormal (f w.1) = tangentPairNormal (unitQuaternionFrame w.2)}

noncomputable def spatialPlaneSpinProjection (f : B → OrthonormalTangentPair)
    (w : SpatialPlaneSpin f) : OrientedPlaneFrames f :=
  ⟨(w.1.1,unitQuaternionFrame w.1.2),w.2⟩

theorem spatialPlaneSpinProjection_continuous (f : B → OrthonormalTangentPair) :
    Continuous (spatialPlaneSpinProjection f) :=
  (continuous_subtype_val.fst.prodMk
    (unitQuaternionFrame_isCoveringMap.continuous.comp continuous_subtype_val.snd)).subtype_mk _

noncomputable def rotatedFrameToSpatial (f : B → OrthonormalTangentPair)
    (w : QuaternionFramePullback (rotatedFrameFamily f)) : SpatialPlaneSpin f :=
  ⟨(w.1.1.1,w.1.2),by
    change tangentPairNormal (f w.1.1.1) = tangentPairNormal (unitQuaternionFrame w.1.2)
    rw [← w.2]
    exact (rotateTangentPair_same_normal _ _).symm⟩

noncomputable def spatialToRotatedFrame (f : B → OrthonormalTangentPair) (w : SpatialPlaneSpin f) :
    QuaternionFramePullback (rotatedFrameFamily f) :=
  ⟨((w.1.1,frameAngle f (spatialPlaneSpinProjection f w)),w.1.2),
    frameAngle_rotates f (spatialPlaneSpinProjection f w)⟩

noncomputable def rotatedFramePullbackSpatialHomeomorph (f : B → OrthonormalTangentPair)
    (hf : Continuous f) : QuaternionFramePullback (rotatedFrameFamily f) ≃ₜ SpatialPlaneSpin f where
  toFun := rotatedFrameToSpatial f
  invFun := spatialToRotatedFrame f
  left_inv w := by
    apply Subtype.ext
    refine Prod.ext (Prod.ext rfl (Circle.ext ?_)) rfl
    change tangentPairPhase (f w.1.1.1) (unitQuaternionFrame w.1.2) = _
    rw [← w.2]
    exact tangentPairPhase_rotate _ _
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.fst.prodMk continuous_subtype_val.snd).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.fst.prodMk
    ((frameAngle_continuous f hf).comp (spatialPlaneSpinProjection_continuous f))).prodMk
      continuous_subtype_val.snd).subtype_mk _

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.orientedPlaneFrameHomeomorph
#print axioms TwoAxisHelicoid.rotatedFramePullbackSpatialHomeomorph
