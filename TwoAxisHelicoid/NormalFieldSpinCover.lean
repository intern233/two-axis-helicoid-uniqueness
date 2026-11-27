import TwoAxisHelicoid.CompactCoreSpatialSpin

namespace TwoAxisHelicoid
open Set Topology

variable {B : Type*} [TopologicalSpace B]

/-- Oriented orthonormal spatial frames in an ambient unit-normal field;
a global tangent reference frame is unnecessary. -/
abbrev NormalFieldFrames (n : B → Fin 3 → ℝ) :=
  {v : B × OrthonormalTangentPair // n v.1 = tangentPairNormal v.2}

/-- The ambient quaternion spin frames over those actual planes. -/
abbrev NormalFieldSpin (n : B → Fin 3 → ℝ) :=
  {v : B × UnitQuaternion // n v.1 = tangentPairNormal (unitQuaternionFrame v.2)}

noncomputable def normalFieldSpinProjection (n : B → Fin 3 → ℝ) (x : NormalFieldSpin n) : NormalFieldFrames n :=
  ⟨(x.1.1,unitQuaternionFrame x.1.2),x.2⟩

theorem normalFieldSpinProjection_isCoveringMap [T2Space B] (n : B → Fin 3 → ℝ) :
    IsCoveringMap (normalFieldSpinProjection n) :=
  (productQuaternionFrame_isCoveringMap B).restrictPreimage
    {v : B × OrthonormalTangentPair | n v.1 = tangentPairNormal v.2}

noncomputable def normalSpinRotation (n : B → Fin 3 → ℝ) (u : Circle) (x : NormalFieldSpin n) : NormalFieldSpin n :=
  ⟨(x.1.1,spinCircleAction u x.1.2),by
    change n x.1.1 = tangentPairNormal (unitQuaternionFrame (spinCircleAction u x.1.2))
    rw [unitQuaternionFrame_spinCircleAction,rotateTangentPair_same_normal]; exact x.2⟩

theorem normalSpinRotation_continuous (n : B → Fin 3 → ℝ) (u : Circle) : Continuous (normalSpinRotation n u) := by
  have h : Continuous (fun x : NormalFieldSpin n => spinCircleAction u x.1.2) :=
    spinCircleAction_continuous.comp (f := fun x : NormalFieldSpin n => (u,x.1.2))
      (continuous_const.prodMk continuous_subtype_val.snd)
  exact (continuous_subtype_val.fst.prodMk h).subtype_mk _

/-- Restriction of the quaternion covering for a compact normal field
to a puncture complement, expressed in its actual oriented tangent planes. -/
noncomputable def normalSpinPunctureIdent (p : B) (n : B → Fin 3 → ℝ)
    (f : {x : B // x ≠ p} → OrthonormalTangentPair) (hn : ∀ x, n x.1 = tangentPairNormal (f x)) :
    SpatialPlaneSpin f ≃ₜ {s : NormalFieldSpin n // s.1.1 ≠ p} where
  toFun := fun s => ⟨⟨(s.1.1.1,s.1.2),(hn s.1.1).trans s.2⟩,s.1.1.2⟩
  invFun := fun x => ⟨(⟨x.1.1.1,x.2⟩,x.1.1.2),(hn ⟨x.1.1.1,x.2⟩).symm.trans x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h := continuous_subtype_val (p := fun v : {b : B // b ≠ p} × UnitQuaternion =>
      tangentPairNormal (f v.1) = tangentPairNormal (unitQuaternionFrame v.2))
    exact ((((continuous_subtype_val.comp h.fst).prodMk h.snd).subtype_mk _).subtype_mk _)
  continuous_invFun := by
    have h := continuous_subtype_val.comp (continuous_subtype_val (p := fun v : NormalFieldSpin n => v.1.1 ≠ p))
    exact ((h.fst.subtype_mk _).prodMk h.snd).subtype_mk _

noncomputable def normalFramesPunctureIdent (p : B) (n : B → Fin 3 → ℝ)
    (f : {x : B // x ≠ p} → OrthonormalTangentPair) (hn : ∀ x, n x.1 = tangentPairNormal (f x)) :
    OrientedPlaneFrames f ≃ₜ {s : NormalFieldFrames n // s.1.1 ≠ p} where
  toFun := fun s => ⟨⟨(s.1.1.1,s.1.2),(hn s.1.1).trans s.2⟩,s.1.1.2⟩
  invFun := fun x => ⟨(⟨x.1.1.1,x.2⟩,x.1.1.2),(hn ⟨x.1.1.1,x.2⟩).symm.trans x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h := continuous_subtype_val (p := fun v : {b : B // b ≠ p} × OrthonormalTangentPair =>
      tangentPairNormal (f v.1) = tangentPairNormal v.2)
    exact ((((continuous_subtype_val.comp h.fst).prodMk h.snd).subtype_mk _).subtype_mk _)
  continuous_invFun := by
    have h := continuous_subtype_val.comp (continuous_subtype_val (p := fun v : NormalFieldFrames n => v.1.1 ≠ p))
    exact ((h.fst.subtype_mk _).prodMk h.snd).subtype_mk _

theorem normalSpinPunctureIdent_projection (p : B) (n : B → Fin 3 → ℝ)
    (f : {x : B // x ≠ p} → OrthonormalTangentPair) (hn : ∀ x, n x.1 = tangentPairNormal (f x))
    (x : SpatialPlaneSpin f) :
    normalFieldSpinProjection n (normalSpinPunctureIdent p n f hn x).1 =
      (normalFramesPunctureIdent p n f hn (spatialPlaneSpinProjection f x)).1 := rfl

/-- Equality of the spin projections in angle coordinates is exactly
commutation over the corresponding spatial orthonormal frame bundles. -/
theorem spatial_spin_transport_square {f g : C(B,OrthonormalTangentPair)}
    (H : SpatialPlaneSpin f ≃ₜ SpatialPlaneSpin g)
    (h : ∀ x, spatialSpinMarkedProjection g (H x) = spatialSpinMarkedProjection f x) (x : SpatialPlaneSpin f) :
    spatialPlaneSpinProjection g (H x) = orientedPlaneFrameHomeomorph g g.continuous
      ((orientedPlaneFrameHomeomorph f f.continuous).symm (spatialPlaneSpinProjection f x)) := by
  exact (orientedPlaneFrameHomeomorph g g.continuous).symm.injective <| (h x).trans
    ((orientedPlaneFrameHomeomorph g g.continuous).symm_apply_apply _).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normalFieldSpinProjection_isCoveringMap
#print axioms TwoAxisHelicoid.normalSpinPunctureIdent_projection
