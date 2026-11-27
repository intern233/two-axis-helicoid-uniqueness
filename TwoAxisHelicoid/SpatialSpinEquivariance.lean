import TwoAxisHelicoid.NormalFieldSpinCover

namespace TwoAxisHelicoid
open Set Topology

variable {B : Type*} [TopologicalSpace B]

noncomputable def spatialSpinRotation (f : C(B,OrthonormalTangentPair)) (u : Circle)
    (x : SpatialPlaneSpin f) : SpatialPlaneSpin f :=
  normalSpinRotation (tangentPairNormal ∘ f) u x

theorem spatialSpinRotation_one (f : C(B,OrthonormalTangentPair)) (x : SpatialPlaneSpin f) :
    spatialSpinRotation f 1 x = x := Subtype.ext (Prod.ext rfl (spinCircleAction_one _))

theorem spatialSpinRotation_at_continuous (f : C(B,OrthonormalTangentPair)) (x : SpatialPlaneSpin f) :
    Continuous (fun u => spatialSpinRotation f u x) := by
  have hc : Continuous (fun u : Circle => spinCircleAction u x.1.2) :=
    spinCircleAction_continuous.comp (f := fun u : Circle => (u,x.1.2)) (continuous_id.prodMk continuous_const)
  exact (continuous_const.prodMk hc).subtype_mk _

theorem spatialSpinRotation_proj (f : C(B,OrthonormalTangentPair)) (u : Circle) (x : SpatialPlaneSpin f) :
    spatialSpinMarkedProjection f (spatialSpinRotation f u x) =
      ((spatialSpinMarkedProjection f x).1,u^2*(spatialSpinMarkedProjection f x).2) := by
  apply Prod.ext
  · rfl
  · apply Circle.ext
    let w := spatialPlaneSpinProjection f x
    let a := frameAngle f w
    have ha : rotateTangentPair a (f x.1.1) = unitQuaternionFrame x.1.2 := frameAngle_rotates f w
    change tangentPairPhase (f x.1.1) (unitQuaternionFrame (spinCircleAction u x.1.2)) = ((u^2*a : Circle) : ℂ)
    rw [unitQuaternionFrame_spinCircleAction,← ha,← rotateTangentPair_mul,tangentPairPhase_rotate]

/-- Every marked morphism between the two concrete ambient quaternion
coverings commutes with every Spin(2) rotation: path-lift uniqueness
on the connected circle forces equivariance. -/
theorem spatial_spin_angle_equivariant [T2Space B] (f g : C(B,OrthonormalTangentPair))
    (H : SpatialPlaneSpin f ≃ₜ SpatialPlaneSpin g)
    (hH : ∀ x, spatialSpinMarkedProjection g (H x) = spatialSpinMarkedProjection f x)
    (u : Circle) (x : SpatialPlaneSpin f) :
    H (spatialSpinRotation f u x) = spatialSpinRotation g u (H x) := by
  have he : (fun a => H (spatialSpinRotation f a x)) = fun a => spatialSpinRotation g a (H x) := by
    refine (spatialSpinMarkedProjection_isCoveringMap g).eq_of_comp_eq
      (H.continuous.comp (spatialSpinRotation_at_continuous f x)) (spatialSpinRotation_at_continuous g (H x)) ?_ 1 ?_
    · funext a
      change spatialSpinMarkedProjection g (H (spatialSpinRotation f a x)) = spatialSpinMarkedProjection g (spatialSpinRotation g a (H x))
      rw [hH,spatialSpinRotation_proj,spatialSpinRotation_proj,hH]
    · simp only [spatialSpinRotation_one]
  exact congrFun he u

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatial_spin_angle_equivariant
