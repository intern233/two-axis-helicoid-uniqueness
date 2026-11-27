import TwoAxisHelicoid.SpinCircleAction
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

namespace TwoAxisHelicoid
open Set Topology

variable {B : Type*} [TopologicalSpace B] (f : B → OrthonormalTangentPair)

/-- The Euclidean tangent frame at every rotation of a given frame. -/
noncomputable def rotatedFrameFamily (p : B × Circle) : OrthonormalTangentPair :=
  rotateTangentPair p.2 (f p.1)

theorem rotatedFrameFamily_continuous (hf : Continuous f) :
    Continuous (rotatedFrameFamily f) :=
  rotateTangentPair_continuous.comp (continuous_snd.prodMk (hf.comp continuous_fst))

/-- All quaternion lifts over all oriented rotations of the frame
are obtained by acting on the lifts of the chosen frame. -/
noncomputable def rotatedFrameLiftMk (v : QuaternionFramePullback f × Circle) :
    QuaternionFramePullback (rotatedFrameFamily f) :=
  ⟨((v.1.1.1,v.2^2),spinCircleAction v.2 v.1.1.2),by
    change rotateTangentPair _ (f _) = _
    rw [v.1.2,unitQuaternionFrame_spinCircleAction]⟩

set_option maxHeartbeats 900000 in
theorem rotatedFrameLiftMk_continuous : Continuous (rotatedFrameLiftMk f) := by
  change Continuous (fun v : QuaternionFramePullback f × Circle =>
    (⟨((v.1.1.1,v.2^2),spinCircleAction v.2 v.1.1.2),_⟩ : QuaternionFramePullback (rotatedFrameFamily f)))
  apply Continuous.subtype_mk
  have hx : Continuous (fun v : QuaternionFramePullback f × Circle => v.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun v : QuaternionFramePullback f × Circle => v.2) := continuous_snd
  have hq : Continuous (fun v : QuaternionFramePullback f × Circle =>
      spinCircleAction v.2 v.1.1.2) :=
    spinCircleAction_continuous.comp (f := fun v : QuaternionFramePullback f × Circle => (v.2,v.1.1.2)) (hu.prodMk hx.snd)
  exact (hx.fst.prodMk (hu.pow 2)).prodMk hq

omit [TopologicalSpace B] in
theorem rotatedFrameLiftMk_surjective : Function.Surjective (rotatedFrameLiftMk f) := by
  rintro ⟨⟨⟨x,v⟩,q⟩,hq⟩
  obtain ⟨u,rfl⟩ := circle_square_surjective v
  let s := spinCircleAction u⁻¹ q
  have hs : f x = unitQuaternionFrame s := by
    change f x = unitQuaternionFrame (spinCircleAction u⁻¹ q)
    rw [unitQuaternionFrame_spinCircleAction]
    rw [← hq]
    change f x = rotateTangentPair _ (rotateTangentPair _ (f x))
    rw [← rotateTangentPair_mul,inv_pow,inv_mul_cancel,rotateTangentPair_one]
  refine ⟨(⟨(x,s),hs⟩,u),Subtype.ext (Prod.ext rfl ?_)⟩
  change spinCircleAction u (spinCircleAction u⁻¹ q) = q
  rw [← spinCircleAction_mul,mul_inv_cancel,spinCircleAction_one]

theorem spin_product_local_homeomorph {X Y Z W : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    {a : X → Y} {b : Z → W} (ha : IsLocalHomeomorph a) (hb : IsLocalHomeomorph b) :
    IsLocalHomeomorph (Prod.map a b) := by
  intro p
  obtain ⟨e,hx,rfl⟩ := ha p.1
  obtain ⟨d,hy,rfl⟩ := hb p.2
  exact ⟨e.prod d,⟨hx,hy⟩,rfl⟩

theorem rotatedFrameLiftMk_isLocalHomeomorph (hf : Continuous f) :
    IsLocalHomeomorph (rotatedFrameLiftMk f) := by
  have ha := coverPullbackProjection_isLocalHomeomorph hf unitQuaternionFrame_isCoveringMap.isLocalHomeomorph
  have hb := spin_product_local_homeomorph ha circle_square_isCoveringMap.isLocalHomeomorph
  have hg := coverPullbackProjection_isLocalHomeomorph (rotatedFrameFamily_continuous f hf)
    unitQuaternionFrame_isCoveringMap.isLocalHomeomorph
  change IsLocalHomeomorph (coverPullbackProjection (rotatedFrameFamily f) unitQuaternionFrame ∘
    rotatedFrameLiftMk f) at hb
  exact hb.of_comp hg (rotatedFrameLiftMk_continuous f)

theorem rotatedFrameLiftMk_fibers (v w : QuaternionFramePullback f × Circle) :
    rotatedFrameLiftMk f v = rotatedFrameLiftMk f w ↔
      v = w ∨ v = (quaternionFramePullbackDeck f w.1,-w.2) := by
  constructor
  · intro h
    have hx := congrArg (fun q : QuaternionFramePullback (rotatedFrameFamily f) => q.1.1.1) h
    have hu := congrArg (fun q : QuaternionFramePullback (rotatedFrameFamily f) => q.1.1.2) h
    have hq := congrArg (fun q : QuaternionFramePullback (rotatedFrameFamily f) => q.1.2) h
    change v.1.1.1 = w.1.1.1 at hx
    change v.2^2 = w.2^2 at hu
    change spinCircleAction v.2 v.1.1.2 = spinCircleAction w.2 w.1.1.2 at hq
    rcases (circle_square_fibers v.2 w.2).mp hu with he | he
    · left
      rw [he] at hq
      exact Prod.ext (Subtype.ext (Prod.ext hx ((unitQuaternionPhase w.2.normSq_coe).injective hq))) he
    · right
      rw [he,spinCircleAction_neg,← spinCircleAction_antipode] at hq
      have hq' := (unitQuaternionPhase w.2.normSq_coe).injective hq
      have hh := congrArg unitQuaternionAntipode hq'
      rw [unitQuaternionAntipode_involutive] at hh
      exact Prod.ext (Subtype.ext (Prod.ext hx hh)) he
  · rintro (rfl | rfl)
    · rfl
    · apply Subtype.ext
      change ((w.1.1.1,(-w.2)^2),spinCircleAction (-w.2) (unitQuaternionAntipode w.1.1.2)) = _
      rw [spinCircleAction_neg,spinCircleAction_antipode,unitQuaternionAntipode_involutive]
      have hs : (-w.2)^2 = w.2^2 := (circle_square_fibers _ _).mpr (Or.inr rfl)
      rw [hs]
      rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rotatedFrameLiftMk_fibers
