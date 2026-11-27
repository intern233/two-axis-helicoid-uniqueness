import TwoAxisHelicoid.NormalFrameSpinBundle

namespace TwoAxisHelicoid
open Set Topology

theorem productQuaternionFrame_isCoveringMap (B : Type*) [TopologicalSpace B] [T2Space B] :
    IsCoveringMap (Prod.map (id : B → B) unitQuaternionFrame) := by
  let τ := (Homeomorph.refl B).prodCongr unitQuaternionAntipode
  apply free_involution_quotient_isCoveringMap τ
  · exact fun w => Prod.ext rfl (unitQuaternionAntipode_involutive w.2)
  · exact fun w h => unitQuaternionAntipode_ne w.2 (congrArg Prod.snd h)
  · have hp : IsOpenQuotientMap (Prod.map (id : B → B) unitQuaternionFrame) :=
      (IsOpenQuotientMap.id (X := B)).prodMap ⟨unitQuaternionFrame_surjective,
        unitQuaternionFrame_isCoveringMap.continuous,unitQuaternionFrame_isCoveringMap.isOpenMap⟩
    exact hp.isQuotientMap
  · intro v w
    constructor
    · intro he
      have hx : v.1 = w.1 := congrArg (fun w : B × OrthonormalTangentPair => w.1) he
      have hq : unitQuaternionFrame v.2 = unitQuaternionFrame w.2 := congrArg Prod.snd he
      rcases unitQuaternionFrame_fibers.mp hq with hh | hh
      · exact Or.inl (Prod.ext hx (Subtype.ext hh))
      · right
        refine Prod.ext hx (Subtype.ext ?_)
        change v.2.1 = (unitQuaternionAntipode w.2).1
        rw [unitQuaternionAntipode_val,hh]
    · rintro (rfl | rfl)
      · rfl
      · exact Prod.ext rfl (unitQuaternionFrame_antipode _)

/-- Restricting the spatial Spin(3) cover to the oriented tangent frames
gives an actual covering map on the entire tangent frame bundle. -/
theorem spatialPlaneSpinProjection_isCoveringMap
    {B : Type*} [TopologicalSpace B] [T2Space B] (f : B → OrthonormalTangentPair) :
    IsCoveringMap (spatialPlaneSpinProjection f) :=
  (productQuaternionFrame_isCoveringMap B).restrictPreimage
    {w : B × OrthonormalTangentPair | tangentPairNormal (f w.1) = tangentPairNormal w.2}

noncomputable def weierstrassSpatialSpinHomeomorph
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    PuncturedMultiplierSpinBundle (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m) ≃ₜ
      SpatialPlaneSpin (weierstrassTorusFrame ht ha m hC) :=
  (weierstrassFrameSpinHomeomorph ht ha m hC).trans
    (rotatedFramePullbackSpatialHomeomorph _ (weierstrassTorusFrame_continuous ht ha m hC))

theorem weierstrassSpatialSpinHomeomorph_proj
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    (x : PuncturedSignCover (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)) (u : Circle) :
    (spatialPlaneSpinProjection _ (weierstrassSpatialSpinHomeomorph ht ha m hC
      (Quotient.mk _ (x,u)))).1 =
    (puncturedSignCoverProjection _ _ x,
      rotateTangentPair (u^2) (weierstrassTorusFrame ht ha m hC (puncturedSignCoverProjection _ _ x))) := by
  have h := (weierstrassFrameSpinHomeomorph ht ha m hC (Quotient.mk _ (x,u))).2.symm
  rw [weierstrassFrameSpinHomeomorph_over_frames] at h
  exact Prod.ext (weierstrassSpinCoverHomeomorph_base ht ha m hC x) h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.spatialPlaneSpinProjection_isCoveringMap
#print axioms TwoAxisHelicoid.weierstrassSpatialSpinHomeomorph_proj
