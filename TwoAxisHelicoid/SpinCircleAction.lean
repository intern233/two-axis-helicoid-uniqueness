import TwoAxisHelicoid.CircleSquareCover

namespace TwoAxisHelicoid
open Complex Set Topology

noncomputable def spinCircleAction (u : Circle) (q : UnitQuaternion) : UnitQuaternion :=
  unitQuaternionPhase u.normSq_coe q

theorem spinCircleAction_continuous :
    Continuous (fun p : Circle × UnitQuaternion => spinCircleAction p.1 p.2) := by
  apply unitSpinorQuaternionHomeomorph.continuous.comp
  apply Continuous.subtype_mk
  change Continuous (fun p : Circle × UnitQuaternion =>
    (p.1 : ℂ) • (unitSpinorQuaternionHomeomorph.symm p.2).1)
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp (unitSpinorQuaternionHomeomorph.symm.continuous.comp continuous_snd))

theorem spinCircleAction_one (q : UnitQuaternion) : spinCircleAction 1 q = q := by
  obtain ⟨s,rfl⟩ := unitSpinorQuaternionHomeomorph.surjective q
  rw [spinCircleAction,unitQuaternionPhase_spinor]
  apply congrArg unitSpinorQuaternionHomeomorph
  apply Subtype.ext
  change (1 : ℂ) • s.1 = s.1
  exact one_smul _ _

theorem spinCircleAction_mul (u v : Circle) (q : UnitQuaternion) :
    spinCircleAction (u*v) q = spinCircleAction u (spinCircleAction v q) := by
  obtain ⟨s,rfl⟩ := unitSpinorQuaternionHomeomorph.surjective q
  simp only [spinCircleAction,unitQuaternionPhase_spinor]
  apply congrArg unitSpinorQuaternionHomeomorph
  apply Subtype.ext
  exact mul_smul (u : ℂ) (v : ℂ) s.1

theorem spinCircleAction_neg (u : Circle) (q : UnitQuaternion) :
    spinCircleAction (-u) q = unitQuaternionAntipode (spinCircleAction u q) := by
  obtain ⟨s,rfl⟩ := unitSpinorQuaternionHomeomorph.surjective q
  rw [spinCircleAction,spinCircleAction,unitQuaternionPhase_spinor,unitQuaternionPhase_spinor,
    unitQuaternionAntipode_spinor]
  apply congrArg unitSpinorQuaternionHomeomorph
  apply Subtype.ext
  exact neg_smul (u : ℂ) s.1

theorem spinCircleAction_antipode (u : Circle) (q : UnitQuaternion) :
    spinCircleAction u (unitQuaternionAntipode q) = unitQuaternionAntipode (spinCircleAction u q) :=
  unitQuaternionPhase_antipode u.normSq_coe q

theorem unitQuaternionFrame_surjective : Function.Surjective unitQuaternionFrame :=
  unitNullTangentPairHomeomorph.surjective.comp
    (unitSpinorQuadratic_surjective.comp unitSpinorQuaternionHomeomorph.symm.surjective)

noncomputable def rotateTangentPair (u : Circle) (p : OrthonormalTangentPair) :
    OrthonormalTangentPair := by
  let a := ((u : ℂ).re • p.1.1+(u : ℂ).im • p.1.2,
    -(u : ℂ).im • p.1.1+(u : ℂ).re • p.1.2)
  refine ⟨a,?_⟩
  obtain ⟨v,hv⟩ := circle_square_surjective u
  obtain ⟨q,hq⟩ := unitQuaternionFrame_surjective p
  have he := unitQuaternionPhase_frame_vectors v.normSq_coe q
  have hvC : (v : ℂ)^2 = (u : ℂ) := congrArg (fun z : Circle => (z : ℂ)) hv
  rw [hq,hvC] at he
  change a.1 ⬝ᵥ a.1 = 1 ∧ a.2 ⬝ᵥ a.2 = 1 ∧ a.1 ⬝ᵥ a.2 = 0
  rw [show a = (unitQuaternionFrame (spinCircleAction v q)).1 from he.symm]
  exact (unitQuaternionFrame (spinCircleAction v q)).2

theorem rotateTangentPair_continuous :
    Continuous (fun p : Circle × OrthonormalTangentPair => rotateTangentPair p.1 p.2) := by
  apply Continuous.subtype_mk
  have hu : Continuous (fun p : Circle × OrthonormalTangentPair => (p.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hA := (continuous_subtype_val.comp (continuous_snd (X := Circle) (Y := OrthonormalTangentPair))).fst
  have hB := (continuous_subtype_val.comp (continuous_snd (X := Circle) (Y := OrthonormalTangentPair))).snd
  exact (((Complex.continuous_re.comp hu).smul hA).add ((Complex.continuous_im.comp hu).smul hB)).prodMk
    ((((Complex.continuous_im.comp hu).neg.smul hA).add ((Complex.continuous_re.comp hu).smul hB)))

theorem unitQuaternionFrame_spinCircleAction (u : Circle) (q : UnitQuaternion) :
    unitQuaternionFrame (spinCircleAction u q) = rotateTangentPair (u^2) (unitQuaternionFrame q) :=
  Subtype.ext (unitQuaternionPhase_frame_vectors u.normSq_coe q)

theorem rotateTangentPair_one (p : OrthonormalTangentPair) : rotateTangentPair 1 p = p := by
  obtain ⟨q,rfl⟩ := unitQuaternionFrame_surjective p
  simpa [spinCircleAction_one] using (unitQuaternionFrame_spinCircleAction 1 q).symm

theorem rotateTangentPair_mul (u v : Circle) (p : OrthonormalTangentPair) :
    rotateTangentPair (u*v) p = rotateTangentPair u (rotateTangentPair v p) := by
  obtain ⟨u,rfl⟩ := circle_square_surjective u
  obtain ⟨v,rfl⟩ := circle_square_surjective v
  obtain ⟨q,rfl⟩ := unitQuaternionFrame_surjective p
  rw [← mul_pow,← unitQuaternionFrame_spinCircleAction,← unitQuaternionFrame_spinCircleAction,
    ← unitQuaternionFrame_spinCircleAction,spinCircleAction_mul]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unitQuaternionFrame_spinCircleAction
