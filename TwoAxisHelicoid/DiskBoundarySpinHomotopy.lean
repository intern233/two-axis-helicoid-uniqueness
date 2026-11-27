import TwoAxisHelicoid.PlanarHalfChord

namespace TwoAxisHelicoid
open Set
set_option maxHeartbeats 1000000

/-- A half-period reversal of both tangent vectors has antiperiodic
monodromy under the ambient quaternion covering. -/
theorem antipodal_half_frame_lift (q : C(unitInterval,UnitQuaternion))
    (h : ∀ t, unitQuaternionFrame (q (secondHalfParameter t)) =
      rotateTangentPair (-1) (unitQuaternionFrame (q (firstHalfParameter t)))) :
    q 1 = unitQuaternionAntipode (q 0) := by
  obtain ⟨u,hu⟩ := circle_square_surjective (-1)
  change u^2 = -1 at hu
  have he (t : unitInterval) : unitQuaternionFrame (q (secondHalfParameter t)) =
      unitQuaternionFrame (spinCircleAction u (q (firstHalfParameter t))) := by
    rw [unitQuaternionFrame_spinCircleAction,hu,h t]
  obtain ⟨v,hv,hv0⟩ : ∃ v : Circle, v^2 = -1 ∧
      q (secondHalfParameter 0) = spinCircleAction v (q (firstHalfParameter 0)) := by
    rcases (quaternion_frame_fibers_deck _ _).mp (he 0) with hp | hp
    · exact ⟨u,hu,hp⟩
    · exact ⟨-u,((circle_square_fibers _ _).mpr (Or.inr rfl)).trans hu,
        hp.trans (spinCircleAction_neg _ _).symm⟩
  have heq : (fun t => q (secondHalfParameter t)) = fun t => spinCircleAction v (q (firstHalfParameter t)) := by
    apply unitQuaternionFrame_isCoveringMap.eq_of_comp_eq (q.continuous.comp secondHalfParameter_continuous)
      (spinCircleAction_continuous.comp (f := fun t => (v,q (firstHalfParameter t)))
        (continuous_const.prodMk (q.continuous.comp firstHalfParameter_continuous))) _ 0 hv0
    funext t
    change unitQuaternionFrame (q (secondHalfParameter t)) = unitQuaternionFrame (spinCircleAction v (q (firstHalfParameter t)))
    rw [unitQuaternionFrame_spinCircleAction,hv,h t]
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  simp only [firstHalfParameter_zero,halfParameters_meet] at h0
  simp only [secondHalfParameter_one] at h1
  rw [h1,h0,← spinCircleAction_mul,← pow_two,hv,spinCircleAction_neg,spinCircleAction_one]

/-- A free homotopy of closed Euclidean frame curves preserves the
existence of a closed quaternion lift. -/
theorem quaternion_loop_closed_lift_homotopy (H : C(unitInterval × unitInterval,OrthonormalTangentPair))
    (hp : ∀ s, H (s,1) = H (s,0)) (q : C(unitInterval,UnitQuaternion))
    (hq : ∀ t, unitQuaternionFrame (q t) = H (0,t)) (hc : q 1 = q 0) :
    ∃ r : C(unitInterval,UnitQuaternion), (∀ t, unitQuaternionFrame (r t) = H (1,t)) ∧ r 1 = r 0 := by
  let cov := unitQuaternionFrame_isCoveringMap
  let G := cov.liftHomotopy H q (fun t => (hq t).symm)
  have hG (s t : unitInterval) : unitQuaternionFrame (G (s,t)) = H (s,t) :=
    congrFun (cov.liftHomotopy_lifts H q (fun t => (hq t).symm)) (s,t)
  have h0 (t : unitInterval) : G (0,t) = q t := cov.liftHomotopy_zero H q _ t
  have he : (fun s => G (s,1)) = fun s => G (s,0) := by
    apply cov.eq_of_comp_eq (G.continuous.comp (continuous_id.prodMk continuous_const))
      (G.continuous.comp (continuous_id.prodMk continuous_const)) _ 0 ((h0 1).trans (hc.trans (h0 0).symm))
    exact funext fun s => (hG s 1).trans ((hp s).trans (hG s 0).symm)
  let r : C(unitInterval,UnitQuaternion) := ⟨fun t => G (1,t),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  exact ⟨r,hG 1,congrFun he 1⟩

/-- A homotopy from a frame curve to a half-period reversing frame
curve obstructs a closed ambient spin lift. -/
theorem quaternion_homotopic_reversed_frame_not_closed (H : C(unitInterval × unitInterval,OrthonormalTangentPair))
    (hp : ∀ s, H (s,1) = H (s,0))
    (ha : ∀ t, H (1,secondHalfParameter t) = rotateTangentPair (-1) (H (1,firstHalfParameter t)))
    (q : C(unitInterval,UnitQuaternion)) (hq : ∀ t, unitQuaternionFrame (q t) = H (0,t)) : q 1 ≠ q 0 := by
  intro hc
  obtain ⟨r,hr,he⟩ := quaternion_loop_closed_lift_homotopy H hp q hq hc
  have hn := antipodal_half_frame_lift r (fun t => (hr _).trans ((ha t).trans (congrArg _ (hr _)).symm))
  exact unitQuaternionAntipode_ne _ (hn.symm.trans he)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quaternion_homotopic_reversed_frame_not_closed
