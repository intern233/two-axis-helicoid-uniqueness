import TwoAxisHelicoid.TangentPhaseMonodromy

namespace TwoAxisHelicoid
open Set

noncomputable def firstHalfParameter (t : unitInterval) : unitInterval :=
  ⟨t.1/2,by constructor <;> linarith [t.2.1,t.2.2]⟩

noncomputable def secondHalfParameter (t : unitInterval) : unitInterval :=
  ⟨t.1/2+1/2,by constructor <;> linarith [t.2.1,t.2.2]⟩

theorem firstHalfParameter_continuous : Continuous firstHalfParameter :=
  (continuous_subtype_val.div_const _).subtype_mk _

theorem secondHalfParameter_continuous : Continuous secondHalfParameter :=
  ((continuous_subtype_val.div_const _).add_const _).subtype_mk _

theorem firstHalfParameter_zero : firstHalfParameter 0 = 0 := Subtype.ext (by norm_num [firstHalfParameter])
theorem secondHalfParameter_one : secondHalfParameter 1 = 1 := Subtype.ext (by norm_num [secondHalfParameter])
theorem halfParameters_meet : secondHalfParameter 0 = firstHalfParameter 1 :=
  Subtype.ext (by norm_num [firstHalfParameter,secondHalfParameter])

/-- A circle map reversing sign after half a turn has antipodal endpoint
monodromy under the square covering. -/
theorem antipodal_half_chord_lift (q : C(unitInterval,Circle))
    (h : ∀ t, q (secondHalfParameter t)^2 = -q (firstHalfParameter t)^2) : q 1 = -q 0 := by
  obtain ⟨u,hu⟩ := circle_square_surjective (-1)
  change u^2 = -1 at hu
  have hs (t) : q (secondHalfParameter t)^2 = (u*q (firstHalfParameter t))^2 := by
    rw [mul_pow,hu,neg_one_mul,h t]
  obtain ⟨v,hv,hv0⟩ : ∃ v : Circle, v^2 = -1 ∧
      q (secondHalfParameter 0) = v*q (firstHalfParameter 0) := by
    rcases (circle_square_fibers _ _).mp (hs 0) with hh | hh
    · exact ⟨u,hu,hh⟩
    · exact ⟨-u,((circle_square_fibers _ _).mpr (Or.inr rfl)).trans hu,hh.trans (neg_mul _ _).symm⟩
  have hsame : (fun t => q (secondHalfParameter t)) = fun t => v*q (firstHalfParameter t) := by
    apply circle_square_isCoveringMap.eq_of_comp_eq (q.continuous.comp secondHalfParameter_continuous)
      (continuous_const.mul (q.continuous.comp firstHalfParameter_continuous)) _ 0 hv0
    funext t
    change q (secondHalfParameter t)^2 = (v*q (firstHalfParameter t))^2
    rw [mul_pow,hv,neg_one_mul,h t]
  have h0 := congrFun hsame 0
  have h1 := congrFun hsame 1
  simp only [firstHalfParameter_zero,halfParameters_meet] at h0
  simp only [secondHalfParameter_one] at h1
  rw [h1,h0,← mul_assoc,← pow_two,hv,neg_one_mul]

theorem homotopy_circle_closed_half_lift (H : C(unitInterval × unitInterval,Circle))
    (hp : ∀ s, H (s,1) = H (s,0)) (q : C(unitInterval,Circle))
    (hq : ∀ t, q t^2 = H (0,t)) (he : q 1 = q 0) :
    ∃ r : C(unitInterval,Circle), (∀ t, r t^2 = H (1,t)) ∧ r 1 = r 0 := by
  let cov := circle_square_isCoveringMap
  let G := cov.liftHomotopy H q (fun t => (hq t).symm)
  have hG (s t : unitInterval) : G (s,t)^2 = H (s,t) :=
    congrFun (cov.liftHomotopy_lifts H q (fun t => (hq t).symm)) (s,t)
  have h0 (t : unitInterval) : G (0,t) = q t := cov.liftHomotopy_zero H q _ t
  have hclose : (fun s => G (s,1)) = fun s => G (s,0) := by
    apply cov.eq_of_comp_eq (G.continuous.comp (continuous_id.prodMk continuous_const))
      (G.continuous.comp (continuous_id.prodMk continuous_const)) _ 0 ((h0 1).trans (he.trans (h0 0).symm))
    exact funext fun s => (hG s 1).trans ((hp s).trans (hG s 0).symm)
  let q₁ : C(unitInterval,Circle) := ⟨fun t => G (1,t),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  exact ⟨q₁,hG 1,congrFun hclose 1⟩

/-- Homotopy of periodic direction maps preserves the obstruction. Only
the terminal direction needs an antipodal half-period. -/
theorem homotopy_to_half_chord_lift_not_closed (H : C(unitInterval × unitInterval,Circle))
    (hp : ∀ s, H (s,1) = H (s,0)) (ha : ∀ t, H (1,secondHalfParameter t) = -H (1,firstHalfParameter t))
    (q : C(unitInterval,Circle)) (hq : ∀ t, q t^2 = H (0,t)) : q 1 ≠ q 0 := by
  intro he
  obtain ⟨r,hr,hc⟩ := homotopy_circle_closed_half_lift H hp q hq he
  have hanti := antipodal_half_chord_lift r (fun t =>
    (hr (secondHalfParameter t)).trans ((ha t).trans (congrArg Neg.neg (hr (firstHalfParameter t))).symm))
  exact Circle.neg_ne_self (r 0) (hanti.symm.trans hc)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.antipodal_half_chord_lift
#print axioms TwoAxisHelicoid.homotopy_to_half_chord_lift_not_closed
