import TwoAxisHelicoid.RegularPlanarTurning

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 1000000

theorem planarMeanVelocity_add_period {γ : ℝ → ℂ} {ω : ℂ} (hp : ∀ t, γ (t+1) = γ t+ω) (t h : ℝ) :
    planarMeanVelocity γ (t+1) h = planarMeanVelocity γ t h := by
  have hd (x : ℝ) : deriv γ (x+1) = deriv γ x := by
    have he := congrArg (fun f : ℝ → ℂ => deriv f x) (funext hp)
    simpa only [deriv_comp_add_const,deriv_add_const] using he
  apply intervalIntegral.integral_congr
  intro r _
  change deriv γ (t+1+r*h) = deriv γ (t+r*h)
  rw [show t+1+r*h = t+r*h+1 by ring,hd]

/-- The secants of an embedded essential curve provide an explicit
periodic homotopy through nonzero tangent vectors to its period. -/
theorem essential_torus_velocity_homotopy {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {ω : ℂ} (hω : ω ≠ 0) (hp : ∀ t, γ (t+1) = γ t+ω) (hr : ∀ t, deriv γ t ≠ 0)
    (hi : ∀ t h : ℝ, h ∈ Ioo (0 : ℝ) 1 → γ (t+h) ≠ γ t) :
    ∃ D : C(unitInterval × unitInterval,ℂ), (∀ x, D x ≠ 0) ∧
      (∀ t : unitInterval, D (0,t) = ω) ∧ (∀ t : unitInterval, D (1,t) = deriv γ t.1) ∧
      ∀ s : unitInterval, D (s,1) = D (s,0) := by
  let D := fun x : unitInterval × unitInterval => planarMeanVelocity γ x.2.1 (1-x.1.1)
  have hD : Continuous D := (planarMeanVelocity_continuous hγ).comp
    (f := fun x : unitInterval × unitInterval => (x.2.1,1-x.1.1))
    ((continuous_subtype_val.comp continuous_snd).prodMk (continuous_const.sub
      (continuous_subtype_val.comp continuous_fst)))
  have hD0 (t : unitInterval) : D (0,t) = ω := by
    simpa [D,hp] using planarMeanVelocity_chord hγ t.1 1
  have hD1 (t : unitInterval) : D (1,t) = deriv γ t.1 := by simp [D,planarMeanVelocity_zero]
  have hn (x : unitInterval × unitInterval) : D x ≠ 0 := by
    rcases x with ⟨s,t⟩
    by_cases hzero : s = 0
    · subst s
      rw [hD0]
      exact hω
    by_cases hone : s = 1
    · subst s
      rw [hD1]
      exact hr _
    have hs0 : (s : ℝ) ≠ 0 := fun he => hzero (Subtype.ext he)
    have hs1 : (s : ℝ) ≠ 1 := fun he => hone (Subtype.ext he)
    intro he
    have hc := planarMeanVelocity_chord hγ t.1 (1-s.1)
    change planarMeanVelocity γ t.1 (1-s.1) = 0 at he
    rw [he,smul_zero] at hc
    exact hi t.1 _ ⟨by linarith [lt_of_le_of_ne s.2.2 hs1],
      by linarith [lt_of_le_of_ne s.2.1 hs0.symm]⟩ (sub_eq_zero.mp hc.symm)
  refine ⟨⟨D,hD⟩,hn,hD0,hD1,fun s => ?_⟩
  change planarMeanVelocity γ 1 (1-s.1) = planarMeanVelocity γ 0 (1-s.1)
  simpa only [zero_add] using planarMeanVelocity_add_period hp 0 (1-s.1)

/-- The tangent of a simple essential torus curve has a closed half
angle in its plane lift. The period chord is a nonzero constant, and
the intermediate secants never vanish. -/
theorem essential_torus_tangent_closed_half_angle {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {ω : ℂ} (hω : ω ≠ 0) (hp : ∀ t, γ (t+1) = γ t+ω) (hr : ∀ t, deriv γ t ≠ 0)
    (hi : ∀ t h : ℝ, h ∈ Ioo (0 : ℝ) 1 → γ (t+h) ≠ γ t) :
    ∃ q : C(unitInterval,Circle), (∀ t : unitInterval, q t^2 = unitComplexDirection (deriv γ t.1) (hr _)) ∧
      q 1 = q 0 := by
  obtain ⟨D,hn,hD0,hD1,he⟩ := essential_torus_velocity_homotopy hγ hω hp hr hi
  let H : C(unitInterval × unitInterval,Circle) := ⟨fun x => unitComplexDirection (D x) (hn x),
    unitComplexDirection_continuous D.continuous hn⟩
  have hperiod (s : unitInterval) : H (s,1) = H (s,0) := by
    apply Circle.ext
    change D (s,1)/(‖D (s,1)‖ : ℂ) = D (s,0)/(‖D (s,0)‖ : ℂ)
    rw [he s]
  obtain ⟨v,hv⟩ := circle_square_surjective (unitComplexDirection ω hω)
  change v^2 = unitComplexDirection ω hω at hv
  have hstart (t : unitInterval) : (ContinuousMap.const unitInterval v) t^2 = H (0,t) := by
    change v^2 = H (0,t)
    rw [hv]
    apply Circle.ext
    change ω/(‖ω‖ : ℂ) = D (0,t)/(‖D (0,t)‖ : ℂ)
    rw [hD0]
  obtain ⟨q,hq,hclose⟩ := homotopy_circle_closed_half_lift H hperiod _ hstart rfl
  refine ⟨q,?_,hclose⟩
  intro t
  rw [hq]
  apply Circle.ext
  change D (1,t)/(‖D (1,t)‖ : ℂ) = deriv γ t.1/(‖deriv γ t.1‖ : ℂ)
  rw [hD1]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.essential_torus_tangent_closed_half_angle
