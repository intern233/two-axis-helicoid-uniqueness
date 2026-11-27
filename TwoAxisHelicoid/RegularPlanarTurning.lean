import TwoAxisHelicoid.PlanarHalfChord
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace TwoAxisHelicoid
open Set Complex MeasureTheory
set_option maxHeartbeats 1000000

noncomputable def unitComplexDirection (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z/(‖z‖ : ℂ),mem_sphere_zero_iff_norm.mpr (by simp [norm_ne_zero_iff.mpr hz])⟩

theorem unitComplexDirection_continuous {A : Type*} [TopologicalSpace A] {f : A → ℂ}
    (hf : Continuous f) (hn : ∀ a, f a ≠ 0) : Continuous (fun a => unitComplexDirection (f a) (hn a)) :=
  (hf.div (continuous_ofReal.comp hf.norm) (fun x => ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hn x)))).subtype_mk _

noncomputable def planarMeanVelocity (γ : ℝ → ℂ) (t h : ℝ) :=
  ∫ r in (0 : ℝ)..1, deriv γ (t+r*h)

theorem planarMeanVelocity_continuous {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (fun x : ℝ × ℝ => planarMeanVelocity γ x.1 x.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun x : (ℝ × ℝ) × ℝ => deriv γ (x.1.1+x.2*x.1.2))
  exact (hγ.continuous_deriv (by simp)).comp (continuous_fst.fst.add (continuous_snd.mul continuous_fst.snd))

theorem planarMeanVelocity_zero (γ : ℝ → ℂ) (t : ℝ) : planarMeanVelocity γ t 0 = deriv γ t := by
  simp [planarMeanVelocity]

theorem planarMeanVelocity_chord {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (t h : ℝ) :
    h • planarMeanVelocity γ t h = γ (t+h)-γ t := by
  let g := fun r : ℝ => γ (t+r*h)
  have hd (r : ℝ) : HasDerivAt g (h • deriv γ (t+r*h)) r := by
    have hi : HasDerivAt (fun x : ℝ => t+x*h) h r := by
      simpa using ((hasDerivAt_id r).mul_const h).const_add t
    exact (hγ.differentiable (by simp) (t+r*h)).hasDerivAt.scomp r hi
  have hc : Continuous (fun r : ℝ => h • deriv γ (t+r*h)) :=
    ((hγ.continuous_deriv (by simp)).comp (f := fun r : ℝ => t+r*h) (continuous_const.add (continuous_id.mul_const h))).const_smul h
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun r _ => hd r) (hc.intervalIntegrable 0 1)
  simpa [planarMeanVelocity,g] using hh

/-- A regular simple periodic planar curve is embedded on each open
one-period arc. The normalized tangent to such a curve has no closed
lift under the square map, by deforming to its antipodal half-chord. -/
theorem regular_planar_tangent_no_closed_half_angle {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hr : ∀ t, deriv γ t ≠ 0)
    (hi : ∀ t h : ℝ, h ∈ Ioo (0 : ℝ) 1 → γ (t+h) ≠ γ t)
    (q : C(unitInterval,Circle))
    (hq : ∀ t : unitInterval, q t^2 = unitComplexDirection (deriv γ t.1) (hr _)) : q 1 ≠ q 0 := by
  let D := fun x : unitInterval × unitInterval => planarMeanVelocity γ x.2.1 (x.1.1/2)
  have hD : Continuous D := (planarMeanVelocity_continuous hγ).comp
    (f := fun x : unitInterval × unitInterval => (x.2.1,x.1.1/2))
    ((continuous_subtype_val.comp continuous_snd).prodMk ((continuous_subtype_val.comp continuous_fst).div_const _))
  have hn (x : unitInterval × unitInterval) : D x ≠ 0 := by
    by_cases h : x.1.1 = 0
    · simpa only [D,h,zero_div,planarMeanVelocity_zero] using hr x.2.1
    · intro he
      have hc := planarMeanVelocity_chord hγ x.2.1 (x.1.1/2)
      change planarMeanVelocity γ x.2.1 (x.1.1/2) = 0 at he
      rw [he,smul_zero] at hc
      exact hi x.2.1 _ ⟨by linarith [lt_of_le_of_ne x.1.2.1 (Ne.symm h)],by linarith [x.1.2.2]⟩
        (sub_eq_zero.mp hc.symm)
  let H : C(unitInterval × unitInterval,Circle) := ⟨fun x => unitComplexDirection (D x) (hn x),
    unitComplexDirection_continuous hD hn⟩
  have hperiod (t : ℝ) : deriv γ (t+1) = deriv γ t := by
    rw [← deriv_comp_add_const]
    exact congrArg (fun f : ℝ → ℂ => deriv f t) (funext hp)
  have hDper (s : unitInterval) : D (s,1) = D (s,0) := by
    apply intervalIntegral.integral_congr
    intro r _
    change deriv γ (1+r*(s.1/2)) = deriv γ (0+r*(s.1/2))
    rw [add_comm,zero_add,hperiod]
  have hDa (r : unitInterval) : D (1,secondHalfParameter r) = -D (1,firstHalfParameter r) := by
    let t := (r : ℝ)/2
    have h1 := planarMeanVelocity_chord hγ (t+1/2) (1/2)
    have h0 := planarMeanVelocity_chord hγ t (1/2)
    rw [show (t+1/2)+(1/2) = t+1 by ring,hp t] at h1
    change planarMeanVelocity γ (t+1/2) (1/2) = -planarMeanVelocity γ t (1/2)
    rw [Complex.real_smul] at h1 h0
    push_cast at h1 h0
    linear_combination 2*h1+2*h0
  apply homotopy_to_half_chord_lift_not_closed H _ _ q
  · intro t
    apply Circle.ext
    change (q t^2 : Circle).val = D (0,t)/(‖D (0,t)‖ : ℂ)
    rw [hq]
    simp [D,planarMeanVelocity_zero,unitComplexDirection]
  · intro s
    apply Circle.ext
    change D (s,1)/(‖D (s,1)‖ : ℂ) = D (s,0)/(‖D (s,0)‖ : ℂ)
    rw [hDper]
  · intro r
    apply Circle.ext
    change D (1,secondHalfParameter r)/(‖D (1,secondHalfParameter r)‖ : ℂ) =
      -(D (1,firstHalfParameter r)/(‖D (1,firstHalfParameter r)‖ : ℂ))
    rw [hDa,norm_neg,neg_div]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_planar_tangent_no_closed_half_angle
