import TwoAxisHelicoid.ChartAvoidingPaths
import TwoAxisHelicoid.GaussMultiplierRigidity

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
set_option maxHeartbeats 800000

namespace HolomorphicCoefficientDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem AvoidingPath.integral_const_mul {A : HolomorphicCoefficientDisks X} {U : Set X}
    {x y : X} (c : A.AvoidingPath U x y) (k : ℂ) (F : X → ℂ → ℂ) :
    c.integral (fun p z => k*F p z) = k*c.integral F := by
  induction c with
  | refl => simp only [integral,mul_zero]
  | step p x y hx hy hU =>
      change (∫ s : ℝ in 0..1,
        (chartAt ℂ p y-chartAt ℂ p x)*(k*F p (chartSegment p x y s))) = _
      simpa only [integral,mul_left_comm] using!
        intervalIntegral.integral_const_mul k
          (fun s : ℝ => (chartAt ℂ p y-chartAt ℂ p x)*F p (chartSegment p x y s))
  | trans c d hc hd => simp only [integral,hc,hd,mul_add]

noncomputable def weightedGaussCoefficient (g : X → ℂ) (dh : X → ℂ → ℂ) (p : X) (z : ℂ) : ℂ :=
  g ((chartAt ℂ p).symm z)*dh p z

noncomputable def inverseGaussCoefficient (g : X → ℂ) (dh : X → ℂ → ℂ) (p : X) (z : ℂ) : ℂ :=
  (g ((chartAt ℂ p).symm z))⁻¹*dh p z

def HorizontalLinePeriodsClose {A : HolomorphicCoefficientDisks X} {U : Set X}
    {x : X} (c : A.AvoidingPath U x x) (g : X → ℂ) (dh : X → ℂ → ℂ) : Prop :=
  (((c.integral (inverseGaussCoefficient g dh)-c.integral (weightedGaussCoefficient g dh))/2).re = 0 ∧
    (I*(c.integral (inverseGaussCoefficient g dh)+c.integral (weightedGaussCoefficient g dh))/2).re = 0)

theorem AvoidingPath.gauss_periods_scale {A : HolomorphicCoefficientDisks X} {U : Set X}
    {x y : X} (c : A.AvoidingPath U x y) {g₁ g₂ : X → ℂ} (dh : X → ℂ → ℂ) {k : ℂ}
    (h : ∀ v ∈ U, g₂ v = k*g₁ v) :
    c.integral (weightedGaussCoefficient g₂ dh) = k*c.integral (weightedGaussCoefficient g₁ dh) ∧
    c.integral (inverseGaussCoefficient g₂ dh) = k⁻¹*c.integral (inverseGaussCoefficient g₁ dh) := by
  constructor
  · rw [← c.integral_const_mul k (weightedGaussCoefficient g₁ dh)]
    apply c.integral_congr
    intro p z _hz hu
    simp only [weightedGaussCoefficient,h _ hu,mul_assoc]
  · rw [← c.integral_const_mul k⁻¹ (inverseGaussCoefficient g₁ dh)]
    apply c.integral_congr
    intro p z _hz hu
    simp only [inverseGaussCoefficient,h _ hu,mul_inv_rev]
    ring

/-- Actual horizontal line integrals exclude a non-unit Gauss multiplier.
The required nonzero horizontal period remains an explicit geometric input. -/
theorem actual_horizontal_closed_multiplier_norm_one {A : HolomorphicCoefficientDisks X} {U : Set X}
    {x : X} (c : A.AvoidingPath U x x) {g₁ g₂ : X → ℂ} (dh : X → ℂ → ℂ) {k : ℂ}
    (hk : k ≠ 0) (h : ∀ v ∈ U, g₂ v = k*g₁ v)
    (hA : c.integral (weightedGaussCoefficient g₁ dh) ≠ 0)
    (hfirst : HorizontalLinePeriodsClose c g₁ dh)
    (hsecond : HorizontalLinePeriodsClose c g₂ dh) : ‖k‖ = 1 := by
  have h₁ := (horizontal_period_closure_iff _ _).mp hfirst
  have h₂ := (horizontal_period_closure_iff _ _).mp hsecond
  obtain ⟨hA₂,hB₂⟩ := c.gauss_periods_scale dh h
  rw [hA₂,hB₂] at h₂
  exact multiplier_norm_one_of_closed_period hA hk h₁ h₂

theorem actual_horizontal_closed_multiplier_phase {A : HolomorphicCoefficientDisks X} {U : Set X}
    {x : X} (c : A.AvoidingPath U x x) {g₁ g₂ : X → ℂ} (dh : X → ℂ → ℂ) {k : ℂ}
    (hk : k ≠ 0) (h : ∀ v ∈ U, g₂ v = k*g₁ v)
    (hA : c.integral (weightedGaussCoefficient g₁ dh) ≠ 0)
    (hfirst : HorizontalLinePeriodsClose c g₁ dh)
    (hsecond : HorizontalLinePeriodsClose c g₂ dh) :
    ∃ θ : ℝ, ∀ v ∈ U, g₂ v = exp ((θ : ℂ)*I)*g₁ v := by
  have hn := actual_horizontal_closed_multiplier_norm_one c dh hk h hA hfirst hsecond
  have he := Complex.norm_mul_exp_arg_mul_I k
  rw [hn,Complex.ofReal_one,one_mul] at he
  exact ⟨Complex.arg k,fun v hv => (h v hv).trans (congrArg (·*g₁ v) he.symm)⟩

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.actual_horizontal_closed_multiplier_norm_one
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.actual_horizontal_closed_multiplier_phase
