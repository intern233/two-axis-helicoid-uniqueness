import TwoAxisHelicoid.ChartRegularConnected
import TwoAxisHelicoid.LogDerivativePathPeriods
import TwoAxisHelicoid.GaussMultiplierRigidity

namespace TwoAxisHelicoid
open Complex Set Metric
set_option maxHeartbeats 1000000

namespace HolomorphicCoefficientDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem gauss_quotient_eq_on_disk {A : HolomorphicCoefficientDisks X} {P : Set X}
    (hP : P.Finite) {g₁ g₂ : X → ℂ}
    (hg₁ : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      AnalyticAt ℂ (fun w : ℂ => g₁ ((chartAt ℂ p).symm w)) z)
    (hg₂ : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      AnalyticAt ℂ (fun w : ℂ => g₂ ((chartAt ℂ p).symm w)) z)
    (hn₁ : ∀ x ∉ P, g₁ x ≠ 0) (hn₂ : ∀ x ∉ P, g₂ x ≠ 0)
    (hlog : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      chartLogDerivative g₂ p z = chartLogDerivative g₁ p z)
    (p : X) {x y : X} (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p)
    (hxP : x ∉ P) (hyP : y ∉ P) : g₂ y/g₁ y = g₂ x/g₁ x := by
  let Ω := ball (chartAt ℂ p p) (A.radius p) \ chartPoles P p
  have hxΩ : (chartAt ℂ p x) ∈ Ω := by
    refine ⟨hx.2,(A.chart_regular_iff P p hx.2).mp ?_⟩
    simpa only [(chartAt ℂ p).left_inv hx.1] using! hxP
  have hyΩ : (chartAt ℂ p y) ∈ Ω := by
    refine ⟨hy.2,(A.chart_regular_iff P p hy.2).mp ?_⟩
    simpa only [(chartAt ℂ p).left_inv hy.1] using! hyP
  have hr z (hz : z ∈ Ω) := (A.chart_regular_iff P p hz.1).mpr hz.2
  have ho : IsOpen Ω := isOpen_ball.sdiff (chartPoles_finite hP p).isClosed
  have hc : IsConnected Ω := ⟨⟨chartAt ℂ p x,hxΩ⟩,
    complex_ball_diff_finite_isPreconnected _ (A.radius_pos p) (chartPoles_finite hP p)⟩
  obtain ⟨c,_hc,he⟩ := equal_logarithmic_derivatives_constant_ratio ho hc
    (fun z hz => (hg₁ p z hz.1 (hr z hz)).differentiableAt)
    (fun z hz => (hg₂ p z hz.1 (hr z hz)).differentiableAt)
    (fun z hz => hn₁ _ (hr z hz)) (fun z hz => hn₂ _ (hr z hz))
    (fun z hz => hlog p z hz.1 (hr z hz))
  have hex : g₂ x = c*g₁ x := by
    simpa only [(chartAt ℂ p).left_inv hx.1] using! he _ hxΩ
  have hey : g₂ y = c*g₁ y := by
    simpa only [(chartAt ℂ p).left_inv hy.1] using! he _ hyΩ
  rw [hex,hey,mul_div_cancel_right₀ _ (hn₁ _ hyP),mul_div_cancel_right₀ _ (hn₁ _ hxP)]

theorem regular_chain_gauss_quotient_eq {A : HolomorphicCoefficientDisks X} {P : Set X}
    (hP : P.Finite) {g₁ g₂ : X → ℂ}
    (hg₁ : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      AnalyticAt ℂ (fun w : ℂ => g₁ ((chartAt ℂ p).symm w)) z)
    (hg₂ : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      AnalyticAt ℂ (fun w : ℂ => g₂ ((chartAt ℂ p).symm w)) z)
    (hn₁ : ∀ x ∉ P, g₁ x ≠ 0) (hn₂ : ∀ x ∉ P, g₂ x ≠ 0)
    (hlog : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      chartLogDerivative g₂ p z = chartLogDerivative g₁ p z)
    {x y : X} {r : ℝ} (c : A.primitives.RegularChain Pᶜ x y r) : g₂ y/g₁ y = g₂ x/g₁ x := by
  induction c with
  | refl => rfl
  | step p x y hx hy hxP hyP => exact gauss_quotient_eq_on_disk hP hg₁ hg₂ hn₁ hn₂ hlog p hx hy hxP hyP
  | trans c d hc hd => exact hd.trans hc

/-- Equality of actual logarithmic differentials on a connected complex
curve minus finitely many points forces one global nonzero multiplier. -/
theorem gauss_maps_proportional_of_log_derivative_eq [PreconnectedSpace X] [Nonempty X]
    (A : HolomorphicCoefficientDisks X) {P : Set X} (hP : P.Finite) {g₁ g₂ : X → ℂ}
    (hg₁ : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      AnalyticAt ℂ (fun w : ℂ => g₁ ((chartAt ℂ p).symm w)) z)
    (hg₂ : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      AnalyticAt ℂ (fun w : ℂ => g₂ ((chartAt ℂ p).symm w)) z)
    (hn₁ : ∀ x ∉ P, g₁ x ≠ 0) (hn₂ : ∀ x ∉ P, g₂ x ≠ 0)
    (hlog : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      chartLogDerivative g₂ p z = chartLogDerivative g₁ p z) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ x ∉ P, g₂ x = c*g₁ x := by
  obtain ⟨b,hb⟩ := (finite_compl_dense_complex_charts hP).nonempty
  refine ⟨g₂ b/g₁ b,div_ne_zero (hn₂ b hb) (hn₁ b hb),?_⟩
  intro x hx
  obtain ⟨r,hr⟩ := A.primitives.exists_chain b x
  obtain ⟨V,W,_hV,_hW,hbV,hxW,h⟩ := hr.regular_approximation
    (finite_compl_dense_complex_charts hP) 1 (by norm_num)
  obtain ⟨s,hs,_he⟩ := h b hbV x hxW hb hx
  exact (div_eq_iff (hn₁ x hx)).mp (regular_chain_gauss_quotient_eq hP hg₁ hg₂ hn₁ hn₂ hlog hs)

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.gauss_maps_proportional_of_log_derivative_eq
