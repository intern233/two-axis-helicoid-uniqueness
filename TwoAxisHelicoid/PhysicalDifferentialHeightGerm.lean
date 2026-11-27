import TwoAxisHelicoid.DifferentialHelicoidHeightGerm

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology
open scoped Topology

/-- A physical height with the given complex coefficient differs from
the real part of any holomorphic height primitive by one real constant
on the actual punctured neighborhood. -/
theorem punctured_height_equals_real_primitive {x : ℂ → ℝ} {h H : ℂ → ℂ}
    (reg : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ x w ∧ scalarComplexCoefficient x w=h w ∧ HasDerivAt H (h w) w) :
    ∃ b : ℝ, ∀ᶠ w in 𝓝[≠] (0:ℂ), x w=b+(H w).re := by
  obtain ⟨r,rp,sub⟩ := Metric.mem_nhdsWithin_iff.mp reg
  let U := ball (0:ℂ) r \ {0}
  have op : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have co : IsPreconnected U := complex_ball_diff_finite_isPreconnected 0 rp (finite_singleton 0)
  have hx (w : ℂ) (hw : w∈U) : HasFDerivAt x (realCoefficientDerivative (h w)) w := by
    rw [← (sub hw).2.1]
    exact scalarComplexCoefficient_hasFDerivAt (sub hw).1
  have dh (w : ℂ) (hw : w∈U) : HasFDerivAt (fun v => (H v).re) (realCoefficientDerivative (h w)) w :=
    reCLM.hasFDerivAt.comp w ((sub hw).2.2.hasFDerivAt.restrictScalars ℝ)
  obtain ⟨b,eq⟩ := op.exists_eq_add_of_fderiv_eq co (fun w hw => (hx w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (dh w hw).differentiableAt.differentiableWithinAt) (fun w hw => (hx w hw).fderiv.trans (dh w hw).fderiv.symm)
  refine ⟨b,?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) rp),self_mem_nhdsWithin] with w hw ne
  exact (eq ⟨hw,ne⟩).trans (add_comm _ _)

/-- In a puncture chart of any genus the original height takes the value
b+Re ξ in the constructed genuine exterior coordinate, and the Gauss
function in the same coordinate has holomorphic correction zero at
infinity. -/
theorem cap_height_log_differentials_normalize_physical_end {x : ℂ → ℝ} {h g P Q : ℂ → ℂ} {a : ℂ}
    (nz : a≠0) (pa : AnalyticAt ℂ P 0) (qa : AnalyticAt ℂ Q 0) {α : ℝ}
    (reg : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ x w ∧ scalarComplexCoefficient x w=h w)
    (height : ∀ᶠ w in 𝓝[≠] (0:ℂ), h w=a/w^2+P w)
    (order : meromorphicOrderAt (logDeriv g) 0=(-2:ℤ))
    (gauss : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g w ∧ g w≠0 ∧ logDeriv g w-I*(α:ℂ)*h w=Q w) :
    α≠0 ∧ ∃ (H k F : ℂ → ℂ) (b : ℝ), AnalyticAt ℂ k 0 ∧ k 0=0 ∧ AnalyticAt ℂ F 0 ∧ F 0=0 ∧
      (∀ᶠ w in 𝓝[≠] (0:ℂ), HasDerivAt H (h w) w ∧ k (H w)⁻¹=w ∧ x w=b+(H w).re) ∧
      Tendsto (fun ξ : ℂ => k ξ⁻¹) (cobounded ℂ) (𝓝[≠] 0) ∧
      ∀ᶠ ξ in cobounded ℂ, H (k ξ⁻¹)=ξ ∧ x (k ξ⁻¹)=b+ξ.re ∧ g (k ξ⁻¹)=exp (I*(α:ℂ)*ξ+F ξ⁻¹) := by
  obtain ⟨pitch,H,k,F,ka,k0,fa,f0,near,lim,far⟩ := differential_poles_give_true_helicoid_height_germ nz pa qa height order gauss
  obtain ⟨b,eq⟩ := punctured_height_equals_real_primitive ((reg.and near).mono fun _ h => ⟨h.1.1,h.1.2,h.2.1⟩)
  refine ⟨pitch,H,k,F,b,ka,k0,fa,f0,(near.and eq).mono (fun _ h => ⟨h.1.1,h.1.2,h.2⟩),lim,?_⟩
  filter_upwards [far,lim.eventually eq] with ξ data physical
  exact ⟨data.1,by rwa [data.1] at physical,data.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.cap_height_log_differentials_normalize_physical_end
