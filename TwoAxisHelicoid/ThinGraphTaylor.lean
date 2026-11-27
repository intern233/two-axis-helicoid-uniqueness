import TwoAxisHelicoid.SecondOrderMean
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

theorem exists_first_order_mean_at_zero {f f₁ f₂ : ℝ → ℝ} {l : ℝ} (hl : 0 < l)
    (hd : ∀ x ∈ Icc 0 l, HasDerivAt f (f₁ x) x)
    (hdd : ∀ x ∈ Icc 0 l, HasDerivAt f₁ (f₂ x) x) :
    ∃ c ∈ Ioo 0 l, f l-f 0-l*f₁ 0 = f₂ c/2*l^2 := by
  let g := fun x => f (-x)-f 0+x*f₁ 0
  let g₁ := fun x => -f₁ (-x)+f₁ 0
  have hdg (x : ℝ) (hx : x ∈ Icc (-l) 0) : HasDerivAt g (g₁ x) x := by
    have hx' : -x ∈ Icc 0 l := ⟨by linarith [hx.2],by linarith [hx.1]⟩
    have hh := (((hd (-x) hx').comp x (hasDerivAt_id x).neg).sub_const (f 0)).add
      ((hasDerivAt_id x).mul_const (f₁ 0))
    convert hh using 1
    · rfl
    · simp [g₁]
  have hddg (x : ℝ) (hx : x ∈ Icc (-l) 0) : HasDerivAt g₁ (f₂ (-x)) x := by
    have hx' : -x ∈ Icc 0 l := ⟨by linarith [hx.2],by linarith [hx.1]⟩
    have hh := (((hdd (-x) hx').comp x (hasDerivAt_id x).neg).neg).add_const (f₁ 0)
    convert hh using 1
    · rfl
    · simp
  obtain ⟨c,hc,he⟩ := exists_second_order_mean (by linarith : -l < 0) hdg hddg (by simp [g₁])
  refine ⟨-c,⟨by linarith [hc.2],by linarith [hc.1]⟩,?_⟩
  simpa [g,neg_mul,sub_eq_add_neg,add_assoc] using he

/-- The exact one-dimensional estimate used to turn a thin tube and a Hessian
bound into a small gradient in PDF §4.3. -/
theorem thin_graph_derivative_bound {f f₁ f₂ : ℝ → ℝ} {l ε C : ℝ} (hl : 0 < l)
    (hd : ∀ x ∈ Icc 0 l, HasDerivAt f (f₁ x) x)
    (hdd : ∀ x ∈ Icc 0 l, HasDerivAt f₁ (f₂ x) x)
    (hf : ∀ x ∈ Icc 0 l, |f x| ≤ ε)
    (hf₂ : ∀ x ∈ Icc 0 l, |f₂ x| ≤ C) :
    |f₁ 0| ≤ 2*ε/l+C*l/2 := by
  obtain ⟨c,hc,he⟩ := exists_first_order_mean_at_zero hl hd hdd
  have h0 := abs_le.mp (hf 0 ⟨le_rfl,hl.le⟩)
  have hlv := abs_le.mp (hf l ⟨hl.le,le_rfl⟩)
  have hc2 := abs_le.mp (hf₂ c ⟨hc.1.le,hc.2.le⟩)
  have hlow : -(2*ε/l+C*l/2)*l ≤ l*f₁ 0 := by
    have hc3 := mul_le_mul_of_nonneg_right hc2.2 (sq_nonneg l)
    have hdiv : (2*ε/l)*l = 2*ε := div_mul_cancel₀ _ hl.ne'
    nlinarith
  have hupp : l*f₁ 0 ≤ (2*ε/l+C*l/2)*l := by
    have hc3 := mul_le_mul_of_nonneg_right hc2.1 (sq_nonneg l)
    have hdiv : (2*ε/l)*l = 2*ε := div_mul_cancel₀ _ hl.ne'
    nlinarith
  apply abs_le.mpr
  constructor <;> nlinarith

theorem thin_graph_sqrt_bound {f f₁ f₂ : ℝ → ℝ} {ε C : ℝ} (hε : 0 < ε)
    (hd : ∀ x ∈ Icc 0 (Real.sqrt ε), HasDerivAt f (f₁ x) x)
    (hdd : ∀ x ∈ Icc 0 (Real.sqrt ε), HasDerivAt f₁ (f₂ x) x)
    (hf : ∀ x ∈ Icc 0 (Real.sqrt ε), |f x| ≤ ε)
    (hf₂ : ∀ x ∈ Icc 0 (Real.sqrt ε), |f₂ x| ≤ C) :
    |f₁ 0| ≤ (2+C/2)*Real.sqrt ε := by
  have hs := Real.sqrt_pos.mpr hε
  have h := thin_graph_derivative_bound hs hd hdd hf hf₂
  have he : 2*ε/Real.sqrt ε+C*Real.sqrt ε/2 = (2+C/2)*Real.sqrt ε := by
    have hdv : ε/Real.sqrt ε = Real.sqrt ε := by
      apply (div_eq_iff hs.ne').mpr
      nlinarith [Real.sq_sqrt hε.le]
    rw [mul_div_assoc,hdv]
    ring
  rw [he] at h
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thin_graph_derivative_bound
