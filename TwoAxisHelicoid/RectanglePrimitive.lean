import Mathlib.Analysis.Complex.HasPrimitives

namespace TwoAxisHelicoid
open Complex MeasureTheory Metric Set Filter
open scoped Topology Interval

def complexOpenRect (l r b u : ℝ) : Set ℂ :=
  {z | z.re ∈ Ioo l r ∧ z.im ∈ Ioo b u}

theorem complexOpenRect_isOpen (l r b u : ℝ) : IsOpen (complexOpenRect l r b u) :=
  (isOpen_Ioo.preimage continuous_re).inter (isOpen_Ioo.preimage continuous_im)

theorem rectangle_subset_openRect {l r b u : ℝ} {z w : ℂ}
    (hz : z ∈ complexOpenRect l r b u) (hw : w ∈ complexOpenRect l r b u) :
    Rectangle z w ⊆ complexOpenRect l r b u := by
  intro p hp
  exact ⟨ordConnected_Ioo.uIcc_subset hz.1 hw.1 hp.1,
    ordConnected_Ioo.uIcc_subset hz.2 hw.2 hp.2⟩

theorem wedgeIntegral_sub_on_rectangle {f : ℂ → ℂ} {l r b u : ℝ}
    (hf : DifferentiableOn ℂ f (complexOpenRect l r b u))
    {c z w : ℂ} (hc : c ∈ complexOpenRect l r b u)
    (hz : z ∈ complexOpenRect l r b u) (hw : w ∈ complexOpenRect l r b u) :
    wedgeIntegral c w f-wedgeIntegral c z f = wedgeIntegral z w f := by
  have hcorner {p q : ℂ} (hp : p ∈ complexOpenRect l r b u)
      (hq : q ∈ complexOpenRect l r b u) :
      (p.re:ℂ)+q.im*I ∈ complexOpenRect l r b u := by
    simpa [complexOpenRect] using And.intro hp.1 hq.2
  have ih (x y v : ℝ) (hx : (x:ℂ)+v*I ∈ complexOpenRect l r b u)
      (hy : (y:ℂ)+v*I ∈ complexOpenRect l r b u) :
      IntervalIntegrable (fun s : ℝ => f ((s:ℂ)+v*I)) volume x y := by
    apply ContinuousOn.intervalIntegrable
    apply hf.continuousOn.comp (by fun_prop)
    intro s hs
    have he : ((s:ℂ)+v*I).re ∈ uIcc ((x:ℂ)+v*I).re ((y:ℂ)+v*I).re := by simpa using hs
    have hv : ((s:ℂ)+v*I).im ∈ uIcc ((x:ℂ)+v*I).im ((y:ℂ)+v*I).im := by simp
    exact rectangle_subset_openRect hx hy ⟨he,hv⟩
  have iv (x v y : ℝ) (hx : (x:ℂ)+v*I ∈ complexOpenRect l r b u)
      (hy : (x:ℂ)+y*I ∈ complexOpenRect l r b u) :
      IntervalIntegrable (fun s : ℝ => f ((x:ℂ)+s*I)) volume v y := by
    apply ContinuousOn.intervalIntegrable
    apply hf.continuousOn.comp (by fun_prop)
    intro s hs
    have he : ((x:ℂ)+s*I).re ∈ uIcc ((x:ℂ)+v*I).re ((x:ℂ)+y*I).re := by simp
    have hv : ((x:ℂ)+s*I).im ∈ uIcc ((x:ℂ)+v*I).im ((x:ℂ)+y*I).im := by simpa using hs
    exact rectangle_subset_openRect hx hy ⟨he,hv⟩
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (ih c.re z.re c.im (hcorner hc hc) (hcorner hz hc))
    (ih z.re w.re c.im (hcorner hz hc) (hcorner hw hc))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (iv w.re c.im z.im (hcorner hw hc) (hcorner hw hz))
    (iv w.re z.im w.im (hcorner hw hz) (hcorner hw hw))
  have h0 := hf.isConservativeOn ((z.re:ℂ)+c.im*I) ((w.re:ℂ)+z.im*I)
    (rectangle_subset_openRect (hcorner hz hc) (hcorner hw hz))
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq] at h0
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,
    mul_one,zero_add,add_zero,sub_zero] at h0
  simp only [wedgeIntegral,smul_eq_mul] at *
  linear_combination -h1-I*h2+h0

theorem holomorphic_rectangle_has_primitive {f : ℂ → ℂ} {l r b u : ℝ}
    (hf : DifferentiableOn ℂ f (complexOpenRect l r b u))
    {c : ℂ} (hc : c ∈ complexOpenRect l r b u) :
    ∀ z ∈ complexOpenRect l r b u,
      HasDerivAt (fun w => wedgeIntegral c w f) (f z) z := by
  intro z hz
  obtain ⟨d,hd,hsub⟩ := Metric.isOpen_iff.mp (complexOpenRect_isOpen l r b u) z hz
  have hball := hf.mono hsub
  have hder := hball.isConservativeOn.hasDerivAt_wedgeIntegral hball.continuousOn (mem_ball_self hd)
  have hplus := hder.add_const (wedgeIntegral c z f)
  apply hplus.congr_of_eventuallyEq
  filter_upwards [(complexOpenRect_isOpen l r b u).mem_nhds hz] with w hw
  linear_combination wedgeIntegral_sub_on_rectangle hf hc hz hw

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.holomorphic_rectangle_has_primitive
