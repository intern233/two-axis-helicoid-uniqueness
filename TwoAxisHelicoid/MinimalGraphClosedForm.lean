import TwoAxisHelicoid.MinimalGraphConjugate

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

theorem graph_line_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {z : ℂ} (hf : DifferentiableAt ℝ f z) (v : ℂ) :
    HasDerivAt (fun s : ℝ => f (z+s • v)) (fderiv ℝ f z v) 0 := by
  have hl : HasDerivAt (fun s : ℝ => z+s • v) v 0 := by
    simpa only [Pi.add_apply,zero_add,one_smul] using!
      (hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id 0).smul_const v)
  have hf' : HasFDerivAt f (fderiv ℝ f z) (z+(0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt 0 hl

theorem complex_bilinear_symm_of_basis (D : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (h : D 1 I = D I 1) (v w : ℂ) : D v w = D w v := by
  calc
    D v w = v.re * (w.re * D 1 1 + w.im * D 1 I) +
      v.im * (w.re * D I 1 + w.im * D I I) := by
        rw [real_linear_complex_expansion D v]
        simp only [add_apply,smul_apply,smul_eq_mul]
        rw [real_linear_complex_expansion (D 1) w,real_linear_complex_expansion (D I) w]
        rfl
    _ = D w v := by
        rw [real_linear_complex_expansion D w]
        simp only [add_apply,smul_apply,smul_eq_mul]
        rw [real_linear_complex_expansion (D 1) v,real_linear_complex_expansion (D I) v]
        simp only [smul_eq_mul,h]
        ring

/-- The minimal graph equation makes the conjugate of dx closed in the
original graph coordinates. Differentiation is with respect to the actual
slope functions. -/
theorem minimal_graph_conjugate_closed {p q : ℂ → ℝ} {z : ℂ}
    (hp : ContDiffAt ℝ 1 p z) (hq : ContDiffAt ℝ 1 q z)
    (hmix : fderiv ℝ p z I = fderiv ℝ q z 1)
    (hmin : (1+(q z)^2)*fderiv ℝ p z 1-2*p z*q z*fderiv ℝ q z 1+
      (1+(p z)^2)*fderiv ℝ q z I = 0)
    (v w : ℂ) :
    fderiv ℝ (graphConjugateForm p q) z v w = fderiv ℝ (graphConjugateForm p q) z w v := by
  apply complex_bilinear_symm_of_basis
  let D := fderiv ℝ (graphConjugateForm p q) z
  have hline (v w : ℂ) : HasDerivAt (fun s : ℝ => graphConjugateForm p q (z+s • v) w)
      (D v w) 0 := by
    simpa only [map_zero,add_zero] using!
      (graph_line_deriv ((graphConjugateForm_smooth hp hq).differentiableAt one_ne_zero) v).clm_apply
        (hasDerivAt_const (0 : ℝ) w)
  have hB := (graphConjugateB_deriv (graph_line_deriv (hp.differentiableAt one_ne_zero) 1)
    (graph_line_deriv (hq.differentiableAt one_ne_zero) 1))
  have hA := (graphConjugateA_deriv (graph_line_deriv (hp.differentiableAt one_ne_zero) I)
    (graph_line_deriv (hq.differentiableAt one_ne_zero) I))
  have hrB := (hline 1 I).unique (hB.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by simp [graphConjugateForm])))
  have hrA := (hline I 1).unique (hA.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by simp [graphConjugateForm])))
  simp only [zero_smul,add_zero] at hrA hrB
  change D 1 I = D I 1
  rw [hrB,hrA,hmix]
  set W := graphAreaWeight (p z) (q z)
  have hW : W ≠ 0 := (graphAreaWeight_pos _ _).ne'
  have hW2 : W^2=1+(p z)^2+(q z)^2 := graphAreaWeight_sq _ _
  field_simp
  linear_combination -(p z)*hmin + (q z * fderiv ℝ q z 1 - p z * fderiv ℝ q z I)*hW2

noncomputable def graphSlope (u : ℂ → ℝ) (v z : ℂ) := fderiv ℝ u z v

theorem graphSlope_smooth {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (v : ℂ) :
    ContDiffAt ℝ 1 (graphSlope u v) z :=
  (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

theorem graphSlope_fderiv {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (v w : ℂ) :
    fderiv ℝ (graphSlope u v) z w = fderiv ℝ (fderiv ℝ u) z w v := by
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hh := (graph_line_deriv hd w).clm_apply (hasDerivAt_const (0 : ℝ) v)
  simpa only [map_zero,add_zero] using
    (graph_line_deriv ((graphSlope_smooth hu v).differentiableAt one_ne_zero) w).unique hh

/-- The classical minimal graph equation in the original (x,y) plane. -/
def MinimalGraphEquation (u : ℂ → ℝ) (z : ℂ) : Prop :=
  let p := graphSlope u 1
  let q := graphSlope u I
  (1+(q z)^2)*fderiv ℝ p z 1-2*p z*q z*fderiv ℝ q z 1+
      (1+(p z)^2)*fderiv ℝ q z I = 0

/-- Construct a horizontal harmonic-conjugate coordinate locally, with the
actual differential. No conjugate or isothermal chart is supplied as data. -/
theorem minimal_graph_horizontal_conjugate {u : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hu : ∀ z ∈ U, ContDiffAt ℝ 2 u z)
    (hm : ∀ z ∈ U, MinimalGraphEquation u z) :
    ∃ η : ℂ → ℝ, ∀ z ∈ U, HasFDerivAt η
      (graphConjugateForm (graphSlope u 1) (graphSlope u I) z) z := by
  apply hconv.exists_forall_hasFDerivAt_of_fderiv_symmetric hU
  · intro z hz
    exact ((graphConjugateForm_smooth (graphSlope_smooth (hu z hz) 1)
      (graphSlope_smooth (hu z hz) I)).differentiableAt one_ne_zero).differentiableWithinAt
  · intro z hz v w
    apply minimal_graph_conjugate_closed (graphSlope_smooth (hu z hz) 1)
      (graphSlope_smooth (hu z hz) I) _ (hm z hz)
    rw [graphSlope_fderiv (hu z hz),graphSlope_fderiv (hu z hz)]
    exact ((hu z hz).isSymmSndFDerivAt (by simp)).eq I 1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.minimal_graph_horizontal_conjugate
