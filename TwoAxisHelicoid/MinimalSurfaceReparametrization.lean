import TwoAxisHelicoid.MeanCurvatureNumerator

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology ContDiff
set_option maxHeartbeats 1400000

theorem symmetric_complex_plane_bilinear_expansion {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Q : ℂ →L[ℝ] ℂ →L[ℝ] E)
    (hQ : Q I 1 = Q 1 I) (v w : ℂ) :
    Q v w = (v.re*w.re) • Q 1 1 + (v.re*w.im+v.im*w.re) • Q 1 I +
      (v.im*w.im) • Q I I := by
  rw [real_linear_complex_expansion Q v]
  simp only [_root_.add_apply,_root_.smul_apply]
  rw [real_linear_complex_expansion (Q 1) w,real_linear_complex_expansion (Q I) w,hQ]
  simp only [smul_add,smul_smul,add_smul]
  abel

/-- The first and second jets of an arbitrary C² real change of coordinates
preserve the vanishing of the geometric mean curvature. -/
theorem minimal_surface_reparametrization {X : ℂ → Fin 3 → ℝ} {f : ℂ → ℂ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X (f z)) (hf : ContDiffAt ℝ 2 f z)
    (hm : coordinateMeanCurvature X (f z) = 0) :
    coordinateMeanCurvature (X ∘ f) z = 0 := by
  let L := fderiv ℝ X (f z)
  let Q := fderiv ℝ (fderiv ℝ X) (f z)
  let T := fderiv ℝ f z
  let R := fderiv ℝ (fderiv ℝ f) z
  have hQ : Q I 1 = Q 1 I := (hX.isSymmSndFDerivAt (by simp)).eq I 1
  have h₁ (v : ℂ) : fderiv ℝ (X ∘ f) z v = (T v).re • L 1 + (T v).im • L I := by
    rw [fderiv_comp z (hX.differentiableAt two_ne_zero) (hf.differentiableAt two_ne_zero)]
    exact real_linear_complex_expansion L (T v)
  have h₂ (v w : ℂ) : fderiv ℝ (fderiv ℝ (X ∘ f)) z v w =
      ((T v).re*(T w).re) • Q 1 1+((T v).re*(T w).im+(T v).im*(T w).re) • Q 1 I+
      ((T v).im*(T w).im) • Q I I+(R v w).re • L 1+(R v w).im • L I := by
    rw [surface_composition_second_derivative hX hf v w]
    change L (R v w) + Q (T v) (T w) = _
    rw [real_linear_complex_expansion L (R v w),symmetric_complex_plane_bilinear_expansion Q hQ]
    abel
  rw [coordinateMeanCurvature_zero_iff_numerator] at hm ⊢
  change meanCurvatureNumerator (L 1) (L I) (Q 1 1) (Q 1 I) (Q I I) = 0 at hm
  rw [h₁ 1,h₁ I,h₂ 1 1,h₂ 1 I,h₂ I I]
  have he := meanCurvatureNumerator_basis_change (L 1) (L I) (Q 1 1) (Q 1 I) (Q I I)
    (T 1).re (T 1).im (T I).re (T I).im
    (R 1 1).re (R 1 1).im (R 1 I).re (R 1 I).im (R I I).re (R I I).im
  rw [hm,mul_zero] at he
  convert he using 3 <;> ring_nf

noncomputable def spatialPermutation (σ : Equiv.Perm (Fin 3)) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (σ i))

theorem spatialPermutation_dot (σ : Equiv.Perm (Fin 3)) (A B : Fin 3 → ℝ) :
    spatialPermutation σ A ⬝ᵥ spatialPermutation σ B = A ⬝ᵥ B :=
  Equiv.sum_comp σ (fun j => A j*B j)

theorem spatialPermutation_triple (σ : Equiv.Perm (Fin 3)) (A B C : Fin 3 → ℝ) :
    spatialPermutation σ A ⬝ᵥ (spatialPermutation σ B ⨯₃ spatialPermutation σ C) =
      (Equiv.Perm.sign σ : ℤ) * (A ⬝ᵥ (B ⨯₃ C)) := by
  rw [triple_product_eq_det,triple_product_eq_det]
  have he : ![spatialPermutation σ A,spatialPermutation σ B,spatialPermutation σ C] =
      Matrix.submatrix (![A,B,C] : Matrix (Fin 3) (Fin 3) ℝ) id σ := by
    ext i j
    fin_cases i <;> rfl
  rw [he]
  exact Matrix.det_permute' σ (![A,B,C] : Matrix (Fin 3) (Fin 3) ℝ)

theorem minimal_surface_spatialPermutation {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z) (σ : Equiv.Perm (Fin 3)) (hm : coordinateMeanCurvature X z = 0) :
    coordinateMeanCurvature (spatialPermutation σ ∘ X) z = 0 := by
  let P := spatialPermutation σ
  have h₁ (v : ℂ) : fderiv ℝ (P ∘ X) z v = P (fderiv ℝ X z v) := by
    rw [fderiv_comp z P.differentiableAt (hX.differentiableAt two_ne_zero),P.fderiv]
    rfl
  have h₂ (v w : ℂ) : fderiv ℝ (fderiv ℝ (P ∘ X)) z v w = P (fderiv ℝ (fderiv ℝ X) z v w) := by
    have he : fderiv ℝ (P ∘ X) =ᶠ[𝓝 z] fun y => P.comp (fderiv ℝ X y) := by
      filter_upwards [hX.eventually (by norm_num)] with y hy
      rw [fderiv_comp y P.differentiableAt (hy.differentiableAt two_ne_zero),P.fderiv]
    have hx := ((hX.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
    rw [he.fderiv_eq,((hasFDerivAt_const P z).clm_comp hx).fderiv]
    simp
  rw [coordinateMeanCurvature_zero_iff_numerator] at hm ⊢
  rw [h₁,h₁,h₂,h₂,h₂]
  simp only [meanCurvatureNumerator,P,spatialPermutation_dot,spatialPermutation_triple] at hm ⊢
  linear_combination (Equiv.Perm.sign σ : ℤ) * hm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.minimal_surface_reparametrization
#print axioms TwoAxisHelicoid.minimal_surface_spatialPermutation
