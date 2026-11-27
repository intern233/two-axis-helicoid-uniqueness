import TwoAxisHelicoid.FiniteGaussChartMetric
import Mathlib.Analysis.Calculus.FDeriv.Norm

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology ContDiff

/-- Stereographic coordinates read from the physical oriented unit normal. -/
noncomputable def gaussCoordinateOfNormal (n : Fin 3 → ℝ) : ℂ :=
  (⟨n 0,n 1⟩ : ℂ)/(1-n 2 : ℝ)

theorem gaussCoordinateOfNormal_finite (g : ℂ) :
    gaussCoordinateOfNormal (finiteGaussNormal g)=g := by
  have positive : 0<1+normSq g := by linarith [Complex.normSq_nonneg g]
  have den : 1-(normSq g-1)/(1+normSq g)=2/(1+normSq g) := by field_simp; ring
  change (⟨2*g.re/(1+normSq g),2*g.im/(1+normSq g)⟩:ℂ)/(1-(normSq g-1)/(1+normSq g):ℝ)=g
  rw [den]
  apply (div_eq_iff (Complex.ofReal_ne_zero.mpr (div_ne_zero two_ne_zero positive.ne'))).mpr
  apply Complex.ext
  · rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    change 2*g.re/(1+normSq g)=g.re*(2/(1+normSq g))
    ring
  · rw [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]
    change 2*g.im/(1+normSq g)=g.im*(2/(1+normSq g))
    ring

/-- At the pole of the finite chart the physical normal is exactly the
north pole, including the sign determined by the oriented cross product. -/
theorem polar_null_oriented_normal {p : Fin 3 → ℂ} (hp : ComplexNull p) (np : p≠0)
    (pole : nullHorizontalMinus p=0) :
    unitCrossNormal (nullRealDerivative p 1) (nullRealDerivative p I)=![0,0,1] := by
  have hor : p 0=I*p 1 := sub_eq_zero.mp pole
  have h := null_horizontal_product hp
  rw [pole,zero_mul,eq_comm,neg_eq_zero] at h
  have ht : p 2=0 := eq_zero_of_pow_eq_zero h
  have p1 : p 1≠0 := by
    intro e
    apply np
    funext j
    fin_cases j <;> simp [hor,e,ht]
  let c := normSq (p 1)
  have pos : 0<c := Complex.normSq_pos.mpr p1
  have cross : nullRealDerivative p 1 ⨯₃ nullRealDerivative p I = ![0,0,c] := by
    funext j
    fin_cases j <;> simp [cross_apply,hor,ht,c,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
    ring
  rw [unitCrossNormal,cross]
  have area : (![0,0,c] : Fin 3 → ℝ) ⬝ᵥ ![0,0,c]=c^2 := by simp [dotProduct,Fin.sum_univ_succ,pow_two]
  rw [area,Real.sqrt_sq pos.le]
  funext j
  fin_cases j <;> simp [pos.ne']

/-- Separation from the north pole controls the measured Gauss coordinate
uniformly, without imposing a nonzero height derivative. -/
theorem null_gauss_chart_of_normal_bound {p : Fin 3 → ℂ} (hp : ComplexNull p) (np : p≠0)
    (bound : unitCrossNormal (nullRealDerivative p 1) (nullRealDerivative p I) 2≤15/16) :
    nullHorizontalMinus p≠0 ∧
    gaussCoordinateOfNormal (unitCrossNormal (nullRealDerivative p 1) (nullRealDerivative p I))=nullGauss p ∧
    ‖nullGauss p‖≤6 := by
  have hl : nullHorizontalMinus p≠0 := by
    intro bad
    rw [polar_null_oriented_normal hp np bad] at bound
    norm_num at bound
  have normal : unitCrossNormal (nullRealDerivative p 1) (nullRealDerivative p I)=finiteGaussNormal (nullGauss p) :=
    (congrArg (fun q => unitCrossNormal (nullRealDerivative q 1) (nullRealDerivative q I))
      (null_in_finite_gauss_chart hp hl)).trans (finiteGaussTriple_oriented_unit_normal _ hl)
  refine ⟨hl,normal ▸ gaussCoordinateOfNormal_finite _,?_⟩
  rw [normal] at bound
  change (normSq (nullGauss p)-1)/(1+normSq (nullGauss p))≤15/16 at bound
  have hp' : 0<1+normSq (nullGauss p) := by linarith [Complex.normSq_nonneg (nullGauss p)]
  have h := (div_le_iff₀ hp').mp bound
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [sq_nonneg (‖nullGauss p‖-6)]

/-- Chord distance on the actual unit sphere yields the global factor
two for stereographic projection in the finite coordinate. -/
theorem finite_gauss_chord_distance (g h : ℂ) :
    ‖coordinateToEuclidean (finiteGaussNormal g)-coordinateToEuclidean (finiteGaussNormal h)‖^2*
      (1+normSq g)*(1+normSq h)=4*‖g-h‖^2 := by
  have a : 0<1+normSq g := by linarith [Complex.normSq_nonneg g]
  have b : 0<1+normSq h := by linarith [Complex.normSq_nonneg h]
  rw [← map_sub,EuclideanSpace.real_norm_sq_eq,← Complex.normSq_eq_norm_sq]
  simp only [Fin.sum_univ_succ,coordinateToEuclidean_apply,Pi.sub_apply,finiteGaussNormal,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,WithLp.ofLp_toLp]
  field_simp
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

theorem finite_gauss_normal_lipschitz : LipschitzWith 2 (coordinateToEuclidean ∘ finiteGaussNormal) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  let d := ‖coordinateToEuclidean (finiteGaussNormal g)-coordinateToEuclidean (finiteGaussNormal h)‖
  have zero : 0≤d := norm_nonneg _
  have a : 1≤1+normSq g := by linarith [Complex.normSq_nonneg g]
  have b : 1≤1+normSq h := by linarith [Complex.normSq_nonneg h]
  have le : 1≤(1+normSq g)*(1+normSq h) := one_le_mul_of_one_le_of_one_le a b
  have upper := mul_le_mul_of_nonneg_left le (sq_nonneg d)
  have eq : d^2*((1+normSq g)*(1+normSq h))=4*‖g-h‖^2 := by rw [← mul_assoc]; exact finite_gauss_chord_distance _ _
  rw [mul_one,eq] at upper
  change d≤2*dist g h
  rw [dist_eq_norm]
  exact (sq_le_sq₀ zero (by positivity)).mp (by nlinarith only [upper])

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.null_gauss_chart_of_normal_bound
#print axioms TwoAxisHelicoid.finite_gauss_normal_lipschitz

