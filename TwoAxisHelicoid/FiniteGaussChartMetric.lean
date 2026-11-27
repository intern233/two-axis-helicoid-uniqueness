import TwoAxisHelicoid.NullGaussAlgebra
import TwoAxisHelicoid.NullEuclideanMetric
import TwoAxisHelicoid.ChartSecondFundamentalWeingarten

namespace TwoAxisHelicoid
open Complex Matrix Filter Topology
open scoped Topology

/-- Weierstrass data in the finite Gauss chart. The horizontal complex
differential stays nonzero at a Gauss zero. -/
noncomputable def finiteGaussTriple (g l : ℂ) : Fin 3 → ℂ :=
  ![(1-g^2)*l/2,I*(1+g^2)*l/2,g*l]

noncomputable def finiteGaussNormal (g : ℂ) : Fin 3 → ℝ :=
  ![2*g.re/(1+normSq g),2*g.im/(1+normSq g),(normSq g-1)/(1+normSq g)]

theorem null_in_finite_gauss_chart {p : Fin 3 → ℂ} (hp : ComplexNull p) (hl : nullHorizontalMinus p≠0) :
    p=finiteGaussTriple (nullGauss p) (nullHorizontalMinus p) := by
  let l := nullHorizontalMinus p
  let g := nullGauss p
  have height : g*l=p 2 := div_mul_cancel₀ _ hl
  have plus : nullHorizontalPlus p= -(g^2*l) := by
    apply mul_left_cancel₀ hl
    rw [null_horizontal_product hp,← height]
    change -(g*l)^2=l* -(g^2*l)
    ring
  have horizontal₀ : p 0=(nullHorizontalMinus p+nullHorizontalPlus p)/2 := by
    unfold nullHorizontalMinus nullHorizontalPlus
    ring
  have horizontal₁ : p 1=I*(nullHorizontalMinus p-nullHorizontalPlus p)/2 := by
    unfold nullHorizontalMinus nullHorizontalPlus
    linear_combination (p 1)*Complex.I_sq
  funext j
  fin_cases j
  · change p 0=(1-g^2)*l/2
    rw [horizontal₀,plus]
    change (l+ -(g^2*l))/2=(1-g^2)*l/2
    ring
  · change p 1=I*(1+g^2)*l/2
    rw [horizontal₁,plus]
    change I*(l- -(g^2*l))/2=I*(1+g^2)*l/2
    ring
  · exact height.symm

theorem finiteGaussTriple_metric (g l : ℂ) :
    nullMetric (finiteGaussTriple g l)=normSq l*(1+normSq g)^2/4 := by
  simp [nullMetric,finiteGaussTriple,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two]
  ring

private theorem finiteGaussNormal_unit (g : ℂ) : finiteGaussNormal g ⬝ᵥ finiteGaussNormal g=1 := by
  have hp : 0<1+normSq g := by linarith [Complex.normSq_nonneg g]
  simp only [dotProduct,Fin.sum_univ_succ,finiteGaussNormal,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  field_simp
  simp only [Complex.normSq_apply]
  ring

/-- Normalizing the actual two tangent vectors of the null differential
recovers stereographic projection everywhere in this chart. -/
theorem finiteGaussTriple_oriented_unit_normal (g : ℂ) {l : ℂ} (hl : l≠0) :
    let D := nullRealDerivative (finiteGaussTriple g l)
    unitCrossNormal (D 1) (D I)=finiteGaussNormal g := by
  let D := nullRealDerivative (finiteGaussTriple g l)
  let c := normSq l*(1+normSq g)^2/4
  have hp : 0<1+normSq g := by linarith [Complex.normSq_nonneg g]
  have cp : 0<c := div_pos (mul_pos (Complex.normSq_pos.mpr hl) (sq_pos_of_pos hp)) (by norm_num)
  have cross : D 1 ⨯₃ D I=c • finiteGaussNormal g := by
    ext j
    fin_cases j <;> simp [D,cross_apply,finiteGaussTriple,finiteGaussNormal,nullRealDerivative_apply,c,
      Complex.mul_re,Complex.mul_im,pow_two] <;>
      field_simp <;> simp only [Complex.normSq_apply] <;> ring
  change (Real.sqrt ((D 1 ⨯₃ D I) ⬝ᵥ (D 1 ⨯₃ D I)))⁻¹ • (D 1 ⨯₃ D I)=_
  rw [cross,smul_dotProduct,dotProduct_smul,smul_eq_mul,smul_eq_mul,finiteGaussNormal_unit,mul_one,
    ← pow_two,Real.sqrt_sq cp.le,smul_smul,inv_mul_cancel₀ cp.ne',one_smul]

theorem physical_speed_in_finite_gauss_chart {p : Fin 3 → ℂ} (hp : ComplexNull p)
    (hl : nullHorizontalMinus p≠0) (v : ℂ) :
    ‖coordinateToEuclidean (nullRealDerivative p v)‖=
      (1+normSq (nullGauss p))/2*‖nullHorizontalMinus p*v‖ := by
  have pn : p≠0 := by
    rintro rfl
    exact hl (by simp [nullHorizontalMinus])
  have metric : nullMetric p=normSq (nullHorizontalMinus p)*(1+normSq (nullGauss p))^2/4 :=
    (congrArg nullMetric (null_in_finite_gauss_chart hp hl)).trans (finiteGaussTriple_metric _ _)
  have hs : 0<1+normSq (nullGauss p) := by linarith [Complex.normSq_nonneg (nullGauss p)]
  rw [nullRealDerivative_euclidean_norm hp pn,metric,norm_mul]
  have root : Real.sqrt (normSq (nullHorizontalMinus p)*(1+normSq (nullGauss p))^2/4) =
      ‖nullHorizontalMinus p‖*((1+normSq (nullGauss p))/2) := by
    apply (Real.sqrt_eq_iff_eq_sq (div_nonneg (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)) (by norm_num)) (by positivity)).mpr
    rw [Complex.normSq_eq_norm_sq]
    ring
  rw [root]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.finiteGaussTriple_oriented_unit_normal
#print axioms TwoAxisHelicoid.physical_speed_in_finite_gauss_chart

