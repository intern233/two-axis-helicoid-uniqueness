import TwoAxisHelicoid.HelicoidGraphConformalMetric
import TwoAxisHelicoid.ChartSecondFundamentalWeingarten

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

noncomputable def tubeCartesianLinear : HelicoidTubeCoordinates →L[ℝ] (Fin 3 → ℝ) :=
  (show HelicoidTubeCoordinates →ₗ[ℝ] (Fin 3 → ℝ) from
    { toFun := tubeCartesian
      map_add' := fun v w => by ext j; fin_cases j <;> rfl
      map_smul' := fun c v => by ext j; fin_cases j <;> rfl }).toContinuousLinearMap

noncomputable def helicoidHeightSurface (u : ℝ × ℝ → ℝ) : ℂ → Fin 3 → ℝ :=
  tubeCartesianLinear ∘ helicoidGraphMap u ∘ helicoidConformalBase

noncomputable def conformalHelicoidNormal (z : ℂ) : Fin 3 → ℝ := standardHelicoidNormal (Real.sinh z.re) z.im

theorem physical_height_graph_derivative {u : ℝ × ℝ → ℝ} {z : ℂ}
    (du : DifferentiableAt ℝ u (helicoidConformalBase z)) (v : ℂ) :
    let q := helicoidConformalBase z
    let h := Real.cosh z.re
    fderiv ℝ (helicoidHeightSurface u) z v =
      fun j => h*v.re*helicoidTubeR q.1 q.2 (u q) j + v.im*helicoidTubeTheta q.1 q.2 (u q) j+
        fderiv ℝ u q (h*v.re,v.im)*conformalHelicoidNormal z j := by
  have d := tubeCartesianLinear.hasFDerivAt.comp z
    ((helicoidGraphMap_differentiableAt du).hasFDerivAt.comp z (helicoidConformalBase_hasFDerivAt z))
  dsimp only [helicoidHeightSurface]
  rw [d.fderiv]
  exact helicoidGraphMap_fderiv du _ _

/-- The first fundamental form of a half-width graph has a uniform
lower bound even when its height gradient is arbitrarily large. -/
theorem physical_height_graph_speed_lower {u : ℝ × ℝ → ℝ} {z : ℂ}
    (du : DifferentiableAt ℝ u (helicoidConformalBase z))
    (half : |u (helicoidConformalBase z)|≤1/2) (v : ℂ) :
    ‖v‖≤2*‖coordinateToEuclidean (fderiv ℝ (helicoidHeightSurface u) z v)‖ := by
  let q := helicoidConformalBase z
  let Q := Real.cosh z.re
  have Qp : 0<Q := Real.cosh_pos _
  have Q1 : 1≤Q := Real.one_le_cosh _
  have eqQ : helicoidQ q.1=Q := helicoidQ_sinh _
  have small : |u q/Q^2|≤1/2 := by
    rw [abs_div,abs_of_pos (sq_pos_of_pos Qp),div_le_iff₀ (sq_pos_of_pos Qp)]
    linarith [one_le_pow₀ Q1 (n:=2)]
  have lb := symmetric_two_coordinate_lower_bound small (Q*v.re) (Q*v.im)
  have simplifyA : Q*v.re+u q/Q^2*(Q*v.im)=Q*v.re+u q*v.im/Q := by field_simp
  have simplifyB : Q*v.im+u q/Q^2*(Q*v.re)=Q*(v.im+u q*(Q*v.re)/Q^3) := by field_simp
  rw [simplifyA,simplifyB] at lb
  have vnorm : (Q*v.re)^2+(Q*v.im)^2=Q^2*‖v‖^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  rw [vnorm,mul_pow] at lb
  have bound := mul_le_mul_of_nonneg_right (one_le_pow₀ Q1 (n:=2)) (sq_nonneg ‖v‖)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq]
  change ‖v‖^2≤2^2*∑ j,(fderiv ℝ (helicoidHeightSurface u) z v j)^2
  rw [physical_height_graph_derivative du]
  change ‖v‖^2≤2^2*∑ j,(Q*v.re*helicoidTubeR q.1 q.2 (u q) j+v.im*helicoidTubeTheta q.1 q.2 (u q) j+
    fderiv ℝ u q (Q*v.re,v.im)*standardHelicoidNormal q.1 q.2 j)^2
  rw [helicoidTube_vector_metric,eqQ]
  nlinarith only [lb,bound,sq_nonneg (fderiv ℝ u q (Q*v.re,v.im))]

theorem helicoid_base_cross (r θ : ℝ) :
    standardHelicoidR θ ⨯₃ standardHelicoidTheta r θ=helicoidQ r • standardHelicoidNormal r θ := by
  have qp := (helicoidQ_pos r).ne'
  funext j
  fin_cases j <;> simp [cross_apply,standardHelicoidR,standardHelicoidTheta,standardHelicoidNormal]
  <;> field_simp
  nlinarith [congrArg (fun x : ℝ => r*x) (Real.sin_sq_add_cos_sq θ)]

private theorem projected_tangent_area (R T N : Fin 3 → ℝ) (a b c d e f : ℝ) :
    N ⬝ᵥ ((a • R+b • T+c • N) ⨯₃ (d • R+e • T+f • N))=(a*e-b*d)*(N ⬝ᵥ (R ⨯₃ T)) := by
  have reverse : T ⨯₃ R= -(R ⨯₃ T) := (cross_anticomm R T).symm
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,dotProduct_add,dotProduct_smul,
    smul_eq_mul,cross_self,dotProduct_zero,dot_self_cross,dot_cross_self,reverse,dotProduct_neg]
  ring

/-- The actual oriented normal of a half-width graph makes an acute
angle with the base normal. The derivative of the height may be large
in either coordinate. -/
theorem physical_height_graph_normal_positive {u : ℝ × ℝ → ℝ} {z : ℂ}
    (du : DifferentiableAt ℝ u (helicoidConformalBase z))
    (half : |u (helicoidConformalBase z)|≤1/2) :
    0<conformalHelicoidNormal z ⬝ᵥ unitCrossNormal (fderiv ℝ (helicoidHeightSurface u) z 1)
      (fderiv ℝ (helicoidHeightSurface u) z I) := by
  let q := helicoidConformalBase z
  let Q := Real.cosh z.re
  let s := u q
  let R := standardHelicoidR q.2
  let T := standardHelicoidTheta q.1 q.2
  let N := conformalHelicoidNormal z
  let D := fderiv ℝ (helicoidHeightSurface u) z
  have Qp : 0<Q := Real.cosh_pos _
  have Q1 : 1≤Q := Real.one_le_cosh _
  have eqQ : helicoidQ q.1=Q := helicoidQ_sinh _
  have nn : N ⬝ᵥ N=1 := by
    change standardHelicoidNormal q.1 q.2 ⬝ᵥ standardHelicoidNormal q.1 q.2=1
    simpa only [dotProduct,← sq] using (standardHelicoid_unit_normal q.1 q.2).1
  have hRT : R ⨯₃ T=Q • N := eqQ ▸ helicoid_base_cross q.1 q.2
  have first : D 1=Q • R+(Q*s/Q^3) • T+fderiv ℝ u q (Q,0) • N := by
    change fderiv ℝ (helicoidHeightSurface u) z 1=_
    rw [physical_height_graph_derivative du]
    funext j
    change Q*(1:ℂ).re*(R j+s/(helicoidQ q.1)^3*T j)+(1:ℂ).im*helicoidTubeTheta q.1 q.2 s j+
      fderiv ℝ u q (Q*(1:ℂ).re,(1:ℂ).im)*N j=_
    simp only [Complex.one_re,Complex.one_im,eqQ,mul_one,zero_mul,add_zero,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have second : D I=(s/Q) • R+(1:ℝ) • T+fderiv ℝ u q (0,1) • N := by
    change fderiv ℝ (helicoidHeightSurface u) z I=_
    rw [physical_height_graph_derivative du]
    funext j
    change Q*I.re*helicoidTubeR q.1 q.2 s j+I.im*(T j+s/(helicoidQ q.1)*R j)+
      fderiv ℝ u q (Q*I.re,I.im)*N j=_
    simp only [Complex.I_re,Complex.I_im,eqQ,one_mul,mul_zero,zero_mul,zero_add,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have orient : 0<N ⬝ᵥ (D 1 ⨯₃ D I) := by
    rw [first,second,projected_tangent_area,hRT,dotProduct_smul,nn,smul_eq_mul,mul_one]
    have small : s^2≤1/4 := by
      have h := (sq_le_sq₀ (abs_nonneg s) (by norm_num : (0:ℝ)≤1/2)).mpr half
      simpa only [sq_abs] using (show |s|^2≤1/4 by linarith)
    have strict : s^2<Q^4 := lt_of_le_of_lt small (lt_of_lt_of_le (by norm_num : (1:ℝ)/4<1) (one_le_pow₀ Q1))
    apply mul_pos _ Qp
    field_simp
    nlinarith only [strict,Qp,pow_pos Qp 2,pow_pos Qp 3]
  have nz : D 1 ⨯₃ D I≠0 := by
    intro h
    rw [h,dotProduct_zero] at orient
    exact lt_irrefl _ orient
  have pos : 0<(D 1 ⨯₃ D I) ⬝ᵥ (D 1 ⨯₃ D I) :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg _) (fun h => nz (dotProduct_self_eq_zero.mp h.symm))
  change 0<N ⬝ᵥ unitCrossNormal (D 1) (D I)
  rw [unitCrossNormal,dotProduct_smul,smul_eq_mul]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr pos)) orient

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_height_graph_speed_lower
#print axioms TwoAxisHelicoid.physical_height_graph_normal_positive
