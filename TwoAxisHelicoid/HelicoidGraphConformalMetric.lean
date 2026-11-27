import TwoAxisHelicoid.HelicoidGraphDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Complex Set Real
open scoped Topology

/-- The conformal plane coordinate of the base helicoid, whose usual
radius parameter is sinh of the real coordinate. -/
noncomputable def helicoidConformalBase (z : ℂ) : ℝ × ℝ := (Real.sinh z.re,z.im)

theorem helicoidConformalBase_hasFDerivAt (z : ℂ) :
    HasFDerivAt helicoidConformalBase ((Real.cosh z.re • reCLM).prod imCLM) z := by
  have d := (Real.hasDerivAt_sinh z.re).comp_hasFDerivAt z reCLM.hasFDerivAt
  exact d.prodMk imCLM.hasFDerivAt

theorem helicoidQ_sinh (x : ℝ) : helicoidQ (Real.sinh x)=Real.cosh x := by
  have sq := Real.cosh_sq_sub_sinh_sq x
  apply (sq_eq_sq₀ (helicoidQ_pos _).le (Real.cosh_pos _).le).mp
  rw [helicoidQ_sq]
  linarith

/-- Cauchy--Schwarz for the graph height in the induced helicoid
metric, evaluated on any actual tangent direction. -/
theorem helicoid_graph_height_direction_bound (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) (x y : ℝ) :
    (fderiv ℝ u q (x,y))^2 ≤ (helicoidGraphGradientNorm u q)^2*(x^2+(helicoidQ q.1)^2*y^2) := by
  let D := fderiv ℝ u q
  let Q := helicoidQ q.1
  let a := D (1,0)
  let b := D (0,1)
  have qp : Q≠0 := (helicoidQ_pos _).ne'
  have val : D (x,y)=x*a+y*b := by
    have h : (x,y)=x • ((1,0):ℝ × ℝ)+y • (0,1) := by ext <;> simp
    rw [h,map_add,map_smul,map_smul]
    rfl
  change D (x,y)^2≤(Real.sqrt (a^2+b^2/Q^2))^2*(x^2+Q^2*y^2)
  rw [val,Real.sq_sqrt (by positivity)]
  have ident : (a^2+b^2/Q^2)*(x^2+Q^2*y^2)-(x*a+y*b)^2=(a*Q*y-b*x/Q)^2 := by
    field_simp
    ring
  linarith [sq_nonneg (a*Q*y-b*x/Q)]

/-- A half-width normal graph with height gradient at most one half
has uniformly comparable induced and standard helicoid metrics. -/
theorem helicoid_graph_metric_bounds {u : ℝ × ℝ → ℝ} {q : ℝ × ℝ}
    (du : DifferentiableAt ℝ u q) (s : |u q|≤1/2) (grad : helicoidGraphGradientNorm u q≤1/2) (x y : ℝ) :
    let m := x^2+(helicoidQ q.1)^2*y^2
    let lengthSq := ∑ i, (tubeCartesian (fderiv ℝ (helicoidGraphMap u) q (x,y)) i)^2
    m/4≤lengthSq ∧ lengthSq≤4*m := by
  dsimp only
  rw [helicoidGraphMap_fderiv du,helicoidTube_vector_metric]
  let Q := helicoidQ q.1
  have qp : 0<Q := helicoidQ_pos _
  have Q2 : 1≤Q^2 := one_le_pow₀ (helicoidQ_ge_one _)
  have ak : |u q/Q^2|≤1/2 := by
    rw [abs_div,abs_of_pos (sq_pos_of_pos qp),div_le_iff₀ (sq_pos_of_pos qp)]
    linarith
  have lower := symmetric_two_coordinate_lower_bound ak x (Q*y)
  have A : x+u q/Q^2*(Q*y)=x+u q*y/Q := by field_simp
  have B : Q*y+u q/Q^2*x=Q*(y+u q*x/Q^3) := by field_simp
  rw [A,B,mul_pow,mul_pow] at lower
  have upper := helicoid_graph_tangent_part_bound (r := q.1) s x y
  have ht := helicoid_graph_height_direction_bound u q x y
  have am : 0≤x^2+Q^2*y^2 := by positivity
  have small : (helicoidGraphGradientNorm u q)^2≤1/4 := by
    have nonnegative : 0≤helicoidGraphGradientNorm u q := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (1/2-helicoidGraphGradientNorm u q),mul_nonneg nonnegative (sub_nonneg.mpr grad)]
  have v := mul_le_mul_of_nonneg_right small am
  change _≤(x+u q*y/Q)^2+Q^2*(y+u q*x/Q^3)^2+_ ∧ _≤4*(x^2+Q^2*y^2)
  change (x+u q*y/Q)^2+Q^2*(y+u q*x/Q^3)^2≤_ at upper
  constructor <;> nlinarith [sq_nonneg (fderiv ℝ u q (x,y))]

/-- In the true conformal plane parameters this bounds every spatial
tangent of the normal graph by the same scalar cosh(x). -/
theorem helicoid_conformal_graph_metric_bounds {u : ℝ × ℝ → ℝ} {z : ℂ}
    (du : DifferentiableAt ℝ u (helicoidConformalBase z)) (s : |u (helicoidConformalBase z)|≤1/2)
    (grad : helicoidGraphGradientNorm u (helicoidConformalBase z)≤1/2) (v : ℂ) :
    let m := (Real.cosh z.re)^2*‖v‖^2
    let h := ∑ j, (tubeCartesian (fderiv ℝ (helicoidGraphMap u ∘ helicoidConformalBase) z v) j)^2
    m/4≤h ∧ h≤4*m := by
  let q := helicoidConformalBase z
  have deriv := ((helicoidGraphMap_differentiableAt du).hasFDerivAt.comp z (helicoidConformalBase_hasFDerivAt z)).fderiv
  have e : (Real.cosh z.re*v.re)^2+(helicoidQ q.1)^2*v.im^2=(Real.cosh z.re)^2*‖v‖^2 := by
    change _+(helicoidQ (Real.sinh z.re))^2*_=_
    rw [helicoidQ_sinh,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  dsimp only
  rw [deriv,← e]
  exact helicoid_graph_metric_bounds du s grad _ _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoid_conformal_graph_metric_bounds
