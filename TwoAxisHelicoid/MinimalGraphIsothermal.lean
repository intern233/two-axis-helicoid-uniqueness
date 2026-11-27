import TwoAxisHelicoid.MinimalGraphClosedForm
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- The induced Euclidean metric of the graph, in the coordinate
directions (x,y), is a scalar multiple of dx² + (*dx)². -/
theorem graph_horizontal_metric_identity (p q x y : ℝ) :
    x^2+y^2+(p*x+q*y)^2 =
      (graphAreaWeight p q)^2/(1+q^2) *
        (x^2+(graphConjugateA p q*x+graphConjugateB p q*y)^2) := by
  let W := graphAreaWeight p q
  have hW : W ≠ 0 := (graphAreaWeight_pos p q).ne'
  have hW2 := graphAreaWeight_sq p q
  change W^2 = _ at hW2
  unfold graphConjugateA graphConjugateB
  change x^2+y^2+(p*x+q*y)^2 = W^2/(1+q^2)*(x^2+(p*q/W*x+(1+q^2)/W*y)^2)
  have hq : (1+q^2) ≠ 0 := by positivity
  field_simp
  linear_combination -(x^2)*hW2

noncomputable def graphHorizontalChart (η : ℂ → ℝ) (z : ℂ) : ℂ := ⟨z.re,η z⟩

noncomputable def graphHorizontalDerivative (A B : ℝ) : ℂ →L[ℝ] ℂ :=
  equivRealProdCLM.symm.toContinuousLinearMap.comp (reCLM.prod (A • reCLM + B • imCLM))

theorem graphHorizontalDerivative_apply (A B : ℝ) (w : ℂ) :
    graphHorizontalDerivative A B w = ⟨w.re,A*w.re+B*w.im⟩ := rfl

theorem graphHorizontalDerivative_bijective (A B : ℝ) (hB : 0 < B) :
    Function.Bijective (graphHorizontalDerivative A B) := by
  constructor
  · intro v w he
    rw [graphHorizontalDerivative_apply,graphHorizontalDerivative_apply] at he
    have hr := congrArg Complex.re he
    change v.re = w.re at hr
    have hi := congrArg Complex.im he
    change A*v.re+B*v.im = A*w.re+B*w.im at hi
    rw [hr] at hi
    exact Complex.ext hr ((mul_right_inj' hB.ne').mp (add_left_cancel hi))
  · intro w
    refine ⟨⟨w.re,(w.im-A*w.re)/B⟩,Complex.ext rfl ?_⟩
    change A*w.re+B*((w.im-A*w.re)/B) = w.im
    field_simp
    ring

theorem graphHorizontalChart_hasFDerivAt {η : ℂ → ℝ} {z : ℂ} {A B : ℝ}
    (hη : HasFDerivAt η (A • reCLM+B • imCLM) z) :
    HasFDerivAt (graphHorizontalChart η) (graphHorizontalDerivative A B) z :=
  equivRealProdCLM.symm.hasFDerivAt.comp z (reCLM.hasFDerivAt.prodMk hη)

theorem graphHorizontalChart_contDiffAt {η : ℂ → ℝ} {z : ℂ} {n : ℕ∞ω}
    (hη : ContDiffAt ℝ n η z) : ContDiffAt ℝ n (graphHorizontalChart η) z :=
  equivRealProdCLM.symm.contDiff.contDiffAt.comp z (reCLM.contDiff.contDiffAt.prodMk hη)

/-- The actual minimal graph equation yields an isothermal chart near
every regular graph point. The conformal metric identity is asserted on
the open set where the equation holds. -/
theorem minimal_graph_isothermal_chart {u : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hu : ∀ z ∈ U, ContDiffAt ℝ 2 u z)
    (hm : ∀ z ∈ U, MinimalGraphEquation u z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z₀ ∈ e.source ∧
      ContDiffAt ℝ 2 e z₀ ∧ ContDiffAt ℝ 2 e.symm (e z₀) ∧
      ∀ z ∈ U, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ v : ℂ,
        v.re^2+v.im^2+(fderiv ℝ u z v)^2 = c₀*normSq (fderiv ℝ e z v) := by
  let p := graphSlope u 1
  let q := graphSlope u I
  let A := fun z => graphConjugateA (p z) (q z)
  let B := fun z => graphConjugateB (p z) (q z)
  obtain ⟨η,hη⟩ := minimal_graph_horizontal_conjugate hU hconv hu hm
  have hcη : ContDiffAt ℝ 2 η z₀ := by
    apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
    exact ⟨_,⟨U,hU.mem_nhds hz₀,hη⟩,graphConjugateForm_smooth
      (graphSlope_smooth (hu z₀ hz₀) 1) (graphSlope_smooth (hu z₀ hz₀) I)⟩
  let c := graphHorizontalChart η
  have hc : ContDiffAt ℝ 2 c z₀ := graphHorizontalChart_contDiffAt hcη
  have hcd (z : ℂ) (hz : z ∈ U) : HasFDerivAt c (graphHorizontalDerivative (A z) (B z)) z :=
    graphHorizontalChart_hasFDerivAt (hη z hz)
  let D := (LinearEquiv.ofBijective (graphHorizontalDerivative (A z₀) (B z₀)).toLinearMap
    (graphHorizontalDerivative_bijective _ _ (graphConjugateB_pos _ _))).toContinuousLinearEquiv
  have hD : HasFDerivAt c (D : ℂ →L[ℝ] ℂ) z₀ := hcd z₀ hz₀
  let e := hc.toOpenPartialHomeomorph c hD (by norm_num)
  refine ⟨e,hc.mem_toOpenPartialHomeomorph_source hD (by norm_num),hc,
    hc.to_localInverse hD (by norm_num),?_⟩
  intro z hz
  refine ⟨(graphAreaWeight (p z) (q z))^2/(1+(q z)^2),div_pos (sq_pos_of_pos (graphAreaWeight_pos _ _)) (by positivity),?_⟩
  intro v
  change _ = _*normSq (fderiv ℝ c z v)
  rw [(hcd z hz).fderiv,graphHorizontalDerivative_apply,real_linear_complex_expansion (fderiv ℝ u z) v]
  simpa only [normSq_apply,smul_eq_mul,pow_two,p,q,A,B,graphSlope,mul_comm] using
    graph_horizontal_metric_identity (p z) (q z) v.re v.im

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.minimal_graph_isothermal_chart
