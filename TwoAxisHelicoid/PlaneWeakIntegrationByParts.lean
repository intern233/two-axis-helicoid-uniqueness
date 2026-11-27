import TwoAxisHelicoid.PlaneDirichletPotential
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter InnerProductSpace
open scoped ContDiff RealInnerProductSpace

theorem planeTestGradient_pair (φ : ℂ → ℝ) (z d : ℂ) :
    ⟪planeTestGradient φ z,d⟫_ℝ=fderiv ℝ φ z d := by
  conv_rhs => rw [show d=d.re • (1:ℂ)+d.im • I by simp]
  simp only [map_add,map_smul,smul_eq_mul,Complex.inner,Complex.mul_re,Complex.conj_im,Complex.conj_re,
    planeTestGradient]
  ring

theorem plane_compact_derivative_integral_zero {φ : ℂ → ℝ} (s : ContDiff ℝ ∞ φ)
    (h : HasCompactSupport φ) (d : ℂ) : (∫ z, fderiv ℝ φ z d)=0 := by
  have cont : Continuous (fun z => fderiv ℝ φ z d) :=
    (s.continuous_fderiv (by simp)).clm_apply continuous_const
  simpa using integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=volume) (f:=fun _ : ℂ => (1:ℝ))
    (g:=φ) (v:=d) (by simp) (by simpa using cont.integrable_of_hasCompactSupport (h.fderiv_apply ℝ d))
    (by simpa using s.continuous.integrable_of_hasCompactSupport h) (fun _ _ => differentiableAt_const _)
    (fun z _ => s.differentiable (by simp) z)

/-- Every pair in the W¹,² closure has the asserted distributional derivative
in every real direction, tested against actual compactly supported functions. -/
theorem disk_potential_distributional_derivative {U : Set ℂ} {v : Lp ℝ 2 (volume:Measure ℂ)}
    {u : Lp ℂ 2 (volume:Measure ℂ)} (pair : (v,u)∈(planeDirichletPairs U).topologicalClosure)
    {φ : ℂ → ℝ} (s : ContDiff ℝ ∞ φ) (h : HasCompactSupport φ) (d : ℂ) :
    (∫ z, v z*fderiv ℝ φ z d) = -(∫ z, ⟪u z,d⟫_ℝ * φ z) := by
  let df := fun z => fderiv ℝ φ z d
  have dfc : Continuous df := (s.continuous_fderiv (by simp)).clm_apply continuous_const
  let dm := dfc.memLp_of_hasCompactSupport (μ:=volume) (p:=2) (h.fderiv_apply ℝ d)
  let l := dm.toLp df
  let b := fun z => φ z • d
  have bc : Continuous b := s.continuous.smul continuous_const
  have bs : HasCompactSupport b := h.smul_right
  let bm := bc.memLp_of_hasCompactSupport (μ:=volume) (p:=2) bs
  let t := bm.toLp b
  have left (a : Lp ℝ 2 (volume:Measure ℂ)) : ⟪a,l⟫_ℝ=(∫ z, a z*df z) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dm.coeFn_toLp] with z hz
    change ⟪a z,l z⟫_ℝ=_
    rw [hz,Real.inner_apply,mul_comm]
  have right (a : Lp ℂ 2 (volume:Measure ℂ)) : ⟪a,t⟫_ℝ=(∫ z, ⟪a z,d⟫_ℝ * φ z) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [bm.coeFn_toLp] with z hz
    change ⟪a z,t z⟫_ℝ=_
    rw [hz]
    change ⟪a z,φ z • d⟫_ℝ=_
    rw [real_inner_smul_right,mul_comm]
  have closed : IsClosed {x : Lp ℝ 2 (volume:Measure ℂ) × Lp ℂ 2 (volume:Measure ℂ) |
        ⟪x.1,l⟫_ℝ = -⟪x.2,t⟫_ℝ} :=
    isClosed_eq (continuous_fst.inner continuous_const) (continuous_snd.inner continuous_const).neg
  have smoothPairs : (planeDirichletPairs U : Set (Lp ℝ 2 (volume:Measure ℂ) × Lp ℂ 2 (volume:Measure ℂ))) ⊆ {x | ⟪x.1,l⟫_ℝ = -⟪x.2,t⟫_ℝ} := by
    rintro x ⟨ψ,sm,cm,_,ex,eg⟩
    change ⟪x.1,l⟫_ℝ = -⟪x.2,t⟫_ℝ
    rw [left,right]
    have l1 : (∫ z, x.1 z*df z)=(∫ z, ψ z*df z) := integral_congr_ae (ex.mono fun z hz => congrArg (fun a : ℝ => a*df z) hz)
    have l2 : (∫ z, ⟪x.2 z,d⟫_ℝ*φ z)=(∫ z, fderiv ℝ ψ z d*φ z) :=
      integral_congr_ae (eg.mono fun z hz => by
        change ⟪x.2 z,d⟫_ℝ*φ z=fderiv ℝ ψ z d*φ z
        rw [hz,planeTestGradient_pair])
    rw [l1,l2]
    have cψ : Continuous (fun z => fderiv ℝ ψ z d) := (sm.continuous_fderiv (by simp)).clm_apply continuous_const
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((cψ.mul s.continuous).integrable_of_hasCompactSupport h.mul_left)
      ((sm.continuous.mul dfc).integrable_of_hasCompactSupport cm.mul_right)
      ((sm.continuous.mul s.continuous).integrable_of_hasCompactSupport cm.mul_right)
      (fun z _ => sm.differentiable (by simp) z) (fun z _ => s.differentiable (by simp) z)
  have eq := closure_minimal smoothPairs closed pair
  change ⟪v,l⟫_ℝ = -⟪u,t⟫_ℝ at eq
  simpa only [left,right] using eq
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_compact_derivative_integral_zero
#print axioms TwoAxisHelicoid.disk_potential_distributional_derivative
