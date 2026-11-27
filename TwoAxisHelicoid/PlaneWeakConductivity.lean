module

public import TwoAxisHelicoid.PlaneConductivityL2
import TwoAxisHelicoid.PlaneConductivityEllipticityBounds
import TwoAxisHelicoid.CoerciveGradientCorrection
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter InnerProductSpace
open scoped RealInnerProductSpace ContDiff

theorem planeMetricFlux_energy (A B C : ℂ → ℝ) (z v : ℂ) :
    ⟪planeMetricFlux A B C z v,v⟫_ℝ=C z*v.re^2-2*B z*v.re*v.im+A z*v.im^2 := by
  simp only [Complex.inner,Complex.mul_re,Complex.conj_re,Complex.conj_im,planeMetricFlux]
  ring

theorem compact_conductivity_operator_coercive (μ : Measure ℂ) {A B C : ℂ → ℝ}
    (sa : Continuous A) (sb : Continuous B) (sc : Continuous C) (ha : ∀ z, 0<A z)
    (det : ∀ z, A z*C z-(B z)^2=1)
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1) :
    ∃ (k : ℝ) (T : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ), 1≤k ∧
      (∀ w : Lp ℂ 2 μ, ⇑(T w) =ᵐ[μ] (fun z => planeMetricFlux A B C z (w z))) ∧
      ∀ w, k⁻¹*‖w‖^2≤⟪T w,w⟫_ℝ := by
  obtain ⟨k,hk1,bounds⟩ := compact_plane_conductivity_uniform_bounds sa sc ha det hk off
  obtain ⟨T,acts⟩ := exists_planeMetricFlux_L2 μ sa sb sc hk off
  refine ⟨k,T,hk1,acts,fun w => ?_⟩
  rw [← real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def,← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner (𝕜:=ℝ) w w).const_mul _) (L2.integrable_inner (𝕜:=ℝ) (T w) w)
  filter_upwards [acts w] with z hz
  rw [hz,real_inner_self_eq_norm_sq,planeMetricFlux_energy]
  have length : ‖w z‖^2=(w z).re^2+(w z).im^2 := by linarith [Complex.sq_norm_sub_sq_re (w z)]
  rw [length,mul_comm,←div_eq_mul_inv]
  exact (bounds z (w z).re (w z).im).1

/-- The real derivative of a scalar test function, in the two Euclidean directions. -/
@[expose] noncomputable def planeTestGradient (φ : ℂ → ℝ) (z : ℂ) : ℂ := ⟨fderiv ℝ φ z 1,fderiv ℝ φ z I⟩

theorem planeTestGradient_memLp {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] {φ : ℂ → ℝ}
    (smooth : ContDiff ℝ ∞ φ) (compact : HasCompactSupport φ) : MemLp (planeTestGradient φ) 2 μ := by
  have cont : Continuous (planeTestGradient φ) := by
    change Continuous (Complex.equivRealProdCLM.symm ∘ (fun z : ℂ => (fderiv ℝ φ z 1,fderiv ℝ φ z I)))
    apply Complex.equivRealProdCLM.symm.continuous.comp
    exact ((smooth.continuous_fderiv (by simp)).clm_apply continuous_const).prodMk
      ((smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  apply cont.memLp_of_hasCompactSupport
  apply compact.mono'
  intro z hz
  by_contra outside
  apply hz
  apply Complex.ext <;> simp [planeTestGradient,fderiv_of_notMem_tsupport ℝ outside]

/-- Closed space of zero-boundary test gradients, with approximation in the physical L² norm. -/
@[expose] noncomputable def planeDirichletGradients (μ : Measure ℂ) (U : Set ℂ) : Submodule ℝ (Lp ℂ 2 μ) :=
  (Submodule.span ℝ {g : Lp ℂ 2 μ | ∃ φ : ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ U ∧ ⇑g =ᵐ[μ] planeTestGradient φ}).topologicalClosure

/-- An actual weak Dirichlet flux exists on every open domain, for arbitrary L²
background data and the original pointwise conductivity. Every smooth compactly
supported scalar test function satisfies the divergence equation. -/
theorem exists_plane_weak_conductivity {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {A B C : ℂ → ℝ} (sa : Continuous A) (sb : Continuous B) (sc : Continuous C)
    (ha : ∀ z, 0<A z) (det : ∀ z, A z*C z-(B z)^2=1)
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1)
    (U : Set ℂ) (e : Lp ℂ 2 μ) :
    ∃ u ∈ planeDirichletGradients μ U, ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      ∫ z, ⟪planeMetricFlux A B C z (e z+u z),planeTestGradient φ z⟫_ℝ ∂μ=0 := by
  obtain ⟨k,T,h1,acts,lower⟩ := compact_conductivity_operator_coercive μ sa sb sc ha det hk off
  let S := planeDirichletGradients μ U
  have closed : IsClosed (S : Set (Lp ℂ 2 μ)) := Submodule.isClosed_topologicalClosure _
  have kp : 0<k := by linarith
  obtain ⟨u,sol,_⟩ := unique_coercive_gradient_correction S closed T (inv_pos.mpr kp) lower e
  refine ⟨u,u.2,?_⟩
  intro φ smooth compact inside
  let m := planeTestGradient_memLp (μ:=μ) smooth compact
  let v := m.toLp (planeTestGradient φ)
  have vm : v∈S := Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨φ,smooth,compact,inside,m.coeFn_toLp⟩)
  have eq := sol ⟨v,vm⟩
  rw [L2.inner_def] at eq
  refine (integral_congr_ae ?_).trans eq
  filter_upwards [acts (e+(u:Lp ℂ 2 μ)),Lp.coeFn_add e (u:Lp ℂ 2 μ),m.coeFn_toLp] with z hz he hv
  change ⟪_,_⟫_ℝ=⟪T (e+(u:Lp ℂ 2 μ)) z,v z⟫_ℝ
  rw [hz,he,hv]
  rfl
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_conductivity_operator_coercive
#print axioms TwoAxisHelicoid.exists_plane_weak_conductivity
