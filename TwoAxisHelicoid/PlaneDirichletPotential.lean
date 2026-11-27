import TwoAxisHelicoid.ClosedGradientGraph
import TwoAxisHelicoid.PlaneDirichletPoincare

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Metric Filter InnerProductSpace
open scoped ContDiff RealInnerProductSpace

private theorem testGradient_zero : planeTestGradient (0:ℂ→ℝ)=0 := by
  funext z
  apply Complex.ext <;> simp [planeTestGradient]

private theorem testGradient_add {φ ψ : ℂ → ℝ} (s : ContDiff ℝ ∞ φ) (t : ContDiff ℝ ∞ ψ) (z : ℂ) :
    planeTestGradient (φ+ψ) z=planeTestGradient φ z+planeTestGradient ψ z := by
  apply Complex.ext <;> simp [planeTestGradient,fderiv_add (s.differentiable (by simp) z) (t.differentiable (by simp) z)]

private theorem testGradient_smul (c : ℝ) (φ : ℂ → ℝ) (z : ℂ) :
    planeTestGradient (c • φ) z=c • planeTestGradient φ z := by
  apply Complex.ext <;> simp [planeTestGradient,fderiv_const_smul_field]

/-- Pairs of scalar test functions and their actual Euclidean gradients. -/
noncomputable def planeDirichletPairs (U : Set ℂ) : Submodule ℝ (Lp ℝ 2 (volume:Measure ℂ) × Lp ℂ 2 (volume:Measure ℂ)) where
  carrier := {x | ∃ φ : ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
    ⇑x.1 =ᵐ[volume] φ ∧ ⇑x.2 =ᵐ[volume] planeTestGradient φ}
  zero_mem' := by
    refine ⟨0,contDiff_const,(by simp [HasCompactSupport]),by simp,Lp.coeFn_zero _ _ _,?_⟩
    rw [testGradient_zero]
    exact Lp.coeFn_zero _ _ _
  add_mem' := by
    rintro x y ⟨φ,s,h,inside,fx,gx⟩ ⟨ψ,t,k,inψ,fy,gy⟩
    refine ⟨φ+ψ,s.add t,h.add k,(tsupport_add φ ψ).trans (union_subset inside inψ),?_,?_⟩
    · filter_upwards [Lp.coeFn_add x.1 y.1,fx,fy] with z add left right
      change (x.1+y.1) z=φ z+ψ z
      simp only [add,Pi.add_apply,left,right]
    · filter_upwards [Lp.coeFn_add x.2 y.2,gx,gy] with z add left right
      change (x.2+y.2) z=_
      rw [add,Pi.add_apply,left,right,testGradient_add s t]
  smul_mem' := by
    rintro c x ⟨φ,s,h,inside,fx,gx⟩
    refine ⟨c • φ,s.const_smul c,h.smul_left,(tsupport_smul_subset_right (fun _ : ℂ => c) φ).trans inside,?_,?_⟩
    · filter_upwards [Lp.coeFn_smul c x.1,fx] with z smul hv
      change (c • x.1) z=c • φ z
      rw [smul,Pi.smul_apply,hv]
    · filter_upwards [Lp.coeFn_smul c x.2,gx] with z smul hv
      change (c • x.2) z=_
      rw [smul,Pi.smul_apply,hv,testGradient_smul]

/-- L² limits of compactly supported gradients on an actual disk carry
a unique zero-boundary Sobolev potential. -/
theorem exists_unique_disk_potential (p : ℂ) (r : ℝ) {u : Lp ℂ 2 (volume:Measure ℂ)}
    (hu : u∈planeDirichletGradients volume (ball p r)) :
    ∃! v : Lp ℝ 2 (volume:Measure ℂ), (v,u)∈(planeDirichletPairs (ball p r)).topologicalClosure := by
  let U := ball p r
  let G := planeDirichletPairs U
  obtain ⟨D,_,est⟩ := disk_test_poincare p r
  apply lift_from_closed_gradient_graph G (D:=D)
  · rintro x ⟨φ,s,h,inside,fx,gx⟩
    have e := est φ s h inside
    have ex : x.1=(s.continuous.memLp_of_hasCompactSupport (μ:=volume) (p:=2) h).toLp φ :=
      Lp.ext (fx.trans (MemLp.coeFn_toLp _).symm)
    have eg : x.2=(planeTestGradient_memLp (μ:=volume) s h).toLp (planeTestGradient φ) :=
      Lp.ext (gx.trans (MemLp.coeFn_toLp _).symm)
    rwa [ex,eg]
  · apply Submodule.topologicalClosure_mono _ hu
    apply Submodule.span_le.mpr
    rintro g ⟨φ,s,h,inside,hg⟩
    let a := (s.continuous.memLp_of_hasCompactSupport (μ:=volume) (p:=2) h).toLp φ
    exact ⟨(a,g),⟨φ,s,h,inside,(s.continuous.memLp_of_hasCompactSupport (μ:=volume) (p:=2) h).coeFn_toLp,hg⟩,rfl⟩

/-- Weak affine Dirichlet data for the original metric on a disk.
The scalar correction and its gradient are a common W¹,² limit of compactly
supported smooth functions. The flux equation holds against every test. -/
theorem exists_affine_disk_weak_solution {A B C : ℂ → ℝ}
    (sa : Continuous A) (sb : Continuous B) (sc : Continuous C) (ha : ∀ z, 0<A z)
    (det : ∀ z, A z*C z-(B z)^2=1)
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1)
    (p : ℂ) (r : ℝ) :
    ∃ (v : Lp ℝ 2 (volume:Measure ℂ)) (u : Lp ℂ 2 (volume:Measure ℂ)),
      (v,u)∈(planeDirichletPairs (ball p r)).topologicalClosure ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball p r →
        (∫ z, ⟪planeMetricFlux A B C z (1+u z),planeTestGradient φ z⟫_ℝ) = 0 := by
  let U := ball p r
  let e : Lp ℂ 2 (volume:Measure ℂ) := indicatorConstLp 2 (isOpen_ball (x:=p) (ε:=r)).measurableSet measure_ball_lt_top.ne 1
  obtain ⟨u,hu,sol⟩ := exists_plane_weak_conductivity sa sb sc ha det hk off U e
  obtain ⟨v,hv,_⟩ := exists_unique_disk_potential p r hu
  refine ⟨v,u,hv,?_⟩
  intro φ s h inside
  refine (integral_congr_ae ?_).trans (sol φ s h inside)
  have one : ∀ᵐ z : ℂ, z∈U → e z=1 := indicatorConstLp_coeFn_mem
  filter_upwards [one] with z eq
  by_cases hz : z∈U
  · rw [eq hz]
  · have out : z∉tsupport φ := fun h => hz (inside h)
    have zero : planeTestGradient φ z=0 := by
      apply Complex.ext <;> simp [planeTestGradient,fderiv_of_notMem_tsupport ℝ out]
    simp only [zero,inner_zero_right]
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_unique_disk_potential
#print axioms TwoAxisHelicoid.exists_affine_disk_weak_solution
