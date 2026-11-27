import TwoAxisHelicoid.PlaneWeakIntegrationByParts

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter Metric InnerProductSpace
open scoped ContDiff RealInnerProductSpace

/-- A constant gradient field restricted to a disk, in the ambient L² space. -/
noncomputable def diskConstantVector (p : ℂ) (r : ℝ) (c : ℂ) : Lp ℂ 2 (volume:Measure ℂ) :=
  indicatorConstLp 2 (isOpen_ball (x:=p) (ε:=r)).measurableSet measure_ball_lt_top.ne c

theorem diskConstantVector_ae (p : ℂ) (r : ℝ) (c : ℂ) :
    ⇑(diskConstantVector p r c) =ᵐ[volume] (ball p r).indicator (fun _ => c) :=
  indicatorConstLp_coeFn

private theorem flux_orth_of_tests {U : Set ℂ} (q : Lp ℂ 2 (volume:Measure ℂ))
    (test : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, ⟪q z,planeTestGradient φ z⟫_ℝ) = 0) :
    ∀ v ∈ planeDirichletGradients volume U, ⟪q,v⟫_ℝ=0 := by
  let L := innerSL ℝ q
  have incl : planeDirichletGradients volume U ≤ L.ker := by
    apply Submodule.topologicalClosure_minimal _ _ L.isClosed_ker
    apply Submodule.span_le.mpr
    rintro w ⟨φ,s,h,inside,hw⟩
    change ⟪q,w⟫_ℝ=0
    rw [L2.inner_def]
    refine (integral_congr_ae ?_).trans (test φ s h inside)
    filter_upwards [hw] with z hz
    change ⟪q z,w z⟫_ℝ=_
    rw [hz]
  exact fun _ hv => incl hv

theorem disk_constant_flux_orthogonal (p : ℂ) (r : ℝ) (q : ℂ) :
    ∀ v ∈ planeDirichletGradients volume (ball p r), ⟪diskConstantVector p r q,v⟫_ℝ=0 := by
  apply flux_orth_of_tests
  intro φ s h inside
  refine (integral_congr_ae ?_).trans (plane_compact_derivative_integral_zero s h q)
  filter_upwards [diskConstantVector_ae p r q] with z hv
  rw [hv]
  by_cases hz : z∈ball p r
  · rw [indicator_of_mem hz,real_inner_comm,planeTestGradient_pair]
  · have out : z∉tsupport φ := fun m => hz (inside m)
    rw [indicator_of_notMem hz,inner_zero_left,fderiv_of_notMem_tsupport ℝ out]
    rfl

/-- Freezing the conductivity at the center of a shrinking disk gives
an arbitrarily small *relative* L² gradient error for affine Dirichlet data. -/
theorem exists_disk_weak_solution_near_affine {A B C : ℂ → ℝ}
    (sa : Continuous A) (sb : Continuous B) (sc : Continuous C) (ha : ∀ z, 0<A z)
    (det : ∀ z, A z*C z-(B z)^2=1)
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1)
    (p : ℂ) {ε : ℝ} (heps : 0<ε) :
    ∃ R : ℝ, 0<R ∧ ∀ r ∈ Ioo (0:ℝ) R,
      ∃ (v : Lp ℝ 2 (volume:Measure ℂ)) (u : Lp ℂ 2 (volume:Measure ℂ)),
        (v,u)∈(planeDirichletPairs (ball p r)).topologicalClosure ∧
        ‖u‖≤ε*‖diskConstantVector p r 1‖ ∧
        ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball p r →
          (∫ z, ⟪planeMetricFlux A B C z (1+u z),planeTestGradient φ z⟫_ℝ) = 0 := by
  obtain ⟨k,T,h1,acts,lower⟩ := compact_conductivity_operator_coercive volume sa sb sc ha det hk off
  have kp : 0<k := by linarith
  let δ := ε*k⁻¹
  have dp : 0<δ := mul_pos heps (inv_pos.mpr kp)
  let f := fun z => planeMetricFlux A B C z 1
  have fc : Continuous f := by
    change Continuous (Complex.equivRealProdCLM.symm ∘ (fun z : ℂ =>
      (C z*(1:ℂ).re-B z*(1:ℂ).im,A z*(1:ℂ).im-B z*(1:ℂ).re)))
    apply Complex.equivRealProdCLM.symm.continuous.comp
    apply Continuous.prodMk <;> fun_prop (disch := assumption)
  obtain ⟨R,hR,osc⟩ := Metric.continuousAt_iff.mp (fc.continuousAt (x:=p)) δ dp
  refine ⟨R,hR,?_⟩
  intro r hr
  let e := diskConstantVector p r 1
  let b := diskConstantVector p r (f p)
  let S := planeDirichletGradients volume (ball p r)
  have est : ‖b-T e‖≤δ*‖e‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub b (T e),acts e,diskConstantVector_ae p r 1,diskConstantVector_ae p r (f p)]
      with z hz act he hb
    change ‖(b-T e) z‖≤δ*‖e z‖
    rw [hz,Pi.sub_apply,act,he,hb]
    by_cases inside : z∈ball p r
    · simp only [indicator_of_mem inside,norm_one,mul_one]
      have small := osc (lt_trans (mem_ball.mp inside) hr.2)
      simpa only [dist_comm (f z) (f p),dist_eq_norm] using small.le
    · simp only [indicator_of_notMem inside,norm_zero,mul_zero]
      have zero : planeMetricFlux A B C z 0=0 := by apply Complex.ext <;> simp [planeMetricFlux]
      simp only [zero,sub_zero,norm_zero,le_refl]
  have closed : IsClosed (S : Set (Lp ℂ 2 (volume:Measure ℂ))) := Submodule.isClosed_topologicalClosure _
  obtain ⟨u,sol,_⟩ := unique_coercive_gradient_correction S closed T (inv_pos.mpr kp) lower e
  obtain ⟨v,hv,_⟩ := exists_unique_disk_potential p r u.2
  have err := (coercive_gradient_correction_bound S T lower e b
    (fun w => disk_constant_flux_orthogonal p r (f p) w w.2) u sol).trans est
  refine ⟨v,u,hv,?_,?_⟩
  · calc
      ‖(u:Lp ℂ 2 (volume:Measure ℂ))‖ = k*(k⁻¹*‖(u:Lp ℂ 2 (volume:Measure ℂ))‖) := by field_simp
      _ ≤ k*(δ*‖e‖) := mul_le_mul_of_nonneg_left err kp.le
      _ = ε*‖e‖ := by dsimp only [δ]; field_simp
  · intro φ s h inside
    let m := planeTestGradient_memLp (μ:=volume) s h
    let w := m.toLp (planeTestGradient φ)
    have hw : w∈S := Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨φ,s,h,inside,m.coeFn_toLp⟩)
    have eq := sol ⟨w,hw⟩
    rw [L2.inner_def] at eq
    refine (integral_congr_ae ?_).trans eq
    filter_upwards [acts (e+(u:Lp ℂ 2 (volume:Measure ℂ))),Lp.coeFn_add e (u:Lp ℂ 2 (volume:Measure ℂ)),
      m.coeFn_toLp,diskConstantVector_ae p r 1] with z hz hadd hwv he
    change ⟪_,_⟫_ℝ=⟪T (e+(u:Lp ℂ 2 (volume:Measure ℂ))) z,w z⟫_ℝ
    rw [hz,hadd,Pi.add_apply,hwv,he]
    by_cases hzin : z∈ball p r
    · rw [indicator_of_mem hzin]
    · have out : z∉tsupport φ := fun hh => hzin (inside hh)
      have zero : planeTestGradient φ z=0 := by
        apply Complex.ext <;> simp [planeTestGradient,fderiv_of_notMem_tsupport ℝ out]
      simp only [zero,inner_zero_right]
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.disk_constant_flux_orthogonal
#print axioms TwoAxisHelicoid.exists_disk_weak_solution_near_affine
