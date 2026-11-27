import TwoAxisHelicoid.MinimalSurfaceComplexStructure

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1400000

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]

theorem smooth_surface_regular_manifold_chart {F : M → Fin 3 → ℝ}
    (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F x)) (x : M) :
    RegularImmersionChart F (chartAt ℂ x) := by
  intro y hy
  let e := chartAt ℂ x
  have hs := (contMDiffAt_iff_source_of_mem_source (e.map_target hy)).mp (hF (e.symm y))
  have hc : ContDiffAt ℝ ∞ (F ∘ (chartAt ℂ x).symm) y := by
    simpa only [e,mfld_simps,(chartAt ℂ x).right_inv hy,contMDiffWithinAt_univ,
      contMDiffAt_iff_contDiffAt] using hs
  refine ⟨hc,?_⟩
  have hd : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (chartAt ℂ x).symm y := by
    simpa only [mfld_simps,mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ,ℂ)) (x := x) (z := y)
        (by simpa only [mfld_simps] using hy))
  have hcomp := mfderiv_comp y ((hF (e.symm y)).mdifferentiableAt (by simp)) hd
  have hj := (hi (e.symm y)).comp (chart_symm_mfderiv_injective x hy)
  change Function.Injective ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F (e.symm y)).comp
    (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) e.symm y)) at hj
  rw [← hcomp] at hj
  simpa only [mfderiv_eq_fderiv,mfld_simps] using! hj

omit [IsManifold 𝓘(ℝ,ℂ) ∞ M] in
/-- Vanishing of the mean curvature in each point's preferred chart
implies vanishing on every overlap of real immersion charts. -/
theorem minimal_surface_chart_meanCurvature_zero {F : M → Fin 3 → ℝ}
    (hr : ∀ x : M, RegularImmersionChart F (chartAt ℂ x))
    (hm : ∀ x : M, coordinateMeanCurvature (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0)
    {e : OpenPartialHomeomorph M ℂ} (he : RegularImmersionChart F e) {y : ℂ} (hy : y ∈ e.target) :
    coordinateMeanCurvature (F ∘ e.symm) y = 0 := by
  let x := e.symm y
  let d := chartAt ℂ x
  let f := e.symm.trans d
  have hxf : x ∈ d.source := mem_chart_source ℂ x
  have hfy : y ∈ f.source := ⟨hy,hxf⟩
  have hz : f y ∈ d.target := d.map_source hxf
  have h : (F ∘ e.symm) =ᶠ[𝓝 y] ((F ∘ d.symm) ∘ f) := by
    filter_upwards [f.open_source.mem_nhds hfy] with w hw
    exact congrArg F (d.left_inv hw.2).symm
  rw [coordinateMeanCurvature_congr h]
  exact minimal_surface_reparametrization ((hr x _ hz).1.of_le (by norm_num))
    ((regularImmersionChart_transition he (hr x) hfy).of_le (by norm_num)) (hm x)

/-- Starting with an ordinary real smooth surface and its actual
immersive map, the geometric zero-mean-curvature condition at every
point induces a complex analytic atlas compatible with the transverse
orientation. No global conformal parametrization is part of the input. -/
theorem smooth_minimal_manifold_induced_complex_structure {F N : M → Fin 3 → ℝ}
    (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F x)) (hN : Continuous N)
    (hm : ∀ x : M, coordinateMeanCurvature (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0)
    (ho : ∀ x : M, surfaceTangentCross (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ⬝ᵥ N x ≠ 0) :
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ ∀ e ∈ atlas ℂ M, OrientedIsothermalChart F N e := by
  apply minimal_surface_induced_complex_structure hN
  intro x
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hr := smooth_surface_regular_manifold_chart hF hi
  obtain ⟨hc,hinj⟩ := hr x _ (e.map_source hx)
  refine ⟨e,hx,hc.of_le (by norm_num),hinj,?_,ho x⟩
  filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
  exact minimal_surface_chart_meanCurvature_zero hr hm (hr x) hy

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_minimal_manifold_induced_complex_structure
