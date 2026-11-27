import TwoAxisHelicoid.OrientedMinimalHarmonicAtlas
import TwoAxisHelicoid.MinimalChartComplexData
import TwoAxisHelicoid.SurfaceDotLaplacian

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology ContDiff

/-- A real minimal parametrization admits positively oriented local
isothermal coordinates. The original coordinate and its inverse are smooth,
and the new coordinate differential is the actual regular analytic null
differential of the surface. -/
theorem positive_minimal_change_of_coordinates {X : ℂ → Fin 3 → ℝ} {a : ℂ}
    (data : ∀ᶠ z in 𝓝 a, ContDiffAt ℝ ∞ X z ∧ Function.Injective (fderiv ℝ X z) ∧ coordinateMeanCurvature X z=0) :
    ∃ k : OpenPartialHomeomorph ℂ ℂ, a∈k.source ∧
      (∀ᶠ z in 𝓝 a, ContDiffAt ℝ ∞ k z ∧ 0<planeRealJacobian (fderiv ℝ k z)) ∧
      (∀ᶠ w in 𝓝 (k a), ContDiffAt ℝ ∞ k.symm w) ∧
      let Y := X ∘ k.symm
      ∀ᶠ w in 𝓝 (k a), (∀ j, AnalyticAt ℂ (fun u => immersionComplexCoefficient Y u j) w) ∧
        ComplexNull (immersionComplexCoefficient Y w) ∧ immersionComplexCoefficient Y w≠0 ∧
        HasFDerivAt Y (nullRealDerivative (immersionComplexCoefficient Y w)) w := by
  let V := surfaceTangentCross X a
  have nz : V≠0 := surfaceTangentCross_ne_zero_of_injective data.self_of_nhds.2.1
  have pos : 0<V ⬝ᵥ V := lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (V j))
    (fun h => nz (dotProduct_self_eq_zero.mp h.symm))
  let e := (Homeomorph.refl ℂ).toOpenPartialHomeomorph
  obtain ⟨k,iso,ka⟩ := minimal_patch_oriented_isothermal (e:=e) (F:=X) (N:=fun _ => V) continuous_const
    (show a∈e.source from mem_univ _) (data.self_of_nhds.1.of_le (by norm_num : (2:ℕ∞ω)≤∞))
    data.self_of_nhds.2.1 (data.mono fun _ d => d.2.2) pos.ne'
  let Y := X ∘ k.symm
  have cs := k.continuousAt ka
  have ci := k.tendsto_symm ka
  have identity {z : ℂ} (hz : z∈k.source) : X =ᶠ[𝓝 z] Y ∘ k := by
    filter_upwards [k.open_source.mem_nhds hz] with w hw
    exact congrArg X (k.left_inv hw).symm
  have smooth : ∀ᶠ z in 𝓝 a, ContDiffAt ℝ ∞ k z := by
    filter_upwards [k.open_source.mem_nhds ka,data] with z hz hx
    have hY := iso.1 _ (k.map_source hz)
    exact contDiffAt_of_comp_immersion hY.1 hY.2 (k.continuousAt hz) (hx.1.congr_of_eventuallyEq (identity hz).symm)
  have inverse : ∀ᶠ w in 𝓝 (k a), ContDiffAt ℝ ∞ k.symm w := by
    filter_upwards [ci.eventually data,k.open_target.mem_nhds (k.map_source ka)] with w h hw
    exact contDiffAt_of_comp_immersion h.1 h.2.1 (k.symm.continuousAt hw) (iso.1 w hw).1
  have cv : ContinuousAt (fun z => surfaceTangentCross X z ⬝ᵥ V) a :=
    spatialDotBilinear.continuous₂.continuousAt.comp ((continuousAt_surfaceTangentCross (data.self_of_nhds.1.of_le (by norm_num))).prodMk continuousAt_const)
  have orient : ∀ᶠ z in 𝓝 a, 0<planeRealJacobian (fderiv ℝ k z) := by
    filter_upwards [cv.eventually (Ioi_mem_nhds pos),k.open_source.mem_nhds ka,smooth] with z h hz sk
    have hy := k.map_source hz
    have cross := surfaceTangentCross_coordinate_change (identity hz)
      ((iso.1 _ hy).1.differentiableAt (by simp)) (sk.differentiableAt (by simp))
    change 0<surfaceTangentCross X z ⬝ᵥ V at h
    rw [cross,smul_dotProduct,smul_eq_mul] at h
    exact pos_of_mul_pos_left h (iso.2 _ hy).2.le
  refine ⟨k,ka,smooth.and orient,inverse,?_⟩
  have cy : ∀ᶠ w in 𝓝 (k a), ConformalCoordinateDerivatives Y w ∧ Function.Injective (fderiv ℝ Y w) := by
    filter_upwards [k.open_target.mem_nhds (k.map_source ka)] with w hw
    obtain ⟨c,cp,metric⟩ := (iso.2 w hw).1
    obtain ⟨aa,ab,inj⟩ := conformal_immersion_of_metric_factor _ cp metric
    exact ⟨(conformalCoordinateDerivatives_iff_dot ((iso.1 w hw).1.differentiableAt (by simp))).mpr ⟨aa,ab⟩,inj⟩
  have my : ∀ᶠ w in 𝓝 (k a), coordinateMeanCurvature Y w=0 := by
    filter_upwards [ci.eventually data,inverse] with w hx hi
    exact minimal_surface_reparametrization (hx.1.of_le (by norm_num)) (hi.of_le (by norm_num)) hx.2.2
  filter_upwards [k.open_target.mem_nhds (k.map_source ka),(eventually_eventually_nhds.mpr cy),
    (eventually_eventually_nhds.mpr my)] with w hw cy' my'
  exact minimal_chart_actual_complex_data ((iso.1 w hw).1.of_le (by norm_num)) (cy'.mono fun _ h => h.1)
    (cy'.mono fun _ h => h.2) my'

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positive_minimal_change_of_coordinates

