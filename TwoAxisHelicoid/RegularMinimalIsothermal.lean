import TwoAxisHelicoid.MinimalSurfaceGraphChart
import TwoAxisHelicoid.MinimalChartComplexData

namespace TwoAxisHelicoid
open Complex Matrix Filter Set InnerProductSpace
open scoped Topology ContDiff
set_option maxHeartbeats 1400000

theorem openPartialHomeomorph_deriv_right_inverse (e : OpenPartialHomeomorph ℂ ℂ)
    {y : ℂ} (hy : y ∈ e.target) (hf : DifferentiableAt ℝ e (e.symm y))
    (hg : DifferentiableAt ℝ e.symm y) (v : ℂ) :
    fderiv ℝ e (e.symm y) (fderiv ℝ e.symm y v) = v := by
  have h : ((e : ℂ → ℂ) ∘ e.symm) =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with w hw
    exact e.right_inv hw
  have hd := h.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp y hf hg,fderiv_id] at hd
  exact congrArg (fun D : ℂ →L[ℝ] ℂ => D v) hd

/-- An arbitrary regular C² minimal parametrization admits an actual
local isothermal reparametrization with positive metric factor. -/
theorem regular_minimal_isothermal_chart {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z) (hi : Function.Injective (fderiv ℝ X z))
    (hm : ∀ᶠ w in 𝓝 z, coordinateMeanCurvature X w = 0) :
    ∃ k : OpenPartialHomeomorph ℂ ℂ, z ∈ k.source ∧ ContDiffAt ℝ 2 k z ∧
      ContDiffAt ℝ 2 k.symm (k z) ∧ ∀ᶠ y in 𝓝 (k z), ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ,
        (fderiv ℝ (X ∘ k.symm) y v) ⬝ᵥ (fderiv ℝ (X ∘ k.symm) y v) = c*normSq v := by
  obtain ⟨σ,e,u,r,hr,hz,he,hes,hgraph,hball⟩ := regular_minimal_surface_graph_chart hX hi hm
  let U := Metric.ball (e z) r
  have hU : e z ∈ U := Metric.mem_ball_self hr
  obtain ⟨c,hc,hce,hcs,hmetric⟩ := minimal_graph_isothermal_chart Metric.isOpen_ball (convex_ball _ _)
    (fun w hw => (hball w hw).2.1) (fun w hw => (hball w hw).2.2) hU
  let k := e.trans c
  have hk : z ∈ k.source := ⟨hz,hc⟩
  have hki : ContDiffAt ℝ 2 k.symm (k z) := by
    have hes' : ContDiffAt ℝ 2 e.symm (c.symm (c (e z))) := (c.left_inv hc).symm ▸ hes
    exact hes'.comp _ hcs
  refine ⟨k,hk,hce.comp _ he,hki,?_⟩
  have hY : ContDiffAt ℝ 2 (X ∘ e.symm) (e z) := by
    exact ((e.left_inv hz).symm ▸ hX : ContDiffAt ℝ 2 X (e.symm (e z))).comp _ hes
  have ht := c.tendsto_symm hc
  change ∀ᶠ y in 𝓝 (c (e z)), _
  filter_upwards [c.open_target.mem_nhds (c.map_source hc),hcs.eventually (by norm_num),
    ht.eventually (hce.eventually (by norm_num)),ht.eventually (hY.eventually (by norm_num)),
    ht.eventually (Metric.isOpen_ball.mem_nhds hU)] with y hy hd he' hY' hb
  let w := c.symm y
  obtain ⟨g,hg,hmw⟩ := hmetric w hb
  refine ⟨g,hg,?_⟩
  intro v
  let v' := fderiv ℝ c.symm y v
  have hh := graph_projection_chart_metric σ e hgraph (hball w hb).1
    ((hball w hb).2.1.differentiableAt two_ne_zero) (hY'.differentiableAt two_ne_zero) v'
  change fderiv ℝ ((X ∘ e.symm) ∘ c.symm) y v ⬝ᵥ fderiv ℝ ((X ∘ e.symm) ∘ c.symm) y v = _
  rw [fderiv_comp y (hY'.differentiableAt two_ne_zero) (hd.differentiableAt two_ne_zero)]
  change fderiv ℝ (X ∘ e.symm) w v' ⬝ᵥ fderiv ℝ (X ∘ e.symm) w v' = _
  rw [hh,hmw]
  have hInv := openPartialHomeomorph_deriv_right_inverse c hy (he'.differentiableAt two_ne_zero)
    (hd.differentiableAt two_ne_zero) v
  rw [show fderiv ℝ c w v' = v from hInv]

theorem conformal_immersion_of_metric_factor (L : ℂ →L[ℝ] (Fin 3 → ℝ)) {c : ℝ} (hc : 0 < c)
    (hm : ∀ v, L v ⬝ᵥ L v = c*normSq v) :
    L 1 ⬝ᵥ L 1 = L I ⬝ᵥ L I ∧ L 1 ⬝ᵥ L I = 0 ∧ Function.Injective L := by
  have h₁ : L 1 ⬝ᵥ L 1 = c := by simpa using hm 1
  have hI : L I ⬝ᵥ L I = c := by simpa using hm I
  have hsum := hm (1+I)
  rw [map_add,add_dotProduct,dotProduct_add,dotProduct_add,dotProduct_comm (L I) (L 1),h₁,hI] at hsum
  have hs : normSq (1+I) = 2 := by norm_num [Complex.normSq_apply]
  rw [hs] at hsum
  refine ⟨h₁.trans hI.symm,by linarith,(injective_iff_map_eq_zero _).mpr ?_⟩
  intro v hv
  have hv' := hm v
  rw [hv,zero_dotProduct] at hv'
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hv'.symm).resolve_left hc.ne')

/-- The Weierstrass differential of the surface in isothermal coordinates
is derived from a regular minimal C² chart in arbitrary real parameters. -/
theorem regular_minimal_chart_actual_complex_data {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z) (hi : Function.Injective (fderiv ℝ X z))
    (hm : ∀ᶠ w in 𝓝 z, coordinateMeanCurvature X w = 0) :
    ∃ k : OpenPartialHomeomorph ℂ ℂ, z ∈ k.source ∧ ContDiffAt ℝ 2 k z ∧
      ContDiffAt ℝ 2 k.symm (k z) ∧
      (∀ᶠ y in 𝓝 (k z), ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ,
        fderiv ℝ (X ∘ k.symm) y v ⬝ᵥ fderiv ℝ (X ∘ k.symm) y v = c*normSq v) ∧
      HarmonicAt (X ∘ k.symm) (k z) ∧
      (∀ j, AnalyticAt ℂ (fun w => immersionComplexCoefficient (X ∘ k.symm) w j) (k z)) ∧
      ComplexNull (immersionComplexCoefficient (X ∘ k.symm) (k z)) ∧
      immersionComplexCoefficient (X ∘ k.symm) (k z) ≠ 0 ∧
      HasFDerivAt (X ∘ k.symm) (nullRealDerivative (immersionComplexCoefficient (X ∘ k.symm) (k z))) (k z) := by
  obtain ⟨k,hz,hk,hs,hm'⟩ := regular_minimal_isothermal_chart hX hi hm
  have ht := k.tendsto_symm hz
  have hY : ContDiffAt ℝ 2 (X ∘ k.symm) (k z) :=
    ((k.left_inv hz).symm ▸ hX : ContDiffAt ℝ 2 X (k.symm (k z))).comp _ hs
  have hh : ∀ᶠ y in 𝓝 (k z), ConformalCoordinateDerivatives (X ∘ k.symm) y ∧
      Function.Injective (fderiv ℝ (X ∘ k.symm) y) := by
    filter_upwards [hm',hY.eventually (by norm_num)] with y hy hc
    obtain ⟨c,hc',hg⟩ := hy
    obtain ⟨ha,hb,hi'⟩ := conformal_immersion_of_metric_factor _ hc' hg
    exact ⟨(conformalCoordinateDerivatives_iff_dot (hc.differentiableAt two_ne_zero)).mpr ⟨ha,hb⟩,hi'⟩
  have hzero : ∀ᶠ y in 𝓝 (k z), coordinateMeanCurvature (X ∘ k.symm) y = 0 := by
    filter_upwards [ht.eventually hm,ht.eventually (hX.eventually (by norm_num)),hs.eventually (by norm_num)]
      with y hy hxw hsw
    exact minimal_surface_reparametrization hxw hsw hy
  exact ⟨k,hz,hk,hs,hm',conformal_minimal_chart_harmonicAt hY (hh.mono fun _ h => h.1)
    (hh.mono fun _ h => h.2) hzero,minimal_chart_actual_complex_data hY
    (hh.mono fun _ h => h.1) (hh.mono fun _ h => h.2) hzero⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_minimal_chart_actual_complex_data
