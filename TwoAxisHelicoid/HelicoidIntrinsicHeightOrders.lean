import TwoAxisHelicoid.PuncturedMetricGrowth
import TwoAxisHelicoid.HelicoidProjectedMetricGerm
import TwoAxisHelicoid.HelicoidNaturalPuncture
import TwoAxisHelicoid.HelicoidPolynomialHeightOrders

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology OnePoint

/-- Polynomial growth of the natural exterior graph parameter in an
actual compactifying isothermal coordinate. This is obtained from the
two-dimensional area distortion estimate applied to the inverse chart. -/
theorem HasHelicoidC1End.natural_parameter_polynomial_growth {M : Type*} [TopologicalSpace M]
    [T2Space M] [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (proper : IsProperMap X)
    (E : PuncturedComplexEnd M)
    (smooth : ∀ᶠ z in 𝓝[≠] (0:ℂ), ContDiffAt ℝ 1 (X ∘ E.coord.symm) z)
    (iso : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∃ c : ℝ, 0<c ∧ ∀ v : ℂ,
      (∑ j, (tubeCartesian (fderiv ℝ (X ∘ E.coord.symm) z v) j)^2)=c*‖v‖^2) :
    ∃ N : ℕ, 0<N ∧ ∃ C : ℝ, 0<C ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ),
      ‖helicoidProjectedComplexParameter (X (E.coord.symm z))‖≤C/‖z‖^N ∧
      |(X (E.coord.symm z)).2|≤(C+1)/‖z‖^N := by
  obtain ⟨D,actual⟩ := graph.natural_puncture_coordinate proper
  let e := E.filledChart.symm.trans D.filledChart
  have src : (0:ℂ)∈e.source := by
    refine ⟨mem_ball_self E.radius_pos,?_⟩
    change E.filledInverse 0∈(OnePoint.some '' D.coord.sourceᶜ)ᶜ
    simp [PuncturedComplexEnd.filledInverse]
  have fix : e 0=0 := by change (E.filledInverse 0).elim 0 D.coord=0; simp [PuncturedComplexEnd.filledInverse]
  let P := fun z => helicoidProjectedComplexParameter (X (E.coord.symm z))
  have eq : (e : ℂ → ℂ) =ᶠ[𝓝[≠] (0:ℂ)] fun z => (P z)⁻¹ := by
    filter_upwards [E.from_zero.eventually actual,self_mem_nhdsWithin] with z h hz
    change (E.filledInverse z).elim 0 D.coord=(P z)⁻¹
    rw [PuncturedComplexEnd.filledInverse,ite_eq_right (show z≠0 from hz)]
    exact h.1
  have mt := graph.reciprocal_projection_metric proper E smooth iso
  obtain ⟨N,hN,C,hC,growth⟩ := reciprocal_growth_of_punctured_metric e src fix (by
    filter_upwards [punctured_germ_eventually_local eq,mt] with z same h
    obtain ⟨reg,m,c,hm,hc,metric⟩ := h
    refine ⟨reg.congr_of_eventuallyEq same,m,c,hm,hc,?_⟩
    rw [same.fderiv_eq]
    exact metric)
  refine ⟨N,hN,C,hC,?_⟩
  filter_upwards [eq,growth,E.from_zero.eventually actual,self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one)] with z he hb hg nz small
  rw [he,inv_inv] at hb
  refine ⟨hb,?_⟩
  have ht : |(X (E.coord.symm z)).2|≤‖P z‖+1 := by
    have b := abs_add_le ((X (E.coord.symm z)).2-(P z).im) (P z).im
    rw [sub_add_cancel] at b
    exact b.trans (by linarith [hg.2,Complex.abs_im_le_norm (P z)])
  have nn := pow_pos (norm_pos_iff.mpr nz) N
  have s : ‖z‖<1 := by simpa only [mem_ball,dist_zero_right] using small
  have u : ‖z‖^N≤1 := pow_le_one₀ (norm_nonneg _) s.le
  rw [le_div_iff₀ nn] at hb ⊢
  calc
    _ ≤ (‖P z‖+1)*‖z‖^N := mul_le_mul_of_nonneg_right ht nn.le
    _ ≤ _ := by nlinarith

/-- The exact double pole of the height differential for a proper C¹
helicoidal graph marked by a compactifying isothermal chart and a
single-valued holomorphic height primitive on the puncture. -/
theorem HasHelicoidC1End.intrinsic_height_orders {M : Type*} [TopologicalSpace M]
    [T2Space M] [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (proper : IsProperMap X)
    (E : PuncturedComplexEnd M)
    (smooth : ∀ᶠ z in 𝓝[≠] (0:ℂ), ContDiffAt ℝ 1 (X ∘ E.coord.symm) z)
    (iso : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∃ c : ℝ, 0<c ∧ ∀ v : ℂ,
      (∑ j, (tubeCartesian (fderiv ℝ (X ∘ E.coord.symm) z v) j)^2)=c*‖v‖^2)
    {H : ℂ → ℂ} {b : ℝ}
    (height : ∀ᶠ z in 𝓝[≠] (0:ℂ), (X (E.coord.symm z)).2=(H z).re+b)
    (diff : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ H z) :
    MeromorphicAt H 0 ∧ meromorphicOrderAt H 0=((-1:ℤ):WithTop ℤ) ∧
      MeromorphicAt (deriv H) 0 ∧ meromorphicOrderAt (deriv H) 0=((-2:ℤ):WithTop ℤ) := by
  obtain ⟨N,_,C,hC,bd⟩ := graph.natural_parameter_polynomial_growth proper E smooth iso
  exact graph.polynomial_height_orders proper.continuous E height diff
    ⟨N,C+1,by linarith,bd.mono fun _ h => h.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.intrinsic_height_orders
