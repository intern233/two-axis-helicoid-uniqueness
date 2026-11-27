import TwoAxisHelicoid.ChartAvoidingPaths
import TwoAxisHelicoid.DensePeriodExtension
import TwoAxisHelicoid.PuncturedDiskPolygon

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology
set_option maxHeartbeats 1000000

theorem finite_compl_dense_complex_charts {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {P : Set X} (hP : P.Finite) : Dense Pᶜ := by
  apply dense_iff_inter_open.mpr
  intro V hV hne
  obtain ⟨p,hp⟩ := hne
  let e := chartAt ℂ p
  have hW : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.symm.isOpen_inter_preimage hV
  have hep : e p ∈ e.target ∩ e.symm ⁻¹' V :=
    ⟨e.map_source (mem_chart_source ℂ p),by simpa only [mem_preimage,e.left_inv (mem_chart_source ℂ p)] using hp⟩
  obtain ⟨z,hzP,hz⟩ := ((hP.image e).countable.dense_compl ℝ).exists_mem_open hW ⟨e p,hep⟩
  refine ⟨e.symm z,hz.2,?_⟩
  intro h
  exact hzP ⟨e.symm z,h,e.right_inv hz.1⟩

namespace HolomorphicCoefficientDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def chartPoles (P : Set X) (p : X) : Set ℂ :=
  (chartAt ℂ p) '' (P ∩ (chartAt ℂ p).source)

theorem chartPoles_finite {P : Set X} (hP : P.Finite) (p : X) :
    (chartPoles P p).Finite := (hP.inter_of_left _).image _

theorem inverse_mem_domain (A : HolomorphicCoefficientDisks X) (p : X) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) (A.radius p)) :
    (chartAt ℂ p).symm z ∈ A.primitives.domain p := by
  refine ⟨(chartAt ℂ p).map_target (A.ball_target p hz),?_⟩
  change (chartAt ℂ p) ((chartAt ℂ p).symm z) ∈ ball (chartAt ℂ p p) (A.radius p)
  rwa [(chartAt ℂ p).right_inv (A.ball_target p hz)]

theorem chart_regular_iff (A : HolomorphicCoefficientDisks X) (P : Set X) (p : X) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) (A.radius p)) :
    (chartAt ℂ p).symm z ∉ P ↔ z ∉ chartPoles P p := by
  let e := chartAt ℂ p
  constructor
  · intro h
    rintro ⟨x,⟨hxP,hxS⟩,he⟩
    apply h
    rw [← he,e.left_inv hxS]
    exact hxP
  · intro h hp
    exact h ⟨e.symm z,⟨hp,e.map_target (A.ball_target p hz)⟩,
      e.right_inv (A.ball_target p hz)⟩

theorem polygon_lifts_to_avoiding_path (A : HolomorphicCoefficientDisks X)
    (P : Set X) (p : X) {z w : ℂ}
    (c : PlanePolygon (ball (chartAt ℂ p p) (A.radius p) \ chartPoles P p) z w) :
    ∃ d : A.AvoidingPath Pᶜ ((chartAt ℂ p).symm z) ((chartAt ℂ p).symm w),
      d.integral A.coefficient = A.localIntegral p w-A.localIntegral p z := by
  induction c with
  | refl z hz =>
      exact ⟨AvoidingPath.refl _ ((A.chart_regular_iff P p hz.1).mpr hz.2),by
        simp only [AvoidingPath.integral,sub_self]⟩
  | step z w h =>
      have hz : z ∈ ball (chartAt ℂ p p) (A.radius p) \ chartPoles P p := by
        simpa only [AffineMap.lineMap_apply_zero] using h 0 (by norm_num)
      have hw : w ∈ ball (chartAt ℂ p p) (A.radius p) \ chartPoles P p := by
        simpa only [AffineMap.lineMap_apply_one] using h 1 (by norm_num)
      have hez := (chartAt ℂ p).right_inv (A.ball_target p hz.1)
      have hew := (chartAt ℂ p).right_inv (A.ball_target p hw.1)
      have hU (s : ℝ) (hs : s ∈ Icc 0 1) :
          (chartAt ℂ p).symm (chartSegment p ((chartAt ℂ p).symm z)
            ((chartAt ℂ p).symm w) s) ∈ Pᶜ := by
        simp only [chartSegment,hez,hew]
        exact (A.chart_regular_iff P p (h s hs).1).mpr (h s hs).2
      refine ⟨AvoidingPath.step p _ _ (A.inverse_mem_domain p hz.1)
        (A.inverse_mem_domain p hw.1) hU,?_⟩
      change A.segmentIntegral p _ _ = _
      rw [A.segmentIntegral_eq p (A.inverse_mem_domain p hz.1)
        (A.inverse_mem_domain p hw.1),hez,hew]
  | trans c d hc hd =>
      obtain ⟨c',hc'⟩ := hc
      obtain ⟨d',hd'⟩ := hd
      refine ⟨AvoidingPath.trans c' d',?_⟩
      simp only [AvoidingPath.integral,hc',hd']
      ring

theorem regular_chain_lifts_to_avoiding_path {A : HolomorphicCoefficientDisks X}
    {P : Set X} (hP : P.Finite) {x y : X} {r : ℝ}
    (c : A.primitives.RegularChain Pᶜ x y r) :
    ∃ d : A.AvoidingPath Pᶜ x y, (d.integral A.coefficient).re = r := by
  induction c with
  | refl x hx => exact ⟨AvoidingPath.refl x hx,rfl⟩
  | step p x y hx hy hxP hyP =>
      have hx' : (chartAt ℂ p x) ∈
          ball (chartAt ℂ p p) (A.radius p) \ chartPoles P p := by
        refine ⟨hx.2,(A.chart_regular_iff P p hx.2).mp ?_⟩
        simpa only [mem_compl_iff,(chartAt ℂ p).left_inv hx.1] using! hxP
      have hy' : (chartAt ℂ p y) ∈
          ball (chartAt ℂ p p) (A.radius p) \ chartPoles P p := by
        refine ⟨hy.2,(A.chart_regular_iff P p hy.2).mp ?_⟩
        simpa only [mem_compl_iff,(chartAt ℂ p).left_inv hy.1] using! hyP
      obtain ⟨poly⟩ := punctured_disk_polygon_exists (chartAt ℂ p p)
        (A.radius_pos p) (chartPoles_finite hP p) hx' hy'
      obtain ⟨d,hd⟩ := A.polygon_lifts_to_avoiding_path P p poly
      have he : ∃ d : A.AvoidingPath Pᶜ
          ((chartAt ℂ p).symm (chartAt ℂ p x)) ((chartAt ℂ p).symm (chartAt ℂ p y)),
          (d.integral A.coefficient).re = A.primitives.increment p x y := by
        exact ⟨d,by rw [hd]; rfl⟩
      exact (congrArg₂ (fun u v : X => ∃ d : A.AvoidingPath Pᶜ u v,
        (d.integral A.coefficient).re = A.primitives.increment p x y)
        ((chartAt ℂ p).left_inv hx.1) ((chartAt ℂ p).left_inv hy.1)).mp he
  | trans c d hc hd =>
      obtain ⟨c',hc'⟩ := hc
      obtain ⟨d',hd'⟩ := hd
      exact ⟨AvoidingPath.trans c' d',by simp only [AvoidingPath.integral,add_re,hc',hd']⟩

theorem zeroRealPeriods_of_avoiding_finite_poles {A : HolomorphicCoefficientDisks X}
    {P : Set X} (hP : P.Finite) (h : A.ZeroRealAvoidingPeriods Pᶜ A.coefficient) :
    A.ZeroRealPeriods := by
  apply HolomorphicPrimitiveDisks.zeroRealPeriods_of_dense_regular_periods
    (finite_compl_dense_complex_charts hP)
  intro x r c
  obtain ⟨d,hd⟩ := regular_chain_lifts_to_avoiding_path hP c
  exact hd.symm.trans (h x d)

theorem coefficient_zero_on_disks_of_zero_real_periods [CompactSpace X] [PreconnectedSpace X]
    {A : HolomorphicCoefficientDisks X} (hP : A.ZeroRealPeriods) (p : X) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) (A.radius p)) : A.coefficient p z = 0 := by
  have hc := compact_connected_chart_harmonic_constant
    (A.primitives.realPrimitive_continuous hP p) (A.primitives.realPrimitive_harmonic hP p)
  have hconst (w : ℂ) (hw : w ∈ ball (chartAt ℂ p p) (A.radius p)) :
      (A.localIntegral p w).re = (A.localIntegral p (chartAt ℂ p p)).re := by
    have he := A.primitives.realPrimitive_sub hP p p (A.primitives.mem_domain p)
      (A.inverse_mem_domain p hw)
    rw [hc _ p,sub_self] at he
    change 0 = (A.localIntegral p (chartAt ℂ p ((chartAt ℂ p).symm w))).re-
      (A.localIntegral p (chartAt ℂ p p)).re at he
    rw [(chartAt ℂ p).right_inv (A.ball_target p hw)] at he
    linarith
  rw [← (A.localIntegral_hasDerivAt p hz).deriv]
  apply analytic_deriv_zero_of_locally_constant_re (A.localIntegral_analyticAt p hz)
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact (hconst w hw).trans (hconst z hz).symm

/-- Removing finitely many points from the period paths does not weaken
real-period rigidity for a holomorphic differential on a compact curve. -/
theorem zero_of_real_periods_avoiding_finite_poles [CompactSpace X] [PreconnectedSpace X]
    {A : HolomorphicCoefficientDisks X} {P : Set X} (hP : P.Finite)
    (h : A.ZeroRealAvoidingPeriods Pᶜ A.coefficient) (p : X) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) (A.radius p)) : A.coefficient p z = 0 :=
  coefficient_zero_on_disks_of_zero_real_periods
    (zeroRealPeriods_of_avoiding_finite_poles hP h) p hz

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.zero_of_real_periods_avoiding_finite_poles
