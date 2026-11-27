import TwoAxisHelicoid.CentralHalfPeriodGaussValue
import TwoAxisHelicoid.CertifiedCentralHalfPeriods
import TwoAxisHelicoid.QuarterRowSpatialVelocity

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- A whole central neighborhood crosses the transverse symmetry line
strictly with negative first velocity, remains strictly above the
horizontal axis, and has no repeated physical point. -/
theorem certified_central_midpoint_arc_order :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let m := p.t/2
    ∃ (r : ℝ → ℝ) (δ : ℝ), 0<δ ∧
      (∀ y∈Ioo 0 p.t, r y∈Ioo (0:ℝ) 1 ∧ X ((r y:ℂ)+I*y) 2=X 1 2) ∧
      let W := fun y : ℝ => (r y:ℂ)+I*y
      let K := Icc (m-δ) (m+δ)
      StrictAntiOn (fun y => X (W y) 0) K ∧ (∀ y∈K, X 1 1<X (W y) 1) ∧
        X (W m) 0=X 1 0 ∧ (∀ y∈K, X (W y) 0=X 1 0 ↔ y=m) := by
  intro p X m
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have per := actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  obtain ⟨r,spec,cr,_,_,_,mid⟩ := actual_central_height_arc p.height_pos p.abscissa_mem d per
  let W := fun y : ℝ => (r y:ℂ)+I*y
  let G := thetaGauss p.t p.a 1
  have coord (y : ℝ) (hy : y∈Ioo 0 p.t) : X (W y) 2=X 1 2 := ((spec y hy).2 _ (spec y hy).1).mpr rfl
  have reg (y : ℝ) (hy : y∈Ioo 0 p.t) : W y∉certifiedPeriodPair.lattice :=
    rhombic_horizontal_strip_not_mem p.height_pos (by change (W y).im∈Ioo 0 p.t; simpa [W] using hy)
  have cw (y : ℝ) (hy : y∈Ioo 0 p.t) : ContinuousAt W y :=
    (continuous_ofReal.continuousAt.comp ((cr y hy).continuousAt (isOpen_Ioo.mem_nhds hy))).add (continuous_const.mul continuous_ofReal).continuousAt
  have level (y : ℝ) (hy : y∈Ioo 0 p.t) : (actualComplexHeight p.t p.a 1 p.height_pos (W y)).re=0 := by
    rw [← actual_complex_height_centered_primitive p.height_pos d (reg y hy),coord y hy,sub_self]
  have tm : m∈Ioo 0 p.t := ⟨half_pos p.height_pos,half_lt_self p.height_pos⟩
  have wm : W m=(1+I*p.t)/2 := by dsimp [W,m]; rw [mid]; push_cast; ring
  have minus : W m-p.a∉certifiedPeriodPair.lattice := rhombic_horizontal_strip_not_mem p.height_pos
    (by change (W m-p.a).im∈Ioo 0 p.t; simpa [W] using tm)
  have plus : W m+p.a∉certifiedPeriodPair.lattice := rhombic_horizontal_strip_not_mem p.height_pos
    (by change (W m+p.a).im∈Ioo 0 p.t; simpa [W] using tm)
  have cg := continuous_im.continuousAt.comp (((thetaGauss_hasDerivAt p.height_pos p.a 1 (reg m tm) minus plus).continuousAt).comp (cw m tm))
  obtain ⟨t,a⟩ := certifiedClosedParameters_bounds
  have sign : (G (W m)).im<0 := by
    change (thetaGauss p.t p.a 1 (W m)).im<0
    rw [wm,central_half_period_gauss_value (Ioo_subset_Icc_self t) (Ioo_subset_Icc_self a) p.height_pos p.abscissa_mem]
    simp
  have point := certified_central_half_periods_separated.1
  change 1/2<X ((1+I*p.t)/2) 1-X 1 1 at point
  have above : X 1 1<X (W m) 1 := by rw [wm]; linarith
  have cz := (continuous_apply 1).continuousAt.comp ((d _ (reg m tm)).continuousAt.comp (cw m tm))
  have n : {y | y∈Ioo 0 p.t ∧ (G (W y)).im<0 ∧ X 1 1<X (W y) 1}∈𝓝 m := by
    filter_upwards [isOpen_Ioo.mem_nhds tm,cg.eventually (Iio_mem_nhds sign),cz.eventually (Ioi_mem_nhds above)] with y hy hg hx using ⟨hy,hg,hx⟩
  obtain ⟨ε,ep,box⟩ := Metric.mem_nhds_iff.mp n
  let δ := ε/2
  let K := Icc (m-δ) (m+δ)
  have dp : 0<δ := half_pos ep
  have within {y : ℝ} (hy : y∈K) : y∈Ioo 0 p.t ∧ (G (W y)).im<0 ∧ X 1 1<X (W y) 1 := box (by
    rw [mem_ball,Real.dist_eq,abs_lt]
    dsimp [K,δ] at hy
    constructor <;> linarith [hy.1,hy.2])
  have dec : StrictAntiOn (fun y => X (W y) 0) K := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun y hy =>
      ((continuous_apply 0).continuousAt.comp ((d _ (reg y (within hy).1)).continuousAt.comp (cw y (within hy).1))).continuousWithinAt)
    intro y hy
    have b := within (interior_subset hy)
    obtain ⟨k,kp,h⟩ := quarter_row_spatial_velocity p.height_pos p.abscissa_mem d ((cr y b.1).continuousAt (isOpen_Ioo.mem_nhds b.1))
      b.1 (spec y b.1).1 (s:=0) (by filter_upwards [isOpen_Ioo.mem_nhds b.1] with v hv using level v hv)
    exact (hasDerivAt_pi.mp h 0).deriv.trans_lt (mul_neg_of_pos_of_neg kp b.2.1)
  have x := congrFun (central_half_period_spatial_test p.height_pos d per).2.2.2.1 0
  change X ((1+I*p.t)/2) 0-X 1 0=0 at x
  have on : X (W m) 0=X 1 0 := wm ▸ sub_eq_zero.mp x
  have mk : m∈K := ⟨by linarith,by linarith⟩
  exact ⟨r,δ,dp,fun y hy => ⟨(spec y hy).1,coord y hy⟩,dec,fun _ h => (within h).2.2,on,
    fun y hy => ⟨fun e => dec.injOn hy mk (e.trans on.symm),fun e => e ▸ on⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_half_period_gauss_value
#print axioms TwoAxisHelicoid.certified_central_midpoint_arc_order
