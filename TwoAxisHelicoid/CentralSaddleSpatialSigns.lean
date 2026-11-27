import TwoAxisHelicoid.CentralHeightArc
import TwoAxisHelicoid.SigmaRealPositive

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- The continued horizontal kernel on the real axis is a product of
two real squares and a positive real exponential. -/
theorem thetaA_real_nonnegative (t a x : ℝ) :
    (thetaA t a x).im=0 ∧ 0≤(thetaA t a x).re := by
  let J := fun n u => (thetaScaledJet t n (u:ℝ)).re
  let b := (J 1 0/J 0 a)^2*(J 0 (x-a)/J 0 x)^2
  let v := 2*(a-1)*(J 1 x/J 0 x)
  have e : thetaA t a x=((b*Real.exp v:ℝ):ℂ) := by
    rw [thetaA_eq_scaled,← Complex.ofReal_sub,← Complex.ofReal_zero,
      thetaScaledJet_eq_ofReal t 1 0,thetaScaledJet_eq_ofReal t 0 a,
      thetaScaledJet_eq_ofReal t 0 (x-a),thetaScaledJet_eq_ofReal t 0 x,thetaScaledJet_eq_ofReal t 1 x]
    dsimp [b,v,J]
    push_cast
    rfl
  rw [e]
  refine ⟨rfl,?_⟩
  change 0≤b*Real.exp v
  dsimp [b]
  positivity

/-- The positive normalization orients the entire marked horizontal
line in the direction of decreasing first coordinate. At the first
saddle the upward parameter derivative of the transverse coordinate
is strictly positive. -/
theorem horizontal_axis_and_saddle_orientations {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht) :
    StrictAntiOn (fun x : ℝ => X (x:ℂ) 0) (Ioo 0 2) ∧
      0<(I*coordinateData t a 1 ht a 1).re := by
  have non (x : ℝ) (hx : x∈Ioo (0:ℝ) 2) : 0<(thetaA t a (-x)).re+(thetaA t a x).re := by
    have p := thetaA_real_nonnegative t a x
    have m := thetaA_real_nonnegative t a (-x)
    rw [Complex.ofReal_neg] at m
    obtain left|right := thetaA_pair_not_both_zero ht ha (real_not_mem_rhombic_lattice_of_pos ht hx.1 hx.2)
    · have nz : (thetaA t a x).re≠0 := fun eq => left (Complex.ext eq p.1)
      linarith [lt_of_le_of_ne p.2 nz.symm,m.2]
    · have nz : (thetaA t a (-x)).re≠0 := fun eq => right (Complex.ext eq m.1)
      linarith [lt_of_le_of_ne m.2 nz.symm,p.2]
  have aa : a∈Ioo (0:ℝ) 2 := ⟨ha.1,ha.2.trans (by norm_num)⟩
  have off := real_not_mem_rhombic_lattice_of_pos ht aa.1 aa.2
  have zero : thetaA t a a=0 := (thetaA_zero_iff_shift_lattice ht off off).mpr (by simp)
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Ioo (0:ℝ) 2)
      (fun x hx => (actual_primitive_horizontal_hasDerivAt ht d hx 0).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ioo] at hx
    rw [(actual_primitive_horizontal_hasDerivAt ht d hx 0).deriv]
    change (-(1:ℂ)/2*(thetaA t a (-x)+thetaA t a x)).re<0
    simp only [div_ofNat_re,neg_re,one_re,mul_re,div_ofNat_im,neg_im,one_im,neg_zero,zero_div,zero_mul,sub_zero,add_re]
    linarith [non x hx]
  · change 0<(I*(I*1/2*(thetaA t a a-thetaA t a (-a)))).re
    rw [zero,show I*(I*1/2*(0-thetaA t a (-a)))=thetaA t a (-a)/2 by rw [show I*(I*1/2*(0-thetaA t a (-a)))= -(I*I)*(thetaA t a (-a)/2) by ring,I_mul_I,neg_neg,one_mul]]
    have pos := non a aa
    rw [zero,zero_re,add_zero] at pos
    simpa only [div_ofNat_re] using half_pos pos

/-- On a full one-sided neighborhood of the saddle above the marked
real line, the surface lies strictly in the positive transverse
half-space and strictly on the positive side of the vertical axis. -/
theorem positive_spatial_quadrant_near_saddle {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht) :
    ∃ ε : ℝ, 0<ε ∧ ∀ x y : ℝ, |x-a|<ε → y∈Ioo 0 ε →
      X 1 0<X ((x:ℂ)+I*y) 0 ∧ X 1 1<X ((x:ℂ)+I*y) 1 := by
  let L := rhombicPeriodPair t ht
  let D := fun z : ℂ => (I*coordinateData t a 1 ht z 1).re
  have ax : a∈Ioo (0:ℝ) 2 := ⟨ha.1,ha.2.trans (by norm_num)⟩
  have off : (a:ℂ)∉L.lattice := real_not_mem_rhombic_lattice_of_pos ht ax.1 ax.2
  obtain ⟨axis,dy⟩ := horizontal_axis_and_saddle_orientations ht ha d
  have dx := axis ax (show (1:ℝ)∈Ioo 0 2 by norm_num) ha.2
  have cd : ContinuousAt D (a:ℂ) := continuous_re.continuousAt.comp
    (continuousAt_const.mul ((continuous_apply 1).continuousAt.comp (coordinateData_analyticAt ht off).continuousAt))
  have cx : ContinuousAt (fun z : ℂ => X z 0) (a:ℂ) := (actual_coordinate_primitive_component ht d off 0).continuousAt
  obtain ⟨δ,dp,near⟩ := Metric.mem_nhds_iff.mp
    (show {z : ℂ | z∉L.lattice ∧ 0<D z ∧ X 1 0<X z 0}∈𝓝 (a:ℂ) from
      by filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds off,cd.eventually (Ioi_mem_nhds dy),
           cx.eventually (Ioi_mem_nhds dx)] with z hz hpos hx using ⟨hz,hpos,hx⟩)
  let ε := min (δ/3) (min a (2-a))
  have ep : 0<ε := lt_min (by linarith) (lt_min ha.1 (by linarith [ax.2]))
  refine ⟨ε,ep,?_⟩
  intro x y hx hy
  have rng : x∈Ioo (0:ℝ) 2 := by
    obtain ⟨l,r⟩ := abs_lt.mp hx
    have low : ε≤a := (min_le_right _ _).trans (min_le_left _ _)
    have high : ε≤2-a := (min_le_right _ _).trans (min_le_right _ _)
    constructor <;> linarith
  have close (u : ℝ) (hu : u∈Icc 0 y) : (x:ℂ)+I*u∈ball (a:ℂ) δ := by
    rw [mem_ball,dist_eq_norm,show (x:ℂ)+I*u-a=((x-a:ℝ):ℂ)+I*u by push_cast; ring]
    have bd := norm_add_le ((x-a:ℝ):ℂ) (I*(u:ℂ))
    rw [norm_mul,norm_I,one_mul,norm_real,Real.norm_eq_abs,norm_real,Real.norm_eq_abs,abs_of_nonneg hu.1] at bd
    have small : ε≤δ/3 := min_le_left _ _
    linarith [hy.2,hu.2]
  let z := fun u : ℝ => (x:ℂ)+I*u
  have der (u : ℝ) (hu : u∈Icc 0 y) : HasDerivAt (fun v => X (z v) 1) (D (z u)) u := by
    have line : HasDerivAt z I u := by simpa [z] using (((hasDerivAt_id u).ofReal_comp.const_mul I).const_add (x:ℂ))
    exact (actual_coordinate_primitive_component ht d (near (close u hu)).1 1).comp_hasDerivAt u line
  obtain ⟨u,hu,slope⟩ := exists_hasDerivAt_eq_slope (fun v => X (z v) 1) (fun v => D (z v)) hy.1
    (fun v hv => (der v hv).continuousAt.continuousWithinAt) (fun v hv => der v (Ioo_subset_Icc_self hv))
  have pos := (near (close u (Ioo_subset_Icc_self hu))).2.1
  rw [slope,sub_zero] at pos
  have diff := (div_pos_iff_of_pos_right hy.1).mp pos
  have eq : X (z 0) 1=X 1 1 := by simpa [z] using (actual_primitive_horizontal_line ht d rng).1
  exact ⟨(near (close y ⟨hy.1.le,le_rfl⟩)).2.2,eq ▸ sub_pos.mp diff⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positive_spatial_quadrant_near_saddle
