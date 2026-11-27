import TwoAxisHelicoid.PositiveQuarterHeightRay
import TwoAxisHelicoid.QuarterRowSpatialVelocity
import TwoAxisHelicoid.HeightEndAxisCenter

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- On a positive quarter level, overlapping signs of the actual Gauss
map produce the two spatial orders, with endpoints included even when
the graph meets the vertical axis. -/
theorem low_level_quarter_monotone_windows {t a h b l u : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (bl : b<l) (ut : u<t) (hb : 0<b)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    {r : ℝ → ℝ} (cont : ContinuousOn r (Ico b t)) (inside : ∀ y∈Ioo b t, r y∈Ioo (0:ℝ) 1) :
    let Z := fun y : ℝ => (r y:ℂ)+I*y
    let F := fun y : ℝ => X (Z y)-X 1
    (∀ y∈Ico b t, X (Z y) 2=X 1 2+h) →
    (∀ y∈Ioo b u, (thetaGauss t a 1 (Z y)).re<0) →
    (∀ y∈Ioo l t, (thetaGauss t a 1 (Z y)).im<0) →
    StrictMonoOn (fun y => F y 1) (Icc b u) ∧ StrictAntiOn (fun y => F y 0) (Ico l t) := by
  intro Z F on first last
  let J := Ico b t
  have regular {y : ℝ} (hy : y∈J) : Z y∉(rhombicPeriodPair t ht).lattice :=
    rhombic_horizontal_strip_not_mem ht (by change (Z y).im∈Ioo 0 t; simpa [Z] using And.intro (hb.trans_le hy.1) hy.2)
  have c (j : Fin 3) : ContinuousOn (fun y => F y j) J := by
    intro y hy
    have line : ContinuousWithinAt Z J y := (continuous_ofReal.continuousAt.comp_continuousWithinAt
      (cont y hy)).add (continuous_const.mul continuous_ofReal).continuousAt.continuousWithinAt
    exact ((actual_coordinate_primitive_component ht d (regular hy) j).continuousAt.comp_continuousWithinAt line).sub continuousWithinAt_const
  have deriv {y : ℝ} (hy : y∈Ioo b t) :
      ∃ k : ℝ, 0<k ∧ HasDerivAt (X ∘ Z) ![k*(thetaGauss t a 1 (Z y)).im,-k*(thetaGauss t a 1 (Z y)).re,0] y := by
    have idx : y∈J := ⟨hy.1.le,hy.2⟩
    have cr : ContinuousAt r y := (cont y idx).continuousAt (mem_of_superset (isOpen_Ioo.mem_nhds hy) Ioo_subset_Ico_self)
    apply quarter_row_spatial_velocity ht ha d cr ⟨hb.trans hy.1,hy.2⟩ (inside y hy) (s:=h)
    filter_upwards [isOpen_Ioo.mem_nhds hy] with w hw
    have inJ : w∈J := ⟨hw.1.le,hw.2⟩
    rw [← actual_complex_height_centered_primitive ht d (regular inJ),on w inJ]
    ring
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) ((c 1).mono (fun y hy => ⟨hy.1,hy.2.trans_lt ut⟩))
    intro y hy
    rw [interior_Icc] at hy
    obtain ⟨k,kp,vel⟩ := deriv (show y∈Ioo b t from ⟨hy.1,hy.2.trans ut⟩)
    have dy : HasDerivAt (fun y => F y 1) (-k*(thetaGauss t a 1 (Z y)).re) y := (hasDerivAt_pi.mp vel 1).sub_const (X 1 1)
    rw [dy.deriv]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos kp) (first y hy)
  · apply strictAntiOn_of_deriv_neg (convex_Ico _ _) ((c 0).mono (fun y hy => ⟨bl.le.trans hy.1,hy.2⟩))
    intro y hy
    rw [interior_Ico] at hy
    obtain ⟨k,kp,vel⟩ := deriv (show y∈Ioo b t from ⟨bl.trans hy.1,hy.2⟩)
    have dy : HasDerivAt (fun y => F y 0) (k*(thetaGauss t a 1 (Z y)).im) y := (hasDerivAt_pi.mp vel 0).sub_const (X 1 0)
    rw [dy.deriv]
    exact mul_neg_of_pos_of_neg kp (last y hy)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_level_quarter_monotone_windows
