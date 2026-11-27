import TwoAxisHelicoid.CalibratedTransverseHeight
import TwoAxisHelicoid.PositiveQuarterHeightRay
import TwoAxisHelicoid.QuarterRowSpatialVelocity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- At the calibrated positive height, the transverse coordinate starts
at zero on the vertical axis and increases strictly along the entire
quarter arc. In particular the two reflected open halves lie on
opposite sides of the vertical plane. -/
theorem calibrated_quarter_transverse_positive {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (lo : 1/2≤a) (root : thetaG t a=0)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    (direction : ∀ z∉(rhombicPeriodPair t ht).lattice, 1/4≤X z 2-X 1 2 →
      (obliqueThetaFactor true*torusThetaDirection t a z).re<0) :
    ∀ x∈Ioo (0:ℝ) 1, ∀ y∈Ioo (0:ℝ) t, X ((x:ℂ)+I*y) 2=X 1 2+transverseBoundaryHeight a →
      X 1 1<X ((x:ℂ)+I*y) 1 := by
  let s := transverseBoundaryHeight a
  have hl : 1/4<s := (transverse_boundary_height_bounds lo ha.2).1
  have hp : 0<s := lt_trans (by norm_num) hl
  obtain ⟨b,hb,r,start,cont,_,inside,eq⟩ := positive_quarter_height_ray ht ha hp d per
  let J := Ico b t
  let Z := fun y : ℝ => (r y:ℂ)+I*y
  let Y := fun y : ℝ => X (Z y) 1
  have atB : b∈J := ⟨le_rfl,hb.2⟩
  have domain {y : ℝ} (hy : y∈J) : y∈Ioo 0 t := ⟨hb.1.trans_le hy.1,hy.2⟩
  have regular {y : ℝ} (hy : y∈J) : Z y∉(rhombicPeriodPair t ht).lattice :=
    rhombic_horizontal_strip_not_mem ht (by change (Z y).im∈Ioo 0 t; simpa [Z] using domain hy)
  have centered (y : ℝ) (hy : y∈Ioo b t) : (actualComplexHeight t a 1 ht (Z y)).re=s := by
    have inJ : y∈J := ⟨hy.1.le,hy.2⟩
    have hit := (eq y (domain inJ) (r y) (Ioo_subset_Icc_self (inside y hy))).mpr ⟨hy.1.le,rfl⟩
    rw [← actual_complex_height_centered_primitive ht d (regular inJ)]
    change X (Z y) 2=X 1 2+s at hit
    linarith
  have cy : ContinuousOn Y J := by
    intro y hy
    have cz : ContinuousWithinAt Z J y := (continuous_ofReal.continuousAt.comp_continuousWithinAt
      (cont y hy)).add (continuous_const.mul continuous_ofReal).continuousAt.continuousWithinAt
    exact (actual_coordinate_primitive_component ht d (regular hy) 1).continuousAt.comp_continuousWithinAt cz
  have increasing : StrictMonoOn Y J := by
    apply strictMonoOn_of_deriv_pos (convex_Ico _ _) cy
    intro y hy
    change y∈interior (Ico b t) at hy
    rw [interior_Ico] at hy
    have inJ : y∈J := ⟨hy.1.le,hy.2⟩
    have germ : ∀ᶠ u in 𝓝 y, (actualComplexHeight t a 1 ht (Z u)).re=s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hy) fun u hu => centered u hu
    have cr : ContinuousAt r y := (cont y inJ).continuousAt
      (mem_of_superset (isOpen_Ioo.mem_nhds hy) Ioo_subset_Ico_self)
    obtain ⟨k,kp,vel⟩ := quarter_row_spatial_velocity ht ha d cr (domain inJ) (inside y hy) germ
    have hphys := (actual_complex_height_centered_primitive ht d (regular inJ)).trans (centered y hy)
    have g := transverse_boundary_gauss_sign ht ha root (centered y hy) (direction _ (regular inJ) (hl.le.trans_eq hphys.symm))
    have dw : HasDerivAt Y (-k*(thetaGauss t a 1 (Z y)).re) y := hasDerivAt_pi.mp vel 1
    rw [dw.deriv]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos kp) g
  have base : Y b=X 1 1 := by
    dsimp [Y,Z]
    rw [start,ofReal_one]
    exact (actual_primitive_vertical_line ht d ⟨by linarith [hb.1],hb.2⟩).2
  intro x hx y hy hit
  obtain ⟨by',xx⟩ := (eq y hy x (Ioo_subset_Icc_self hx)).mp hit
  have lt : b<y := lt_of_le_of_ne by' (fun same => by
    rw [← same,start] at xx
    exact hx.2.ne xx)
  have value := increasing atB (show y∈J from ⟨by',hy.2⟩) lt
  rw [base] at value
  simpa only [Y,Z,← xx] using value

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.calibrated_quarter_transverse_positive
