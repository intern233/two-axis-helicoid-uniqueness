import TwoAxisHelicoid.PuncturedLatticePlane
import TwoAxisHelicoid.OffAxisSpatialHeightData
import TwoAxisHelicoid.HeightEndAxisCenter
import TwoAxisHelicoid.CertifiedGlobalImmersion
import TwoAxisHelicoid.FiniteSpatialSeparationCover
import TwoAxisHelicoid.CenteredActualImmersion

namespace TwoAxisHelicoid
open Complex ComplexBall Set Metric

def upperSpatialHeightDisk : ComplexBall := ⟨⟨3/4,1/4⟩,1/10000⟩
def lowerSpatialHeightDisk : ComplexBall := ⟨⟨3/4,-1/4⟩,1/10000⟩

private theorem certified_spatial_height_in_trace (w : SpatialHeightValueTrace) (d : ComplexBall)
    (checked : w.Valid slopingFluxAnalyticSetup TraceData.slopingFluxParams.height.interpret TraceData.slopingFluxParams.q.output.interpret)
    (encloses : (w.box.toBall slopingFluxAnalyticSetup.config.prec).coarsens d)
    (tbound : (TraceData.slopingFluxParams.height.interpret.toBall slopingFluxAnalyticSetup.config.prec).coarsens (realInterval rootTLower rootTUpper))
    {z : ℂ} (inside : d.Contains z) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let b := w.height.output.toBall slopingFluxAnalyticSetup.config.prec
    z∉certifiedPeriodPair.lattice ∧ ((b.center.re-b.radius:ℚ):ℝ)≤X z 2-X 1 2 ∧ X z 2-X 1 2≤((b.center.re+b.radius:ℚ):ℝ) := by
  let p := certifiedClosedParameters
  have hr := certifiedClosedParameters_bounds
  obtain ⟨lo,q,_,_,_⟩ := sloping_flux_root_parameter_enclosures (Ioo_subset_Icc_self hr.1) (Ioo_subset_Icc_self hr.2)
  obtain ⟨off,h⟩ := w.sound slopingFluxAnalyticSetup slopingFluxAnalyticSetup_valid checked p.height_pos p.abscissa_mem p.vertical_closed lo
    (coarsen_contains (realInterval_contains hr.1.1.le hr.1.2.le) tbound) q (coarsen_contains inside encloses)
  have hd : HasTwoAxisHelicoidCoordinateDifferential (actualGlobalImmersion p.t p.a 1 p.height_pos) p.t p.a 1 p.height_pos := fun v hv =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed).2.2.2 v hv).1
  dsimp only
  rw [actual_complex_height_centered_primitive p.height_pos hd off]
  exact ⟨off,re_bounds h⟩

/-- The certified immersion on the full rational disks above and below
the real axis has a vertical separation strictly larger than 9/10. -/
theorem certified_off_axis_vertical_gap {u v : ℂ} (hu : upperSpatialHeightDisk.Contains u) (hv : lowerSpatialHeightDisk.Contains v) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    u∉certifiedPeriodPair.lattice ∧ v∉certifiedPeriodPair.lattice ∧
      9/20<X u 2-X 1 2 ∧ X v 2-X 1 2< -(9/20) ∧ 9/10<X u 2-X v 2 := by
  obtain ⟨bh,lh,th⟩ := spatialUpperHeight_bounds
  obtain ⟨bl,ul,tl⟩ := spatialLowerHeight_bounds
  obtain ⟨ou,hl,_⟩ := certified_spatial_height_in_trace spatialUpperHeight upperSpatialHeightDisk spatialUpperHeight_valid bh th hu
  obtain ⟨ov,_,hr⟩ := certified_spatial_height_in_trace spatialLowerHeight lowerSpatialHeightDisk spatialLowerHeight_valid bl tl hv
  have l := lt_of_lt_of_le (show (9/20:ℝ)<_ by simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr lh) hl
  have r := lt_of_le_of_lt hr (show _< -(9/20:ℝ) by simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr ul)
  exact ⟨ou,ov,l,r,by linarith⟩

theorem certified_projected_off_axis_height_cut :
    let p := certifiedClosedParameters
    let F := centeredActualTorusImmersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
    let project := fun d : ComplexBall => puncturedPlaneProjection certifiedPeriodPair '' (Subtype.val ⁻¹' {z : ℂ | d.Contains z})
    RationalCoordinateCut F (project lowerSpatialHeightDisk) (project upperSpatialHeightDisk) := by
  have up : upperSpatialHeightDisk.Contains upperSpatialHeightDisk.center.val := by
    simp [Contains,upperSpatialHeightDisk]
  have low : lowerSpatialHeightDisk.Contains lowerSpatialHeightDisk.center.val := by
    simp [Contains,lowerSpatialHeightDisk]
  refine ⟨2,0,?_,?_⟩
  · rintro _ ⟨v,hv,rfl⟩
    have h := (certified_off_axis_vertical_gap up hv).2.2.2.1
    change _-_<((0:ℚ):ℝ)
    exact lt_trans h (by norm_num)
  · rintro _ ⟨u,hu,rfl⟩
    have h := (certified_off_axis_vertical_gap hu low).2.2.1
    change ((0:ℚ):ℝ)<_-_
    exact lt_trans (by norm_num) h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_off_axis_vertical_gap
#print axioms TwoAxisHelicoid.certified_projected_off_axis_height_cut
