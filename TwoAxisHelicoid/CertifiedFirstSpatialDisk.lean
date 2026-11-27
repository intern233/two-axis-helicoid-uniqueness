import TwoAxisHelicoid.FirstSpatialDiskTrace

namespace TwoAxisHelicoid
open Complex ComplexBall Set Metric

noncomputable def firstSpatialFormBall (j : Fin 3) : ComplexBall :=
  ((firstSpatialDiskTrace.spatial j).output).toBall slopingFluxAnalyticSetup.config.prec

/-- The three checked rational disks enclose the actual coordinate
coefficients at each point, including the boundary of the disk. -/
theorem certified_first_spatial_disk_coefficients {z : ℂ} (hz : z∈closedBall (1:ℂ) (1/1000:ℝ)) :
    z∉certifiedPeriodPair.lattice ∧ ∀ j, (firstSpatialFormBall j).Contains
      (coordinateData certifiedClosedParameters.t certifiedClosedParameters.a 1 certifiedClosedParameters.height_pos z j) := by
  let b : ComplexBall := ⟨⟨1,0⟩,1/1000⟩
  let S := slopingFluxAnalyticSetup
  let w := firstSpatialDiskTrace
  let p := certifiedClosedParameters
  obtain ⟨box,_,_,ht⟩ := firstDiskNumbers
  have hr := certifiedClosedParameters_bounds
  obtain ⟨lo,q,a,c,_⟩ := sloping_flux_root_parameter_enclosures (Ioo_subset_Icc_self hr.1) (Ioo_subset_Icc_self hr.2)
  have snd (u : ℂ) (hu : |u.im|≤1) : ‖thetaJet p.t 2 u-thetaPartial p.t 2 S.terms u‖≤(S.error:ℝ)/(DyadicBall.denominator S.config.prec:ℝ) :=
    firstDiskTail.remainder_bound S.config (4/5) 1 2 5 1048576 (DyadicThetaTail.valid_of_checks firstDiskTail_valid) (by norm_num) lo (by simpa only [Rat.cast_one] using hu)
  have hzb : z∈closedBall b.center.val (b.radius:ℝ) := by
    have center : b.center.val=(1:ℂ) := by apply Complex.ext <;> norm_num [b,QComplex.val]
    have radius : (b.radius:ℝ)=1/1000 := by norm_num [b]
    rwa [center,radius]
  exact w.sound S slopingFluxAnalyticSetup_valid firstSpatialDiskTrace_valid p.height_pos p.abscissa_mem p.vertical_closed lo snd
      (coarsen_contains (realInterval_contains hr.1.1.le hr.1.2.le) ht) q a c (coarsen_contains (show b.Contains z by simpa only [mem_closedBall,dist_eq_norm,Contains] using hzb) box)

/-- The entire radius-1/1000 disk about 1 is injective after projection
to the certified closed torus. The finite coefficient inequalities are
proved by rational kernel checks on the isolating parameter rectangle. -/
theorem certified_first_spatial_disk_injective :
    InjOn certifiedTorusImmersion (puncturedPlaneProjection certifiedPeriodPair ''
      (Subtype.val ⁻¹' closedBall (1:ℂ) (1/1000 : ℝ))) := by
  let b : ComplexBall := ⟨⟨1,0⟩,1/1000⟩
  obtain ⟨_,width,neg,_⟩ := firstDiskNumbers
  have center : b.center.val=(1:ℂ) := by apply Complex.ext <;> norm_num [b,QComplex.val]
  have radius : (b.radius:ℝ)=1/1000 := by norm_num [b]
  have spec {z : ℂ} (hz : z∈closedBall b.center.val (b.radius:ℝ)) := certified_first_spatial_disk_coefficients (z := z)
    (by rwa [center,radius] at hz)
  have inj := certified_disk_injective_of_coefficient_margins b firstSpatialFormBall (1/4) 2
    (by norm_num [b]) (by norm_num) (by norm_num) (by norm_num) width neg spec
  rwa [center,radius] at inj

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_first_spatial_disk_coefficients
#print axioms TwoAxisHelicoid.certified_first_spatial_disk_injective
