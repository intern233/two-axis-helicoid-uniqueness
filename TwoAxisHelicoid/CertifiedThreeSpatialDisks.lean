import TwoAxisHelicoid.OffAxisSpatialFormData
import TwoAxisHelicoid.CertifiedAxisSpatialCut

namespace TwoAxisHelicoid
open Complex Set Metric ComplexBall

def certifiedProjectedDisk (b : ComplexBall) : Set (PuncturedPeriodTorus certifiedPeriodPair) :=
  puncturedPlaneProjection certifiedPeriodPair '' (Subtype.val ⁻¹' {z | b.Contains z})

private theorem injective_spatial_trace (w : SpatialWeierstrassTrace) (b : ComplexBall)
    (checked : let p := TraceData.slopingFluxParams
      w.Valid slopingFluxAnalyticSetup p.height.interpret p.q.output.interpret p.abscissa.interpret p.coefficient.output.interpret)
    (rad : 0≤b.radius) (box : (w.argument.toBall slopingFluxAnalyticSetup.config.prec).coarsens b)
    (width : ∀ j, 2*((w.spatial j).output.toBall slopingFluxAnalyticSetup.config.prec).radius≤1/16)
    (neg : let B := (w.spatial 0).output.toBall slopingFluxAnalyticSetup.config.prec
      B.center.re+B.radius≤ -(3/2)) : InjOn certifiedTorusImmersion (certifiedProjectedDisk b) := by
  let S := slopingFluxAnalyticSetup
  let p := certifiedClosedParameters
  obtain ⟨_,_,_,tb⟩ := firstDiskNumbers
  have root := certifiedClosedParameters_bounds
  obtain ⟨lo,q,a,c,_⟩ := sloping_flux_root_parameter_enclosures (Ioo_subset_Icc_self root.1) (Ioo_subset_Icc_self root.2)
  have tail (u : ℂ) (hu : |u.im|≤1) : ‖thetaJet p.t 2 u-thetaPartial p.t 2 S.terms u‖≤(S.error:ℝ)/(DyadicBall.denominator S.config.prec:ℝ) :=
    firstDiskTail.remainder_bound S.config (4/5) 1 2 5 1048576 (DyadicThetaTail.valid_of_checks firstDiskTail_valid)
      (by norm_num) lo (by simpa only [Rat.cast_one] using hu)
  have inj := certified_disk_injective_of_coefficient_margins b (fun j => (w.spatial j).output.toBall S.config.prec)
    (1/16) (3/2) rad (by norm_num) (by norm_num) (by norm_num) width neg (fun {z} hz =>
      w.sound S slopingFluxAnalyticSetup_valid checked p.height_pos p.abscissa_mem p.vertical_closed lo tail
        (coarsen_contains (realInterval_contains root.1.1.le root.1.2.le) tb) q a c
        (coarsen_contains (by simpa only [mem_closedBall,dist_eq_norm,Contains] using hz : b.Contains z) box))
  simpa only [certifiedProjectedDisk,closedBall,dist_eq_norm,Contains] using inj

theorem certified_off_axis_spatial_disks_injective :
    InjOn certifiedTorusImmersion (certifiedProjectedDisk upperSpatialHeightDisk) ∧
    InjOn certifiedTorusImmersion (certifiedProjectedDisk lowerSpatialHeightDisk) := by
  obtain ⟨bu,wu,nu⟩ := upperSpatialFormTrace_bounds
  obtain ⟨bl,wl,nl⟩ := lowerSpatialFormTrace_bounds
  exact ⟨injective_spatial_trace _ _ upperSpatialFormTrace_valid (by norm_num [upperSpatialHeightDisk]) bu wu nu,
    injective_spatial_trace _ _ lowerSpatialFormTrace_valid (by norm_num [lowerSpatialHeightDisk]) bl wl nl⟩

private theorem central_height_band {z : ℂ} (hz : z∈closedBall (1:ℂ) (1/1000:ℝ)) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    |X z 2-X 1 2|≤3/1000 := by
  let p := certifiedClosedParameters
  let b : ComplexBall := ⟨⟨0,0⟩,3⟩
  have sub : b.coarsens (firstSpatialFormBall 2) := by decide +kernel
  have h := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  have e := weierstrass_coordinate_chord_error (convex_closedBall (1:ℂ) (1/1000:ℝ))
    (fun w hw => (h.2.2.2 w (certified_first_spatial_disk_coefficients hw).1).1) 2 b
    (fun _ hw => coarsen_contains ((certified_first_spatial_disk_coefficients hw).2 2) sub) (mem_closedBall_self (by norm_num)) hz
  have small : ‖z-1‖≤1/1000 := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have center : b.center.val=0 := by apply Complex.ext <;> norm_num [b,QComplex.val]
  rw [center,mul_zero,zero_re,sub_zero] at e
  have radius : (b.radius:ℝ)=3 := by norm_num [b]
  rw [radius] at e
  linarith

/-- Entire checked neighborhoods in three different height bands form
one injective subset of the actual immersed torus. These neighborhoods
include a disk about the axial crossing and two genuinely off-axis disks. -/
theorem certified_three_disk_union_injective :
    let C := puncturedPlaneProjection certifiedPeriodPair '' (Subtype.val ⁻¹' closedBall (1:ℂ) (1/1000:ℝ))
    InjOn certifiedTorusImmersion ((certifiedProjectedDisk lowerSpatialHeightDisk ∪ C) ∪ certifiedProjectedDisk upperSpatialHeightDisk) := by
  let C := puncturedPlaneProjection certifiedPeriodPair '' (Subtype.val ⁻¹' closedBall (1:ℂ) (1/1000:ℝ))
  let p := certifiedClosedParameters
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  let height := fun q => certifiedTorusImmersion q 2-X 1 2
  have central : ∀ q∈C, |height q|≤3/1000 := by
    rintro _ ⟨w,hw,rfl⟩
    exact central_height_band hw
  have uc : upperSpatialHeightDisk.Contains upperSpatialHeightDisk.center.val := by simp [Contains,upperSpatialHeightDisk]
  have lc : lowerSpatialHeightDisk.Contains lowerSpatialHeightDisk.center.val := by simp [Contains,lowerSpatialHeightDisk]
  have above : ∀ q∈certifiedProjectedDisk upperSpatialHeightDisk, 9/20<height q := by
    rintro _ ⟨w,hw,rfl⟩
    exact (certified_off_axis_vertical_gap hw lc).2.2.1
  have below : ∀ q∈certifiedProjectedDisk lowerSpatialHeightDisk, height q< -(9/20) := by
    rintro _ ⟨w,hw,rfl⟩
    exact (certified_off_axis_vertical_gap uc hw).2.2.2.1
  have join {A B : Set (PuncturedPeriodTorus certifiedPeriodPair)} (a : InjOn certifiedTorusImmersion A)
      (b : InjOn certifiedTorusImmersion B) (ord : ∀ q∈A, ∀ r∈B, height q<height r) :
      InjOn certifiedTorusImmersion (A∪B) := by
    have dis : Disjoint A B := disjoint_left.mpr fun {q} hA hB => (lt_irrefl _) (ord q hA q hB)
    apply (injOn_union dis).mpr
    refine ⟨a,b,?_⟩
    intro q hq r hr eq
    exact (ord q hq r hr).ne (congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y 2-X 1 2) eq)
  obtain ⟨ui,li⟩ := certified_off_axis_spatial_disks_injective
  have first : InjOn certifiedTorusImmersion (certifiedProjectedDisk lowerSpatialHeightDisk∪C) := by
    apply join li certified_first_spatial_disk_injective
    intro q hq r hr
    linarith [below q hq,(abs_le.mp (central r hr)).1]
  apply join first ui
  intro q hq r hr
  have a := above r hr
  rcases hq with low|middle
  · linarith [below q low]
  · linarith [(abs_le.mp (central q middle)).2]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_three_disk_union_injective
