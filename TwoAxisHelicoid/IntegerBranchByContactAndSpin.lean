import TwoAxisHelicoid.VerticalAxisContactTransversality
import TwoAxisHelicoid.HelicoidEvenSpinFromSections
import TwoAxisHelicoid.MarkedHelicoidIntersectionTheorem

namespace TwoAxisHelicoid
open Complex Set Filter Topology
attribute [local irreducible] thetaGauss

/-- The calibrated comparison helicoid has exactly the two axes in
common with an actual embedded integer branch. The calibration is made
at its finite crossing and is compatible with the end's geometric frame. -/
theorem integer_data_calibrated_axes {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (hc : c≠0) (m : ℤ) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (inj : Function.Injective (harmonicTorusImmersion hX))
    (hh : ∀ z∉(rhombicPeriodPair t ht).lattice, puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2=
      coordinateData t a c ht z 2)
    (hg : ∀ z∉gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss
      (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)=thetaGauss t a m z) :
    IsClosedEmbedding (harmonicTorusImmersion hX) ∧
    range (harmonicTorusImmersion hX) ∩ range (axisRuledHelicoid (thetaGauss t a m (I*t)) (2*(a-m)/c) (X (I*t) 2))=
      {P | (P 1=0 ∧ P 2=0) ∨ (P 0=0 ∧ P 1=0)} := by
  let α := 2*(a-m)/c
  let g := thetaGauss t a m (I*t)
  obtain ⟨b,hEnd,align⟩ := harmonic_integer_end_comparison_helicoid ht ha hc m hX hh hg
  have d := harmonic_integer_gauss_data_has_coordinate_differential ht ha hc m hX hh hg
  have closed := harmonicTorusImmersion_closedEmbedding_of_escape hX inj
    (integer_primitive_end_escape_and_embedding m ht ha hc d).1 (rhombic_puncture_eventually_off_lattice ht)
  obtain ⟨hor,ver⟩ := harmonic_integer_data_contains_complete_axes ht ha hc m hX hh hg
  have both := marked_rhombic_helicoid_intersection ht hX (integer_helicoidal_pitch_ne_zero ha hc m) b closed
    (fun x => (harmonicTorusImmersion_range hX).symm ▸ hor x)
    (fun z => (harmonicTorusImmersion_range hX).symm ▸ ver z) hEnd align
  rw [align] at both
  have mid := harmonic_integer_axis_midpoint_data ht ha m hX hg
  have unit : normSq g=1 := thetaGauss_axis_normSq ht ha m ⟨ht,by linarith⟩
  have point : (![1,0,0] : Fin 3 → ℝ)∈range (axisRuledHelicoid g α (X (I*t) 2)) := by
    apply (axisHelicoidSide_eq_zero_iff unit _ _ _).mp
    change axisHelicoidSide (thetaGauss t a m (I*t)) α (X (I*t) 2) _=0
    rw [mid.1]
    rcases mid.2 with h|h <;> simp [h,axisHelicoidSide]
  exact ⟨closed,(axisRuledHelicoid_range_of_horizontal_unit unit α _ point).symm ▸ both⟩

/-- The actual integer parameter is one by the two different mechanisms
used in Sections 4.2–4.5. Local minimal-sheet contact bounds the winding,
and the self-contained parity calculation on the capped embedded
torus eliminates the remaining even branch. -/
theorem integer_branch_one_by_contact_and_spin {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (hc : c≠0) (m : ℤ) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (inj : Function.Injective (harmonicTorusImmersion hX))
    (hh : ∀ z∉(rhombicPeriodPair t ht).lattice, puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2=
      coordinateData t a c ht z 2)
    (hg : ∀ z∉gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss
      (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)=thetaGauss t a m z) :
    m=1 := by
  obtain ⟨closed,axes⟩ := integer_data_calibrated_axes ht ha hc m hX inj hh hg
  have winding := harmonic_integer_axis_parameter_by_equal_angle_contact ht ha hc
    (harmonic_height_primitive_thetaG_zero ht ha hc hX hh) m hX closed hh hg (by
      intro z hz meet
      change X z∈{P : Fin 3 → ℝ | (P 1=0 ∧ P 2=0) ∨ (P 0=0 ∧ P 1=0)}
      rw [← axes,harmonicTorusImmersion_range]
      exact ⟨⟨z,hz,rfl⟩,meet⟩)
  obtain ⟨k,hk⟩ := actual_embedded_integer_odd_from_plane_sections ht ha hc m hX inj hh hg
  omega

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.integer_data_calibrated_axes
#print axioms TwoAxisHelicoid.integer_branch_one_by_contact_and_spin
