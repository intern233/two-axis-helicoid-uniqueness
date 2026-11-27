import TwoAxisHelicoid.IntrinsicHorizontalTorusFlux
import TwoAxisHelicoid.PrimitivePeriodNecessity
import TwoAxisHelicoid.ActualTorusImmersion

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The original sloping period path is an actual admissible smooth arc. -/
noncomputable def originalSlopingFluxArc {t : ℝ} (ht : 0 < t) :
    ComplexPeriodArc ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ where
  left := -1
  right := 1
  ordered := by norm_num
  curve := originalPeriodPath t
  velocity := fun _ => (1-I*t)/2
  stays := fun _ hs => rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs)
  continuous_curve := by unfold originalPeriodPath; fun_prop
  continuous_velocity := continuousOn_const
  derivative := fun s _ => originalPeriodPath_hasDerivAt t s

private theorem coefficient_eq_of_null_derivative_eq {p q : Fin 3 → ℂ}
    (h : nullRealDerivative p = nullRealDerivative q) : p = q := by
  funext j
  apply Complex.ext
  · simpa using congrArg (fun f : ℂ →L[ℝ] (Fin 3 → ℝ) => f 1 j) h
  · simpa using congrArg (fun f : ℂ →L[ℝ] (Fin 3 → ℝ) => f I j) h

/-- Exact complex first-coordinate period on the projected sloping path.
The path is closed on the punctured torus, including its two endpoints. -/
theorem original_sloping_horizontal_quotient_period {t a c : ℝ} (ht : 0 < t)
    (X : PuncturedPeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ)
    (hX : HasTwoAxisHelicoidCoordinateDifferential (puncturedTorusPullback (rhombicPeriodPair t ht) X) t a c ht) :
    ∃ (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) (γ : Path q q),
      TorusPathIntegral (rhombicPeriodPair t ht) (fun z => torusImmersionForms (rhombicPeriodPair t ht) X z 0)
        γ (-(c:ℂ)*originalSlopingPeriod t a) := by
  let L := rhombicPeriodPair t ht
  let A := originalSlopingFluxArc ht
  have hform (z : ℂ) (hz : z ∉ L.lattice) : torusImmersionForms L X z = coordinateData t a c ht z :=
    coefficient_eq_of_null_derivative_eq ((immersionComplexCoefficient_hasFDerivAt (hX z hz).differentiableAt).unique (hX z hz))
  have hper : periodTorusProjection L (A.curve A.left) = periodTorusProjection L (A.curve A.right) := by
    apply (periodTorusProjection_eq_iff L _ _).mpr
    apply PeriodPair.mem_lattice.mpr
    refine ⟨1,-1,?_⟩
    simp [A,originalSlopingFluxArc,originalPeriodPath,L,rhombicPeriodPair]
    ring
  have he : A.integral (fun z => torusImmersionForms L X z 0) = originalCoordinatePeriod t a c ht 0 := by
    unfold ComplexPeriodArc.integral originalCoordinatePeriod
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    change ((1-I*t)/2)*torusImmersionForms L X (A.curve s) 0 = ((1-I*t)/2)*coordinateData t a c ht (A.curve s) 0
    rw [hform _ (A.stays (by simpa only [uIcc_of_le A.ordered] using hs))]
  have hpath : TorusPathIntegral L (fun z => torusImmersionForms L X z 0) A.projected
      (A.integral (fun z => torusImmersionForms L X z 0)) := .arc A.projected A (fun _ => rfl)
  have e : A.start = A.finish := Subtype.ext hper
  refine ⟨A.start,A.projected.cast rfl e,?_⟩
  rw [he,(originalCoordinatePeriod_horizontal (a := a) (c := c) ht).1] at hpath
  exact hpath.cast rfl e

/-- A nonreal period of the actual original kernel detects nonvertical
flux on a genuine closed quotient loop. -/
theorem original_imaginary_period_gives_intrinsic_nonvertical_flux {t a c : ℝ}
    (ht : 0 < t) (hc : c ≠ 0) (X : PuncturedPeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ)
    (hX : HasTwoAxisHelicoidCoordinateDifferential (puncturedTorusPullback (rhombicPeriodPair t ht) X) t a c ht)
    (hf : (originalSlopingPeriod t a).im ≠ 0) : HasIntrinsicNonverticalFlux (rhombicPeriodPair t ht) X := by
  obtain ⟨q,γ,hγ⟩ := original_sloping_horizontal_quotient_period ht X hX
  exact ⟨q,γ,0,_,by decide,hγ,by simpa [Complex.mul_im] using mul_ne_zero hc hf⟩

theorem actual_torus_pulled_coordinate_differential {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0) (hH : thetaHorizontalPeriod t a = 0) :
    HasTwoAxisHelicoidCoordinateDifferential (puncturedTorusPullback (rhombicPeriodPair t ht)
      (fun q => actualTorusImmersion ht ha hc hG hH q.1)) t a c ht := by
  intro z hz
  apply ((actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.2.2 z hz).1.congr_of_eventuallyEq
  filter_upwards [(rhombicPeriodPair t ht).isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
  change w ∉ (rhombicPeriodPair t ht).lattice at hw
  simp [puncturedTorusPullback,hw,puncturedPlaneProjection]

theorem actual_torus_nonvertical_flux_of_original_imaginary {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0) (hH : thetaHorizontalPeriod t a = 0)
    (hf : (originalSlopingPeriod t a).im ≠ 0) : HasIntrinsicNonverticalFlux (rhombicPeriodPair t ht)
      (fun q => actualTorusImmersion ht ha hc hG hH q.1) :=
  original_imaginary_period_gives_intrinsic_nonvertical_flux ht hc _ (actual_torus_pulled_coordinate_differential ht ha hc hG hH) hf

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_torus_nonvertical_flux_of_original_imaginary
