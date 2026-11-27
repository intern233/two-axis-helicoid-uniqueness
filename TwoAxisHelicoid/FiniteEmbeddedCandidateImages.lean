import TwoAxisHelicoid.AnalyticFinitePeriodParameters
import TwoAxisHelicoid.HoffmanWhiteBasicBranch
import TwoAxisHelicoid.CoordinateOrientationIsometry
import TwoAxisHelicoid.PrimitivePeriodNecessity
import TwoAxisHelicoid.WeierstrassTwoPrimitives

namespace TwoAxisHelicoid
open Complex Set Topology

private theorem unphased_data_one (t a c : ℝ) (ht : 0 < t) (z : ℂ) :
    phasedCoordinateData t a c ht 1 z = coordinateData t a c ht z := by
  funext j
  fin_cases j <;> simp [phasedCoordinateData,complexVerticalRotation]

/-- One spatial image for each finite scalar parameter in the independent
analytic finiteness argument. -/
noncomputable def verticalModelImage (t : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  if ht : 0 < t then (fun z => coordinateToEuclidean (actualGlobalImmersion t (verticalA t) 1 ht z)) ''
    ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ else ∅

/-- The distance from the degenerating height and the comparison with the
representative at that same height only use the endpoint analysis and the
actual map's own periods, without the intermediate compact interval boxes. -/
theorem harmonic_embedded_height_and_vertical_model (hHW : RhombicHelicoidIntersectionPrinciple)
    {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hhOrder : meromorphicOrderAt
      (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ)) :
    1/8 < t ∧ t < ellipticVerticalUpper ∧ actualPeriodAlong t = 0 ∧ ∃ (scale : ℝ)
      (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)) (b : EuclideanSpace ℝ (Fin 3)),
      0 < scale ∧ verticalModelImage t = (fun v => scale • E v+b) ''
        range (coordinateToEuclidean ∘ harmonicTorusImmersion hX) := by
  obtain ⟨a,c,R,ha,hc,hT,ha',hR,hY,hh,hg⟩ :=
    harmonic_meromorphic_basic_data_of_intersection_principle hHW ht hX hXi hhOrder hgOrder
  subst a
  let a := verticalA t
  let L := rhombicPeriodPair t ht
  let Y := fun z => R (X z)
  let p := puncturedImmersionCoefficient L Y
  have hq : ‖(1:ℂ)‖ = 1 := norm_one
  have hg' (z : ℂ) (hz : z ∉ gaussLogPoleSet L a) :
      nullGauss (p z) = 1*thetaGauss t a 1 z := (hg z hz).trans (one_mul _).symm
  have hA := hY.null_differential (fun _ hz => rhombic_conj_mem ht hz)
  have he := null_coefficients_eq_phased_coordinateData ht ha hc hq hA.null
    (fun _ hz j => puncturedImmersionCoefficient_analyticAt hY hz j) hh hg'
  have hD (z : ℂ) (hz : z ∉ L.lattice) :
      HasFDerivAt Y (nullRealDerivative (phasedCoordinateData t a c ht 1 z)) z := by
    rw [← he z hz]
    exact puncturedImmersionCoefficient_hasFDerivAt hY hz
  have hD' : HasTwoAxisHelicoidCoordinateDifferential Y t a c ht := by
    intro z hz
    rw [← unphased_data_one]
    exact hD z hz
  obtain ⟨hG,hH⟩ := periodic_actual_primitive_period_equations ht ha hc hD' hY.periodic
  have hzero : actualPeriodAlong t = 0 := hH
  let G := actualGlobalImmersion t a 1 ht
  have hmodel := actual_global_conformal_harmonic_immersion ht ha (by norm_num : (1:ℝ) ≠ 0) hG hH
  have h₂ (z : ℂ) (hz : z ∉ L.lattice) :
      HasFDerivAt G (nullRealDerivative (phasedCoordinateData t a 1 ht 1 z)) z := by
    rw [unphased_data_one]
    exact (hmodel.2.2.2 z hz).1
  obtain ⟨scale,A,b,hs,hpoint⟩ := actual_two_coordinate_primitives_similarity L.isClosed_lattice.isOpen_compl
    (rhombic_punctured_plane_isConnected ht).2 ht hc (by norm_num) hq hq hD h₂
  let E := (euclideanOrientationIsometry R hR).trans A.toIsometryEquiv
  have hp (z : ℂ) (hz : z ∉ L.lattice) :
      coordinateToEuclidean (G z) = scale • E (coordinateToEuclidean (X z))+b := hpoint z hz
  refine ⟨actualPeriodAlong_zero_height_gt_eighth ht hzero,hT,hzero,scale,E,b,hs,?_⟩
  rw [verticalModelImage,dite_eq_left ht,Set.range_comp,harmonicTorusImmersion_range hX]
  ext v
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨_,⟨_,⟨z,hz,rfl⟩,rfl⟩,(hp z hz).symm⟩
  · rintro ⟨_,⟨_,⟨z,hz,rfl⟩,rfl⟩,rfl⟩
    exact ⟨z,hz,hp z hz⟩

/-- A finite family of images represents all embedded meromorphic harmonic
candidates up to positive scaling and arbitrary Euclidean isometry. This
derivation of Appendix B.2 uses the analytic endpoint estimates instead of
the horizontal period interval certificates or the uniqueness theorem. -/
theorem finite_embedded_harmonic_images_without_horizontal_boxes
    (hHW : RhombicHelicoidIntersectionPrinciple) :
    ∃ K : Set (Set (EuclideanSpace ℝ (Fin 3))), K.Finite ∧ ∀ {t : ℝ} (ht : 0 < t)
      {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X),
      Function.Injective (harmonicTorusImmersion hX) →
      meromorphicOrderAt (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ) →
      meromorphicOrderAt (fun z =>
        deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
          nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ) →
      ∃ S ∈ K, ∃ (scale : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
        (b : EuclideanSpace ℝ (Fin 3)), 0 < scale ∧
        S = (fun v => scale • E v+b) '' range (coordinateToEuclidean ∘ harmonicTorusImmersion hX) := by
  refine ⟨verticalModelImage '' {t : ℝ | t ∈ Ioo 0 ellipticVerticalUpper ∧ actualPeriodAlong t = 0},
    actualPeriodAlong_finite_zero_parameters_analytic.image _,?_⟩
  intro t ht X hX hXi h₁ h₂
  obtain ⟨_,hT,hz,hS⟩ := harmonic_embedded_height_and_vertical_model hHW ht hX hXi h₁ h₂
  exact ⟨_,⟨t,⟨⟨ht,hT⟩,hz⟩,rfl⟩,hS⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.finite_embedded_harmonic_images_without_horizontal_boxes
