import TwoAxisHelicoid.HoffmanWhiteBasicBranch
import TwoAxisHelicoid.HarmonicBasicDataRecognition
import TwoAxisHelicoid.CertifiedProperImmersion
import TwoAxisHelicoid.CoordinateOrientationIsometry

namespace TwoAxisHelicoid
open Complex Set Topology

/-- The full normalized parameter and all points of the lattice cover arise
from the certified model by a single Euclidean similarity. Isometries may
reverse orientation, as allowed in the geometric equivalence relation. -/
theorem harmonic_meromorphic_similarity_to_certified_cover
    (hHW : RhombicHelicoidIntersectionPrinciple)
    {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hhOrder : meromorphicOrderAt
      (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ)) :
    t = certifiedClosedParameters.t ∧ ∃ (scale : ℝ)
      (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)) (b : EuclideanSpace ℝ (Fin 3)),
      0 < scale ∧ ∀ z ∉ (rhombicPeriodPair t ht).lattice,
        coordinateToEuclidean (actualGlobalImmersion certifiedClosedParameters.t certifiedClosedParameters.a
          1 certifiedClosedParameters.height_pos z) = scale • E (coordinateToEuclidean (X z))+b := by
  obtain ⟨a,c,R,ha,hc,_,_,hR,hY,hh,hg⟩ :=
    harmonic_meromorphic_basic_data_of_intersection_principle hHW ht hX hXi hhOrder hgOrder
  have hq : ‖(1:ℂ)‖ = 1 := norm_one
  have hg' (z : ℂ) (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) (fun u => R (X u)) z) =
        1*thetaGauss t a 1 z := by rw [one_mul]; exact hg z hz
  have h₁ := harmonic_basic_gauss_data_has_coordinate_differential ht ha hc hq hY hh hg'
  let P := certifiedClosedParameters
  let G := actualGlobalImmersion P.t P.a 1 P.height_pos
  have hmodel := actual_global_conformal_harmonic_immersion P.height_pos P.abscissa_mem
    (by norm_num : (1:ℝ) ≠ 0) P.vertical_closed P.horizontal_closed
  have h₂ (z : ℂ) (hz : z ∉ (rhombicPeriodPair P.t P.height_pos).lattice) :
      HasFDerivAt G (nullRealDerivative (phasedCoordinateData P.t P.a 1 P.height_pos 1 z)) z := by
    have he : phasedCoordinateData P.t P.a 1 P.height_pos 1 z = coordinateData P.t P.a 1 P.height_pos z := by
      funext j
      fin_cases j <;> simp [phasedCoordinateData,complexVerticalRotation]
    rw [he]
    exact (hmodel.2.2.2 z hz).1
  obtain ⟨ht',_,scale,A,b,hs,hpoint⟩ := periodic_explicit_immersions_global_similarity ht P.height_pos
    ha P.abscissa_mem hc (by norm_num) hq hq h₁ h₂ hY.periodic (fun z _ ω hω => hmodel.1 z ω hω)
  exact ⟨ht',scale,(euclideanOrientationIsometry R hR).trans A.toIsometryEquiv,b,hs,hpoint⟩

/-- Equality through a homeomorphism of the two full punctured parameter
tori, including the compact core. -/
theorem harmonic_meromorphic_similarity_to_certified_torus
    (hHW : RhombicHelicoidIntersectionPrinciple)
    {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hhOrder : meromorphicOrderAt
      (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ)) :
    ∃ (U : PuncturedPeriodTorus (rhombicPeriodPair t ht) ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (scale : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)), 0 < scale ∧ ∀ q,
        certifiedTorusImmersion (U q) = scale • E (coordinateToEuclidean (harmonicTorusImmersion hX q))+b := by
  obtain ⟨ht',scale,E,b,hs,hp⟩ :=
    harmonic_meromorphic_similarity_to_certified_cover hHW ht hX hXi hhOrder hgOrder
  subst t
  refine ⟨Homeomorph.refl _,scale,E,b,hs,?_⟩
  intro q
  let L := certifiedPeriodPair
  obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
  have hproj : periodTorusProjection L z = q.1 := hz
  have hL : z ∉ L.lattice := fun h => q.2 (hproj.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
  let r : PuncturedPeriodTorus L := ⟨periodTorusProjection L z,fun h => hL ((periodTorusProjection_eq_zero L z).mp h)⟩
  have hr : r = q := Subtype.ext hproj
  rw [← hr]
  have hXr : harmonicTorusImmersion hX r = X z := harmonicTorusImmersion_projection hX hL
  rw [hXr]
  exact hp z hL

/-- The certified model is globally embedded as soon as one embedded
parametrization satisfying the stated pole-order and symmetry assumptions
exists and the cited intersection theorem applies. -/
theorem harmonic_embedded_meromorphic_implies_certified_closed_embedding
    (hHW : RhombicHelicoidIntersectionPrinciple)
    {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hhOrder : meromorphicOrderAt
      (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ)) :
    IsClosedEmbedding certifiedTorusImmersion := by
  obtain ⟨U,scale,E,b,hs,hpoint⟩ :=
    harmonic_meromorphic_similarity_to_certified_torus hHW ht hX hXi hhOrder hgOrder
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap certifiedTorusImmersion_continuous _
    certifiedTorusImmersion_isProperMap.isClosedMap
  intro p q h
  obtain ⟨p,rfl⟩ := U.surjective p
  obtain ⟨q,rfl⟩ := U.surjective q
  apply congrArg U
  apply hXi
  rw [hpoint,hpoint,add_left_inj] at h
  have h' := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => scale⁻¹ • v) h
  simp only [smul_smul,inv_mul_cancel₀ hs.ne',one_smul] at h'
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective (E.injective h')

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_meromorphic_similarity_to_certified_torus
#print axioms TwoAxisHelicoid.harmonic_embedded_meromorphic_implies_certified_closed_embedding
