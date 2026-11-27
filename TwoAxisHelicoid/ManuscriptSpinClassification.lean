import TwoAxisHelicoid.OriginalNormalizedGaussDivisor
import TwoAxisHelicoid.PublishedOriginalSpinBranch
import TwoAxisHelicoid.PublishedGeometricClassification

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- Apply the period and reconstruction arguments to the very same marked
immersion for which the spin of the cap selected the basic branch. -/
theorem pointed_spin_cap_certifies_original (s : OriginalPositionallyAsymptoticHelicoid)
    (hcap : HasPointedOriginalSpinBranchCap s) :
    HasHelicoidalC1End s.position ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid := by
  obtain ⟨S,hs,hchart,t,ht,a,c,m,e,R,Z,hZ,hcross,hmarked,
    he,hei,hR,hpos,_,ha,hc,_,_,hh,hg,_,hm,_⟩ := hcap
  let _ := S
  let _ := hs
  have endGraph := (harmonic_integer_data_hasHelicoidalC1End ht ha hc m hZ hh hg).comp_homeomorph e
  have pointwise : harmonicTorusImmersion hZ ∘ e = R ∘ s.position := funext hpos
  rw [pointwise] at endGraph
  refine ⟨HasHelicoidalC1End.of_isometry R hR endGraph,?_⟩
  subst m
  have hg' (z : ℂ) (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) Z z) = 1*thetaGauss t a 1 z := by
    simpa only [one_mul] using hg z hz
  have hZdiff := harmonic_basic_gauss_data_has_coordinate_differential ht ha hc norm_one hZ hh hg'
  let p := certifiedClosedParameters
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  have hX := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem
    (by norm_num : (1:ℝ) ≠ 0) p.vertical_closed p.horizontal_closed
  have hXdiff (z : ℂ) (hz : z ∉ certifiedPeriodPair.lattice) :
      HasFDerivAt X (nullRealDerivative (phasedCoordinateData p.t p.a 1 p.height_pos 1 z)) z := by
    have eq : phasedCoordinateData p.t p.a 1 p.height_pos 1 z = coordinateData p.t p.a 1 p.height_pos z := by
      funext j
      fin_cases j <;> simp [phasedCoordinateData,complexVerticalRotation]
    rw [eq]
    exact (hX.2.2.2 z hz).1
  obtain ⟨et,_,k,A,b,hk,hmodel⟩ := periodic_explicit_immersions_global_similarity ht p.height_pos ha p.abscissa_mem hc
    (by norm_num) norm_one norm_one hZdiff hXdiff hZ.periodic (fun z _ w hw => hX.1 z w hw)
  subst t
  have htorus (q : PuncturedPeriodTorus certifiedPeriodPair) :
      certifiedTorusImmersion q = k • A (coordinateToEuclidean (harmonicTorusImmersion hZ q))+b := by
    obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
    have hp : periodTorusProjection certifiedPeriodPair z = q.1 := hz
    have hn : z ∉ certifiedPeriodPair.lattice := fun h => q.2 (hp.symm.trans ((periodTorusProjection_eq_zero _ z).mpr h))
    let r : PuncturedPeriodTorus certifiedPeriodPair :=
      ⟨periodTorusProjection _ z, fun h => hn ((periodTorusProjection_eq_zero _ z).mp h)⟩
    have hr : r = q := Subtype.ext hp
    have eval : harmonicTorusImmersion hZ r = Z z := harmonicTorusImmersion_projection hZ hn
    rw [← hr,eval]
    exact hmodel z hn
  let E := (euclideanOrientationIsometry R hR).trans A.toIsometryEquiv
  refine ⟨S,hs,hchart,e,k,E,b,he,hei,hk,?_,hcross,hmarked,punctured_biholomorphic_identification_fills e he⟩
  intro x
  exact (htorus (e x)).trans (congrArg (fun v : Fin 3 → ℝ => k • A (coordinateToEuclidean v)+b) (hpos x))

/-- The original proof of Theorem 1.1 using the even spin structure of the
actual embedded cap. The embedded-existence input supplies one surface. -/
theorem theorem_1_1_via_manuscript_spin
    (bbc : PublishedOneHandleEndTheorem) (poincare : SimplyConnectedNoncompactUniformization.{0})
    (intersection : GeometricTwoAxisIntersectionTheorem) (pinkall : PinkallEmbeddedTorusRegularHomotopy)
    (whw : Nonempty OriginalPositionallyAsymptoticHelicoid) :
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let represents := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image = c
    (∃! c, represents c) ∧ represents (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : OriginalPositionallyAsymptoticHelicoid,
        HasHelicoidalC1End s.position ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid) ∧
      certifiedPeriodPair.ω₁ = 2 ∧ certifiedPeriodPair.ω₂ = 1+I*p.t ∧
      p.t ∈ Ioo (866227694384/10^12 : ℝ) (866227694385/10^12) ∧
      p.a ∈ Ioo (5936860965140/10^13 : ℝ) (5936860965150/10^13) ∧
      GaussZeroPoleData p.t p.a p.height_pos (immersionGaussMap (actualGlobalImmersion p.t p.a 1 p.height_pos)) := by
  have normalize (s : OriginalPositionallyAsymptoticHelicoid) :
      HasHelicoidalC1End s.position ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid := by
    obtain ⟨A⟩ := bbc s.toOriginalSmoothHelicoid s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
    exact pointed_spin_cap_certifies_original s (published_original_pointed_spin_cap s A poincare intersection pinkall)
  obtain ⟨hc,hr,hE⟩ := positional_classification_of_pointed_models (fun s => (normalize s).2) whw
  let p := certifiedClosedParameters
  refine ⟨hc,hr,hE,normalize,rfl,rfl,?_,?_,
    closed_immersion_gauss_divisor p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed⟩
  · convert certifiedClosedParameters_bounds.1 using 1; norm_num [rootTLower,rootTUpper]
  · convert certifiedClosedParameters_bounds.2 using 1; norm_num [rootALower,rootAUpper]

/-- For each given original surface, the same compact marking carries the
actual normalized Gauss divisor, end and axes from the spin argument. -/
theorem original_pointed_gauss_divisor_via_manuscript_spin (s : OriginalPositionallyAsymptoticHelicoid)
    (bbc : PublishedOneHandleEndTheorem) (poincare : SimplyConnectedNoncompactUniformization.{0})
    (intersection : GeometricTwoAxisIntersectionTheorem) (pinkall : PinkallEmbeddedTorusRegularHomotopy) :
    HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid := by
  obtain ⟨A⟩ := bbc s.toOriginalSmoothHelicoid s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
  exact original_pointed_gauss_divisor_of_normalization s.toOriginalSmoothHelicoid
    (pointed_spin_cap_certifies_original s (published_original_pointed_spin_cap s A poincare intersection pinkall)).2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.theorem_1_1_via_manuscript_spin
#print axioms TwoAxisHelicoid.original_pointed_gauss_divisor_via_manuscript_spin
