import TwoAxisHelicoid.OriginalPointedModel
import TwoAxisHelicoid.ModelGaussDivisor
import TwoAxisHelicoid.TorusHeightFluxLoop

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ComplexConjugate ContDiff Manifold OnePoint

/-- The divisor only depends on germs at finite points of the surface. -/
theorem GaussZeroPoleData.congr_off_lattice {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    {g f : ℂ → ℂ} (D : GaussZeroPoleData t a ht f)
    (heq : ∀ z ∉ (rhombicPeriodPair t ht).lattice, g z = f z) : GaussZeroPoleData t a ht g := by
  let L := rhombicPeriodPair t ht
  have hloc (z : ℂ) (hz : z ∉ L.lattice) : g =ᶠ[𝓝 z] f := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact heq w hw
  have han := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have hneg : -(a:ℂ) ∉ L.lattice := by simpa [L] using han
  have hi : (fun z => (g z)⁻¹) =ᶠ[𝓝 (-(a:ℂ))] fun z => (f z)⁻¹ :=
    (hloc _ hneg).mono fun z hz => congrArg Inv.inv hz
  have away z (hz : z ∉ gaussLogPoleSet L a) := ((not_mem_gaussLogPoleSet L a z).mp hz).1
  refine ⟨fun z hz => (D.analytic z hz).congr (hloc z (away z hz)).symm,
    fun z hz => (heq z (away z hz)).trans_ne (D.nonzero z hz),?_,?_,?_,
    D.positive_analytic.congr (hloc _ han).symm,(heq _ han).trans D.positive_zero,?_,
    D.negative_analytic.congr hi.symm,hi.eq_of_nhds.trans D.negative_zero,?_⟩
  · intro z w hw hz
    have hzw : z+w ∉ L.lattice := by
      intro h
      exact away z hz (by simpa using L.lattice.sub_mem h hw)
    rw [heq _ hzw,heq _ (away z hz)]
    exact D.periodic z w hw hz
  · intro z hz
    have hcz : conj z ∉ L.lattice := by
      intro h
      exact away z hz (by simpa using rhombic_conj_mem ht h)
    rw [heq _ hcz,heq _ (away z hz)]
    exact D.conjugation z hz
  · intro z hz
    have hnz : -z ∉ L.lattice := by simpa using away z hz
    rw [heq _ hnz,heq _ (away z hz)]
    exact D.neg_product z hz
  · simpa only [(hloc _ han).deriv_eq] using D.positive_simple
  · simpa only [hi.deriv_eq] using D.negative_simple


/-- The Gauss divisor holds in every marked presentation satisfying the
pointwise spatial normalization, including the marking of the cap. -/
theorem gauss_divisor_of_given_original_marking (s : OriginalSmoothHelicoid)
    (U : s.carrier ≃ₜ PuncturedPeriodTorus certifiedPeriodPair) (k : ℝ)
    (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)) (b : EuclideanSpace ℝ (Fin 3))
    (hpos : ∀ x, certifiedTorusImmersion (U x) = k • E (s.euclideanPosition x)+b) :
    let p := certifiedClosedParameters
    ∀ Y : ℂ → Fin 3 → ℝ, (∀ z : ℂ, ∀ hz : z ∉ certifiedPeriodPair.lattice,
      coordinateToEuclidean (Y z) = k • E (s.euclideanPosition (U.symm
        ⟨periodTorusProjection certifiedPeriodPair z,fun h => hz ((periodTorusProjection_eq_zero _ z).mp h)⟩))+b) →
      GaussZeroPoleData p.t p.a p.height_pos (immersionGaussMap Y) := by
  intro p Y hY
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  have eq (z : ℂ) (hz : z ∉ certifiedPeriodPair.lattice) : Y z = X z := by
    let q : PuncturedPeriodTorus certifiedPeriodPair :=
      ⟨periodTorusProjection certifiedPeriodPair z,fun e => hz ((periodTorusProjection_eq_zero _ z).mp e)⟩
    have h := (hY z hz).trans (hpos (U.symm q)).symm
    rw [U.apply_symm_apply] at h
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective h
  have D := closed_immersion_gauss_divisor p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed
  apply GaussZeroPoleData.congr_off_lattice p.height_pos p.abscissa_mem D
  intro z hz
  have ev : Y =ᶠ[𝓝 z] X := by
    filter_upwards [certifiedPeriodPair.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact eq w hw
  change immersionGaussMap Y z = immersionGaussMap X z
  apply congrArg nullGauss
  funext j
  have hj : (fun w => Y w j) =ᶠ[𝓝 z] (fun w => X w j) := ev.mono fun w hw => congrFun hw j
  simp only [immersionComplexCoefficient,scalarComplexCoefficient,hj.fderiv_eq]

/-- In its actual normalized original spatial coordinates the surface has
the certified Gauss divisor. Every extension of the parameterization at
lattice points gives the same derivatives at its genuine surface points. -/
theorem original_normalized_position_gauss_divisor (s : OriginalSmoothHelicoid)
    (marked : HasCertifiedPointedNormalization s) :
    let p := certifiedClosedParameters
    ∃ (U : s.carrier ≃ₜ PuncturedPeriodTorus certifiedPeriodPair) (k : ℝ)
      (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)) (b : EuclideanSpace ℝ (Fin 3)),
      0 < k ∧ (∀ x, certifiedTorusImmersion (U x) = k • E (s.euclideanPosition x)+b) ∧
      ∀ Y : ℂ → Fin 3 → ℝ, (∀ z : ℂ, ∀ hz : z ∉ certifiedPeriodPair.lattice,
        coordinateToEuclidean (Y z) = k • E (s.euclideanPosition (U.symm
          ⟨periodTorusProjection certifiedPeriodPair z,fun h => hz ((periodTorusProjection_eq_zero _ z).mp h)⟩))+b) →
        GaussZeroPoleData p.t p.a p.height_pos (immersionGaussMap Y) := by
  obtain ⟨S,hs,_,U,k,E,b,_,_,hk,hpos,_,_,_⟩ := marked
  exact ⟨U,k,E,b,hk,hpos,gauss_divisor_of_given_original_marking s U k E b hpos⟩

/-- A single biholomorphic marking simultaneously locates the compactified
end, the axes and the Gauss divisor of the normalized original position. -/
def HasOriginalPointedGaussDivisor (s : OriginalSmoothHelicoid) : Prop :=
  let p := certifiedClosedParameters
  ∃ S : ChartedSpace ℂ s.carrier, let _ := S
    IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ ∃ (U : s.carrier ≃ₜ PuncturedPeriodTorus certifiedPeriodPair) (k : ℝ)
      (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)) (b : EuclideanSpace ℝ (Fin 3)),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U.symm ∧ 0 < k ∧
      (∀ x, certifiedTorusImmersion (U x) = k • E (s.euclideanPosition x)+b) ∧
      s.position (U.symm (rhombicAxisPoint p.height_pos)) = ![0,0,s.axes.horizontalPoint 2] ∧
      ∃ T : ChartedSpace ℂ (OnePoint s.carrier), let _ := T
        IsManifold 𝓘(ℂ,ℂ) ω (OnePoint s.carrier) ∧ ∃ H : OnePoint s.carrier ≃ₜ PeriodTorus certifiedPeriodPair,
          H OnePoint.infty = 0 ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
          (∀ x : s.carrier, H (x : OnePoint s.carrier) = (U x).1) ∧
          GaussZeroPoleData p.t p.a p.height_pos (immersionGaussMap (puncturedTorusPullback certifiedPeriodPair
            (fun q => WithLp.ofLp (k • E (s.euclideanPosition (U.symm q))+b))))

theorem original_pointed_gauss_divisor_of_normalization (s : OriginalSmoothHelicoid)
    (marked : HasCertifiedPointedNormalization s) : HasOriginalPointedGaussDivisor s := by
  obtain ⟨S,hs,_,U,k,E,b,hu,hui,hk,hpos,_,hc,T,ht,H,hzero,hh,hhi,_,hfill⟩ := marked
  refine ⟨S,hs,U,k,E,b,hu,hui,hk,hpos,hc,T,ht,H,hzero,hh,hhi,hfill,?_⟩
  apply gauss_divisor_of_given_original_marking s U k E b hpos
  intro z hz
  simp [puncturedTorusPullback,hz,puncturedPlaneProjection,coordinateToEuclidean]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_normalized_position_gauss_divisor
#print axioms TwoAxisHelicoid.original_pointed_gauss_divisor_of_normalization
