import TwoAxisHelicoid.SurfaceMorseIndex
import TwoAxisHelicoid.GeometricExteriorAreaIndex
import TwoAxisHelicoid.OriginalHelicoidRepresentative

namespace TwoAxisHelicoid
open Complex Set Filter Function Matrix MeasureTheory
open scoped ContDiff Topology Manifold BigOperators

/-- A geometric helicoidal exterior in any orthogonal spatial frame forces
infinite Morse index on the full original immersion. The negative spaces
are represented by actual smooth compactly supported normal vector fields. -/
theorem exterior_frame_implies_infinite_morse_index {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L₀) (X : M → Fin 3 → ℝ) (hX : Continuous X)
    (hcharts : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d) (A : GeometricExteriorInSomeFrame X) :
    HasInfiniteCompactSurfaceMorseIndex X := by
  let T := A.frame.toContinuousLinearEquiv
  let Z := fun x => A.offset+T (X x)
  have hc : Continuous Z := continuous_const.add (T.continuous.comp hX)
  have hZ := orthogonal_affine_harmonic_charts X hcharts A.frame A.orthogonal A.offset
  obtain ⟨c,f,_,_,hi⟩ := geometric_exterior_actual_area_infinite_index top Z hc hZ A.exterior
  intro C hC n
  obtain ⟨K,U,hK,ht,hP,hdis,hU,hl,horth,hsm,hfixed,hneg⟩ := hi C hC n
  let e := A.exterior.chart
  let W := fun z : ℂ => I*(A.exterior.pitch:ℂ)*z+infinityCorrection f z
  let P := e.symm '' (translatedPlaneCoordinates c '' K)
  let ξ := fun z : ℂ => e.symm (z+c)
  let N := fun x : M => T.symm (holomorphicLogGaussNormal W (e x-c))
  have he (p) (hp : p ∈ K) : e (ξ (planeComplex p))-c = planeComplex p := by
    have hz : planeComplex p+c ∈ e.target := translatedPlaneCoordinates_apply c p ▸ ht p hp
    rw [show e (ξ (planeComplex p)) = planeComplex p+c from e.right_inv hz,add_sub_cancel_right]
  have hT (a b) : T a ⬝ᵥ T b = a ⬝ᵥ b := A.orthogonal a b
  have hunit (p) (hp : p ∈ K) : N (ξ (planeComplex p)) ⬝ᵥ N (ξ (planeComplex p)) = 1 := by
    rw [← hT]
    simp only [N,T.apply_symm_apply,he p hp]
    simpa only [dotProduct,pow_two] using (holomorphicLogGaussNormal_actual_weierstrass_normal W (planeComplex p)).1
  have hnonzero (x) (hx : x ∈ P) : N x ≠ 0 := by
    obtain ⟨_,⟨p,hp,rfl⟩,rfl⟩ := hx
    rw [translatedPlaneCoordinates_apply]
    intro hh
    have h := hunit p hp
    change N (ξ (planeComplex p)) = 0 at hh
    rw [hh,zero_dotProduct] at h
    exact zero_ne_one h
  refine ⟨e,c,K,U,N,A.exterior.holomorphic,hK,ht,hP,hdis,hU,hl,?_,?_,
    independent_compact_normal_multiples U N hl (fun i => (hU i).2) hnonzero,?_,?_⟩
  · intro p hp
    refine ⟨hunit p hp,?_⟩
    intro w
    have hd : fderiv ℝ (Z ∘ ξ) (planeComplex p) w = T (fderiv ℝ (X ∘ ξ) (planeComplex p) w) := by
      change fderiv ℝ (fun z => A.offset+T ((X ∘ ξ) z)) (planeComplex p) w = _
      rw [fderiv_const_add]
      change fderiv ℝ (T ∘ (X ∘ ξ)) (planeComplex p) w = _
      rw [T.comp_fderiv]
      rfl
    rw [← hT,← hd]
    change T (T.symm (holomorphicLogGaussNormal W (e (ξ (planeComplex p))-c))) ⬝ᵥ _ = 0
    rw [T.apply_symm_apply,he p hp]
    exact horth p hp w
  · intro i
    have hs := T.symm.toContinuousLinearMap.contMDiff.comp (hsm i)
    apply hs.congr
    intro x
    exact (T.symm.map_smul (U i x) _).symm
  · intro a s x hx
    have hz i : U i x = 0 := by
      by_contra h
      exact hx ((hU i).2 (subset_closure h))
    simp [hz]
  · intro a ha
    have heq (s : ℝ) : (∫ p in K, coordinateAreaDensity
          ((fun x => X x+s • ((∑ i, a i*U i x) • N x)) ∘ ξ) (planeComplex p)) =
        ∫ p in K, coordinateAreaDensity (fun z =>
          exteriorSurfaceVariation Z e c W (fun x => ∑ i, a i*U i x) s (ξ z)) (planeComplex p) := by
      apply setIntegral_congr_fun hK.measurableSet
      intro p _
      change coordinateAreaDensity ((fun x => X x+s • ((∑ i, a i*U i x) • N x)) ∘ ξ) (planeComplex p) =
        coordinateAreaDensity (fun z => exteriorSurfaceVariation Z e c W (fun x => ∑ i, a i*U i x) s (ξ z)) (planeComplex p)
      refine (coordinate_area_orthogonal_affine T hT A.offset _ (planeComplex p)).symm.trans ?_
      apply congrArg (fun F => coordinateAreaDensity F (planeComplex p))
      funext z
      exact orthogonal_affine_normal_variation T A.offset X (fun x => holomorphicLogGaussNormal W (e x-c))
        (fun x => ∑ i, a i*U i x) s (ξ z)
    change deriv (deriv _) 0 < 0
    rw [funext heq]
    exact hneg a ha

/-- Appendix D.2 for an original real minimal candidate on its induced
complex surface. Only the named geometric exterior theorem is supplied. -/
theorem original_representative_infinite_morse_index (surface : OriginalHelicoidRepresentative)
    (bbc : OriginalHelicoidExteriorPrinciple) :
    ∃ S : ChartedSpace ℂ surface.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω surface.carrier ∧ (∀ d ∈ atlas ℂ surface.carrier, InducedIsothermalChart surface.position d) ∧
      HasInfiniteCompactSurfaceMorseIndex surface.position := by
  have transfer {e : OpenPartialHomeomorph surface.carrier ℂ} (he : InducedIsothermalChart surface.position e) :
      HarmonicImmersionChart surface.position e :=
    real_minimal_isothermal_chart_harmonic surface.smooth surface.immersion surface.minimal he
  obtain ⟨S,hs,hchart,⟨A⟩⟩ := bbc surface
  refine ⟨S,hs,hchart,?_⟩
  let := S
  let := hs
  exact exterior_frame_implies_infinite_morse_index surface.topologicalType surface.position
    surface.closedEmbedding.continuous (fun d hd => transfer (hchart d hd)) A

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_representative_infinite_morse_index
