import TwoAxisHelicoid.OriginalPointedContactSpin
import TwoAxisHelicoid.CenteredClosedPeriodScaling

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology Manifold ContDiff

/-- A marking for a freely specified period solution. One map identifies the
physical position, the crossing over 1, the simple Gauss divisor and the
compactification at 0. The equality of positions is at every physical point. -/
def PhysicalClosedSpinMarking (p : ClosedPeriodParameters) (s : OriginalPositionallyAsymptoticHelicoid) : Prop :=
  let L := rhombicPeriodPair p.t p.height_pos
  ∃ S : ChartedSpace ℂ s.carrier, let _ := S
    IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ (∀ d∈atlas ℂ s.carrier, InducedIsothermalChart s.position d) ∧
    ∃ (e : s.carrier ≃ₜ PuncturedPeriodTorus L) (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
      (Z : ℂ → Fin 3 → ℝ) (hZ : TwoAxisHarmonicConformalImmersion L Z) (c : ℝ),
      OriginalMarkedSpinCapData s p.a c 1 e R Z hZ ∧
      s.position (e.symm (rhombicAxisPoint p.height_pos))=![0,0,s.axes.horizontalPoint 2] ∧
      GaussZeroPoleData p.t p.a p.height_pos (immersionGaussMap Z) ∧
      (∃ b : Fin 3 → ℝ, ∀ x, R (s.position x)=
        c • centeredActualTorusImmersion p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed (e x)+b) ∧
      ∃ T : ChartedSpace ℂ (OnePoint s.carrier), let _ := T
        IsManifold 𝓘(ℂ,ℂ) ω (OnePoint s.carrier) ∧
        ∃ H : OnePoint s.carrier ≃ₜ PeriodTorus L, H OnePoint.infty=0 ∧
          ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
          ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : s.carrier → OnePoint s.carrier) ∧
          ∀ x : s.carrier, H (x : OnePoint s.carrier)=(e x).1

/-- The integer selected by the spin cap supplies a closed parameter
pair before any global root or horizontal sign certificate is used. -/
theorem marked_cap_realizes_closed_period_solution (s : OriginalPositionallyAsymptoticHelicoid)
    (given : HasPointedOriginalSpinBranchCap s) : ∃ p : ClosedPeriodParameters, PhysicalClosedSpinMarking p s := by
  obtain ⟨S,man,charts,t,ht,a,c,m,e,R,Z,hZ,_,cross,cap⟩ := given
  let _ := S
  let _ := man
  have capData := cap
  obtain ⟨he,_,_,position,_,ha,hc,_,_,hh,hg,_,hm,_⟩ := capData
  subst m
  have basic (z : ℂ) (hz : z∉gaussLogPoleSet (rhombicPeriodPair t ht) a) :
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) Z z)=1*thetaGauss t a 1 z := by
    simpa only [one_mul] using hg z hz
  have dZ := harmonic_basic_gauss_data_has_coordinate_differential ht ha hc norm_one hZ hh basic
  have phase (z : ℂ) : phasedCoordinateData t a c ht 1 z=coordinateData t a c ht z := by
    funext j
    fin_cases j <;> simp [phasedCoordinateData,complexVerticalRotation]
  have forms : HasTwoAxisHelicoidCoordinateDifferential Z t a c ht := fun z hz => phase z ▸ dZ z hz
  obtain ⟨G,H⟩ := periodic_actual_primitive_period_equations ht ha hc forms hZ.periodic
  let p : ClosedPeriodParameters := ⟨t,a,ht,ha,G,H⟩
  have model := actual_global_conformal_harmonic_immersion ht ha hc G H
  have divisor : GaussZeroPoleData t a ht (immersionGaussMap Z) := by
    apply GaussZeroPoleData.congr_off_lattice ht ha (closed_immersion_gauss_divisor ht ha hc G H)
    intro z hz
    apply congrArg nullGauss
    apply nullRealDerivative_injective_coefficients
    have d := forms z hz
    have d' := (model.2.2.2 z hz).1
    exact ((immersionComplexCoefficient_hasFDerivAt d.differentiableAt).unique d).trans
      ((immersionComplexCoefficient_hasFDerivAt d'.differentiableAt).unique d').symm
  obtain ⟨b,point⟩ := actual_coordinate_primitives_unique_up_to_scale_translation
    (X:=centeredActualPrimitive t a 1 ht) ht one_ne_zero
    (fun _ hz => centeredActualPrimitive_hasFDerivAt ht ha one_ne_zero G H hz) forms
  have onTorus (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
      harmonicTorusImmersion hZ q=c • centeredActualTorusImmersion ht ha one_ne_zero G H q+b := by
    let L := rhombicPeriodPair t ht
    obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
    have proj : periodTorusProjection L z=q.1 := hz
    have regular : z∉L.lattice := fun h => q.2 (proj.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
    let q' : PuncturedPeriodTorus L := ⟨periodTorusProjection L z,fun h => regular ((periodTorusProjection_eq_zero L z).mp h)⟩
    have agree : q'=q := Subtype.ext proj
    rw [←agree,harmonicTorusImmersion_projection hZ regular]
    change Z z=c • centeredActualPrimitive t a 1 ht z+b
    simpa only [div_one] using point z regular
  exact ⟨p,S,man,charts,e,R,Z,hZ,c,cap,cross,divisor,⟨b,fun x => (position x).symm.trans (onTorus (e x))⟩,
    punctured_biholomorphic_identification_fills e he⟩

/-- For an original representative, both axis contact and the cap spin
choose the basic branch independently of horizontal root uniqueness. -/
theorem original_graph_realizes_closed_period_solution (s : OriginalHelicoidRepresentative) :
    ∃ p : ClosedPeriodParameters, PhysicalClosedSpinMarking p s.toPositional := by
  have ann := annular_riemann_surface_uniformization_proved
  obtain ⟨poles,_⟩ := original_annular_end_pole_model_and_index s ann
  exact marked_cap_realizes_closed_period_solution s.toPositional
    (original_pointed_cap_by_contact_and_spin s.toPositional poles.some
      (compact_genus_one_uniformization_of_annular_classification ann _))

/-- Take the image of the pointwise marked equality in the ambient Euclidean
space. The signed scale in the coordinate formula is an ordinary positive
dilation composed with a Euclidean isometry in the similarity quotient. -/
theorem PhysicalClosedSpinMarking.image_similar {p : ClosedPeriodParameters} {s : OriginalPositionallyAsymptoticHelicoid}
    (mark : PhysicalClosedSpinMarking p s) :
    (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))).r s.image
      (range (centeredActualEuclideanImmersion p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed)) := by
  obtain ⟨S,_,_,e,R,Z,hZ,c,cap,_,_,⟨b,pt⟩,_⟩ := mark
  let _ := S
  obtain ⟨_,_,orth,_,_,_,hc,_⟩ := cap
  let D := DilationEquiv.smulTorsor (coordinateToEuclidean b) hc
  let J := euclideanOrientationIsometry R orth
  let F := D.trans J.symm.toDilationEquiv
  let C := centeredActualEuclideanImmersion p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed
  have physical (x : s.carrier) : F (C (e x))=s.euclideanPosition x := by
    apply J.injective
    change J (J.symm (D (C (e x))))=coordinateToEuclidean (R (s.position x))
    rw [J.apply_symm_apply,pt]
    change c • coordinateToEuclidean _+coordinateToEuclidean b=coordinateToEuclidean (c • _+b)
    rw [map_add,map_smul]
  apply (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))).symm
  refine ⟨F,?_⟩
  ext y
  constructor
  · rintro ⟨_,⟨q,rfl⟩,rfl⟩
    obtain ⟨x,rfl⟩ := e.surjective q
    exact ⟨x,(physical x).symm⟩
  · rintro ⟨x,rfl⟩
    exact ⟨C (e x),mem_range_self _,physical x⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_cap_realizes_closed_period_solution
#print axioms TwoAxisHelicoid.original_graph_realizes_closed_period_solution
#print axioms TwoAxisHelicoid.PhysicalClosedSpinMarking.image_similar
