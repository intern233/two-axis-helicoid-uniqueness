import TwoAxisHelicoid.OriginalPointedClassification
import TwoAxisHelicoid.RawPublishedConformalPoleReduction
import TwoAxisHelicoid.OriginalGeometricTopology
import TwoAxisHelicoid.GeometricHelicoidIntersection
import TwoAxisHelicoid.ClassicalRiemannUniformizationSpecialization
import TwoAxisHelicoid.PositionalMarkedC1End
import TwoAxisHelicoid.ModelGaussDivisor

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology Manifold ContDiff

/-- Compactification, meromorphic double poles and helicoidal asymptotics in
the frame of the end theorem. The input surface has its original smooth real
structure. Completeness, a single end and exclusion of the plane are tested
on its actual metric, topology and image. -/
def PublishedOneHandleEndTheorem : Prop :=
  ∀ s : OriginalSmoothHelicoid,
    (letI : T3Space s.carrier := s.closedEmbedding.isEmbedding.t3Space
     letI := euclideanImmersionEMetricSpace s.euclideanPosition s.euclidean_smooth s.euclidean_immersion
     CompleteSpace s.carrier) →
    (∀ K : Set s.carrier, IsCompact K →
      ∃ U : Set s.carrier, IsOpen U ∧ IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K) →
    (∀ P : ℂ → Fin 3 → ℝ, IsEmbedding P → range s.position ≠ range P) →
    Nonempty (PublishedConformalPoleModel s.position)

/-- The compact conformal model and the two meromorphic end orders suffice
to normalize an original geometric representative. The graph follows before
the use of the exact helicoid intersection theorem. -/
theorem published_end_pointed_normalization (s : OriginalPositionallyAsymptoticHelicoid)
    (bbc : PublishedOneHandleEndTheorem) (uniform : CompactGenusOneUniformization.{0} s.modelTorus)
    (hw : RhombicHelicoidIntersectionPrinciple) :
    HasHelicoidalC1End s.position ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid := by
  obtain ⟨A⟩ := bbc s.toOriginalSmoothHelicoid s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
  obtain ⟨S,hs,hchart,L,f,Y,hfhol,hfinv,hf,hclosed,him,hhi,hh,hg⟩ :=
    original_smooth_surface_published_poles_to_torus s.toOriginalSmoothHelicoid uniform A s.approaches
  let := S
  let := hs
  let image := range (fun q : PuncturedPeriodTorus L => Y q.1)
  have hline : ∀ r : ℝ, s.axes.horizontalPoint+r • ![s.axes.horizontalDirection.re,s.axes.horizontalDirection.im,0] ∈ image := by
    dsimp only [image]
    rw [him]
    exact s.axes.horizontal
  have hver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ image := by
    dsimp only [image]
    rw [him]
    exact s.axes.vertical
  have hend : ApproachesSetAtInfinity image (range (axisRuledHelicoid I s.axes.pitch 0)) := by
    dsimp only [image]
    rw [him]
    exact s.approaches
  constructor
  · have h := positional_marked_torus_has_helicoidal_graph L Y hclosed s.axes.horizontalDirection s.axes.unit
      s.axes.horizontalPoint hline hver s.axes.pitch_ne hend hhi hh hg
    have eq : (fun q : PuncturedPeriodTorus L => Y q.1) ∘ f = s.position := funext hf
    exact eq ▸ h.comp_homeomorph f
  · refine ⟨S,hs,fun e he => (hchart e he).1,?_⟩
    obtain ⟨_,V,k,E,b,_,_,_,hv,hi,_,hc,hx,hk,hpt⟩ := marked_arbitrary_axes_biholomorphic_to_certified hw L Y hclosed
      s.axes.horizontalDirection s.axes.unit s.axes.horizontalPoint hline hver s.axes.pitch_ne hend hhi hh hg
    let U := f.trans V
    have han : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U := hv.comp hfhol
    refine ⟨U,k,E,b,han,hfinv.comp hi,hk,fun x => (hpt (f x)).trans
      (by simp only [hf,OriginalSmoothHelicoid.euclideanPosition,Function.comp_apply]),hc,?_,
      punctured_biholomorphic_identification_fills U han⟩
    change s.position (f.symm (V.symm _)) = _
    rw [← hf,f.apply_symm_apply]
    exact hx

/-- Theorem 1.1 with the published end, uniformization, intersection and
embedded-existence statements supplied separately. All decimal endpoints
are exact rationals. -/
theorem theorem_1_1_from_published_geometric_inputs
    (bbc : PublishedOneHandleEndTheorem) (poincare : SimplyConnectedNoncompactUniformization.{0})
    (intersection : GeometricTwoAxisIntersectionTheorem) (whw : Nonempty OriginalPositionallyAsymptoticHelicoid) :
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
  let p := certifiedClosedParameters
  have normalize (s : OriginalPositionallyAsymptoticHelicoid) :=
    published_end_pointed_normalization s bbc (compact_genus_one_uniformization_of_classical poincare s.modelTorus)
      (rhombic_intersection_of_geometric_theorem intersection)
  obtain ⟨hc,hr,he⟩ := positional_classification_of_pointed_models (fun s => (normalize s).2) whw
  refine ⟨hc,hr,he,normalize,rfl,rfl,?_,?_,
    closed_immersion_gauss_divisor p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed⟩
  · convert certifiedClosedParameters_bounds.1 using 1; norm_num [rootTLower,rootTUpper]
  · convert certifiedClosedParameters_bounds.2 using 1; norm_num [rootALower,rootAUpper]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.theorem_1_1_from_published_geometric_inputs
