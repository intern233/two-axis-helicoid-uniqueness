import TwoAxisHelicoid.PuncturePullbackIsothermalAtlas
import TwoAxisHelicoid.BernsteinBreinerConformalFilling
import TwoAxisHelicoid.OriginalGeometricPoleFrame
import TwoAxisHelicoid.GeometricHelicoidHypotheses

namespace TwoAxisHelicoid
open Complex Matrix Set Topology InnerProductSpace
open scoped Topology Manifold ContDiff

/-- The published conformal compact model in its own Euclidean frame.
The regular first fundamental form is expressed in finite charts of
the compact Riemann surface. The two meromorphic coefficients are
computed from the actual spatial map in the frame of the end theorem. -/
structure PublishedConformalPoleModel {M : Type*} [TopologicalSpace M] (X : M → Fin 3 → ℝ) where
  model : Type
  [topology : TopologicalSpace model]
  [separated : T2Space model]
  [compact : CompactSpace model]
  [charts : ChartedSpace ℂ model]
  [manifold : IsManifold 𝓘(ℂ,ℂ) ω model]
  point : model
  marking : M ≃ₜ {q : model // q ≠ point}
  spatial : model → Fin 3 → ℝ
  agrees : ∀ x, spatial (marking x).1 = X x
  isothermal : IsothermalAwayFromPoint spatial point
  frame : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)
  orthogonal : ∀ u v, frame u ⬝ᵥ frame v = u ⬝ᵥ v
  offset : Fin 3 → ℝ
  chart : OpenPartialHomeomorph model ℂ
  holomorphic : chart ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω model
  end_mem : point ∈ chart.source
  centered : chart point = 0
  height : MeromorphicAt (fun z => immersionComplexCoefficient
    ((fun q => offset+frame (spatial q)) ∘ chart.symm) z 2) 0
  heightOrder : meromorphicOrderAt (fun z => immersionComplexCoefficient
    ((fun q => offset+frame (spatial q)) ∘ chart.symm) z 2) 0 = -2
  gauss : MeromorphicAt (immersionGaussLogDerivative ((fun q => offset+frame (spatial q)) ∘ chart.symm)) 0
  gaussOrder : meromorphicOrderAt (immersionGaussLogDerivative ((fun q => offset+frame (spatial q)) ∘ chart.symm)) 0 = -2
  pitch : ℝ
  pitch_ne : pitch ≠ 0
  asymptote : ApproachesSetAtInfinity (range (axisRuledHelicoid I pitch 0)) (range (fun x => offset+frame (X x)))

attribute [instance] PublishedConformalPoleModel.topology PublishedConformalPoleModel.separated
  PublishedConformalPoleModel.compact PublishedConformalPoleModel.charts PublishedConformalPoleModel.manifold

/-- An original real smooth TwoAxisHelicoid representative equipped with the
published end conclusions acquires a concrete harmonic complex atlas
and an actual torus marking with both poles in its original frame. -/
theorem original_smooth_surface_published_poles_to_torus (surface : OriginalSmoothHelicoid)
    (uniform : CompactGenusOneUniformization.{0} surface.modelTorus) (A : PublishedConformalPoleModel surface.position)
    (hend : ApproachesSetAtInfinity (range surface.position) (range (axisRuledHelicoid I surface.axes.pitch 0))) :
    ∃ S : ChartedSpace ℂ surface.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω surface.carrier ∧
      (∀ e ∈ atlas ℂ surface.carrier, InducedIsothermalChart surface.position e ∧ HarmonicImmersionChart surface.position e) ∧
    ∃ (L : PeriodPair) (f : surface.carrier ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧
      (∀ x, Y (f x).1 = surface.position x) ∧ IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Y q.1) ∧
      range (fun q : PuncturedPeriodTorus L => Y q.1) = range surface.position ∧
      (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
        ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧
        Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z)) ∧
      meromorphicOrderAt (fun z => immersionComplexCoefficient (Y ∘ periodTorusProjection L) z 2) 0 = -2 ∧
      meromorphicOrderAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0 = -2 := by
  have transfer {e : OpenPartialHomeomorph surface.carrier ℂ} (he : InducedIsothermalChart surface.position e) :
      HarmonicImmersionChart surface.position e :=
    real_minimal_isothermal_chart_harmonic surface.smooth surface.immersion surface.minimal he
  obtain ⟨S,hm,he,hj⟩ := puncture_pullback_isothermal_atlas A.point A.marking surface.position A.spatial A.agrees A.isothermal
  let _ := S
  have hman : IsManifold 𝓘(ℂ,ℂ) ω surface.carrier := hm
  have hchart (e : OpenPartialHomeomorph surface.carrier ℂ) (hc : e ∈ atlas ℂ surface.carrier) :=
    transfer (he e hc)
  obtain ⟨b,_⟩ := surface.axes.vertical 0
  let F := fun x => A.offset+A.frame (surface.position x)
  let Z := fun q => A.offset+A.frame (A.spatial q)
  have hZ (x : surface.carrier) : Z (A.marking x).1 = F x :=
    congrArg (fun v => A.offset+A.frame v) (A.agrees x)
  obtain ⟨U⟩ := abstract_conformal_filling_gives_double_pole_end b A.point A.marking hj A.chart A.holomorphic
    A.end_mem A.centered F Z hZ A.height A.heightOrder A.gauss A.gaussOrder
  let W : GeometricDoublePoleInSomeFrame surface.position :=
    ⟨A.frame,A.orthogonal,A.offset,U,A.pitch,A.pitch_ne,A.asymptote⟩
  exact ⟨S,hm,fun e hc => ⟨he e hc,hchart e hc⟩,original_surface_from_arbitrary_pole_frame surface.topologicalType uniform surface.position
    surface.closedEmbedding hchart W surface.axes.pitch_ne hend⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_smooth_surface_published_poles_to_torus
