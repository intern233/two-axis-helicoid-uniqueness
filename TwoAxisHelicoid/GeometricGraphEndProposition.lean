import TwoAxisHelicoid.PhysicalEndPeripheralResidue
import TwoAxisHelicoid.PhysicalGraphHolomorphicRemainder
import TwoAxisHelicoid.GeometricEndFromCapDifferentials

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology InnerProductSpace
open scoped Topology Manifold ContDiff
universe u

/-- For a harmonic conformal surface in its given complex structure,
the physical C¹ graph supplies the complete normalized end datum. -/
theorem harmonic_graph_end_proposition {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    ∃ A : GeometricDoublePoleEnd X,
        (let _ := compactifiedEndAtlas A.endChart
         IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
           ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M)) ∧
        (∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ),
          immersionGaussLogDerivative (X ∘ A.endChart.coord.symm) z-
            I*immersionComplexCoefficient (X ∘ A.endChart.coord.symm) z 2=Q z) ∧
        ∃ D : GeometricExteriorCoordinate X, D.pitch=1 ∧ D.correction 0=0 := by
  obtain ⟨A,compactified⟩ := physical_harmonic_graph_double_pole_end X closed charts graph
  let E := A.endChart
  let Y := X ∘ E.coord.symm
  have chart := harmonic_immersion_chart_maximal charts A.holomorphic
  have harm : ∀ᶠ z in 𝓝[≠] (0:ℂ), HarmonicAt (fun w => Y w 2) z := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) E.radius_pos)] with z nz near
    exact (chart z (E.mem_target_of_ball_ne near nz)).1 2
  obtain ⟨R,Rp,trivialPeriod⟩ := physical_harmonic_end_zero_peripheral_flux charts E A.holomorphic 2
  have period (s : ℝ) (sp : 0<s) : ∃ r∈Ioo (0:ℝ) s,
      (∮ z in C(0,r), immersionComplexCoefficient Y z 2)=0 := by
    let r := min R s/2
    have small : r<min R s := half_lt_self (lt_min Rp sp)
    exact ⟨r,⟨half_pos (lt_min Rp sp),small.trans_le (min_le_right _ _)⟩,
      trivialPeriod r ⟨half_pos (lt_min Rp sp),small.trans_le (min_le_left _ _)⟩⟩
  obtain ⟨H,primitive⟩ := harmonic_puncture_primitive_of_peripheral_flux harm
    (fun s sp => by
      obtain ⟨r,hr,p⟩ := period s sp
      exact ⟨r,hr,congrArg Complex.im p⟩)
  obtain ⟨Q,qa,agree⟩ := physical_graph_holomorphic_log_remainder closed.continuous charts graph A primitive
  have exterior := geometric_exterior_of_cap_differentials (α:=1) charts A period
    ⟨Q,qa,by simpa only [Complex.ofReal_one,mul_one] using agree⟩
  exact ⟨A,compactified,⟨Q,qa,agree⟩,exterior⟩

/-- Proposition 2.1 for an oriented smooth minimal embedding of arbitrary
genus with a physical C¹ helicoidal graph end, in the unit-pitch frame.
The one-point compactification, both measured double poles and the
holomorphic remainder refer to the same immersion and puncture chart.
The exterior height chart has a convergent correction vanishing at infinity. -/
theorem physical_graph_end_proposition {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (immersion : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q))
    (orientation : PositiveSurfaceAtlas M)
    (minimal : ∀ q, coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ (∀ d∈atlas ℂ M, HarmonicImmersionChart X d) ∧
      ∃ A : GeometricDoublePoleEnd X,
        (let _ := compactifiedEndAtlas A.endChart
         IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
           ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M)) ∧
        (∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ),
          immersionGaussLogDerivative (X ∘ A.endChart.coord.symm) z-
            I*immersionComplexCoefficient (X ∘ A.endChart.coord.symm) z 2=Q z) ∧
        ∃ D : GeometricExteriorCoordinate X, D.pitch=1 ∧ D.correction 0=0 := by
  obtain ⟨S,man,charts⟩ := oriented_minimal_induced_harmonic_atlas smooth immersion orientation minimal
  let _ := S
  let _ := man
  exact ⟨S,man,charts,harmonic_graph_end_proposition X closed charts graph⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_graph_end_proposition
#print axioms TwoAxisHelicoid.physical_graph_end_proposition
