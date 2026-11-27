import TwoAxisHelicoid.HelicoidAsymptoticNonplanar
import TwoAxisHelicoid.UniqueAsymptoticVerticalAxis
import TwoAxisHelicoid.OrientedMinimalHarmonicAtlas
import TwoAxisHelicoid.ProperImmersionCompleteness
import TwoAxisHelicoid.NullEuclideanMetric

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped Topology ContDiff Manifold

/-- Actual straight lines in a reference frame in which the asymptotic
helicoid has the vertical axis. No common point of the lines or spatial
reflection is part of the data. -/
structure OriginalHelicoidAxes (S : Set (Fin 3 → ℝ)) where
  horizontalDirection : ℂ
  unit : ‖horizontalDirection‖ = 1
  horizontalPoint : Fin 3 → ℝ
  horizontal : ∀ r : ℝ, horizontalPoint+r • ![horizontalDirection.re,horizontalDirection.im,0] ∈ S
  vertical : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ S
  pitch : ℝ
  pitch_ne : pitch ≠ 0

/-- A proper embedded real minimal representative before constructing any
complex structure, period lattice, Weierstrass coefficients or end chart. -/
structure OriginalSmoothHelicoid where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [separation : T2Space carrier]
  [charts : ChartedSpace ℂ carrier]
  [manifold : IsManifold 𝓘(ℝ,ℂ) ∞ carrier]
  modelTorus : PeriodPair
  topologicalType : carrier ≃ₜ PuncturedPeriodTorus modelTorus
  position : carrier → Fin 3 → ℝ
  closedEmbedding : IsClosedEmbedding position
  smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ position
  immersion : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) position x)
  minimal : ∀ x : carrier, coordinateMeanCurvature (position ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0
  axes : OriginalHelicoidAxes (range position)

attribute [instance] OriginalSmoothHelicoid.topology OriginalSmoothHelicoid.separation
  OriginalSmoothHelicoid.charts OriginalSmoothHelicoid.manifold

noncomputable def OriginalSmoothHelicoid.image (surface : OriginalSmoothHelicoid) : Set (EuclideanSpace ℝ (Fin 3)) :=
  range (coordinateToEuclidean ∘ surface.position)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.image
