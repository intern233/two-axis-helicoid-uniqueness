import TwoAxisHelicoid.TorusSpatialConormalFlux
import TwoAxisHelicoid.IntrinsicGaussPhaseRigidity
import TwoAxisHelicoid.LopezRosRotationTangent
import TwoAxisHelicoid.CertifiedC1HelicoidEnd
import TwoAxisHelicoid.AxisSpatialNormalization

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace Topology

/-- A marked embedded genus-one helicoid, with its actual position map,
oriented conformal charts and one nonplanar helicoidal end. The vertical
direction is measured in the asymptotic axis frame. No straight line or
axis reflection of the surface is required. -/
structure MarkedEmbeddedHelicoidForFlux (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) : Prop where
  regular : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
    ConformalCoordinateDerivatives (puncturedTorusPullback L X) z
  immersion : ∀ z ∉ L.lattice, Function.Injective (fderiv ℝ (puncturedTorusPullback L X) z)
  closedEmbedding : IsClosedEmbedding (coordinateToEuclidean ∘ X)
  asymptotic : ∃ (k : ℝ) (u : ℂ) (b : Fin 3 → ℝ), k ≠ 0 ∧ ‖u‖ = 1 ∧
    HasHelicoidC1End (fun q => coordinateToTube (k • verticalRotation u (X q)+b))

/-- The nonvertical-flux implication from Bernstein–Breiner, Lemma 2.2
and the end of the proof of Theorem 0.1 (Duke Math. J. 159, 2011).
Its content concerns the Euclidean integral of the surface conormal. -/
def MarkedBernsteinBreinerFluxPrinciple : Prop :=
  ∀ (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ),
    MarkedEmbeddedHelicoidForFlux L X → HasSpatialNonverticalFlux L X

/-- The marked-surface consequences of the published conormal-flux
theorem. Equality of data yields the same phase for the Gauss map and
the actual global immersion. Equality of principal parts or first-order
period closure have their respective rigidity conclusions. -/
theorem embedded_marked_helicoid_flux_rigidity (bbs : MarkedBernsteinBreinerFluxPrinciple)
    (L : PeriodPair) (X Y : PuncturedPeriodTorus L → Fin 3 → ℝ) (hX : MarkedEmbeddedHelicoidForFlux L X)
    (hY : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z)
    (ho : meromorphicOrderAt (fun z => torusImmersionForms L X z 2) 0 = (-2:ℤ)) :
    ((∀ z ∉ L.lattice, torusImmersionForms L Y z 2 = torusImmersionForms L X z 2) →
      (∀ z ∉ L.lattice, torusImmersionForms L X z 2 ≠ 0 →
        immersionGaussLog (torusImmersionForms L Y) z = immersionGaussLog (torusImmersionForms L X) z) →
      ∃ θ : ℝ, ∃ b : Fin 3 → ℝ, (∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (X q)+b) ∧
        ∀ z ∉ L.lattice, nullGauss (torusImmersionForms L Y z) = exp ((θ:ℂ)*I)*nullGauss (torusImmersionForms L X z)) ∧
    (CommonLaurentPartAt (fun z => torusImmersionForms L X z 2) (fun z => torusImmersionForms L Y z 2) 0 →
      (∀ z, CommonLaurentPartAt (immersionGaussLog (torusImmersionForms L X)) (immersionGaussLog (torusImmersionForms L Y)) z) →
      ∃ θ : ℝ, ∃ b : Fin 3 → ℝ, ∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (X q)+b) ∧
    ∀ {k : ℝ → ℂ} {d : ℂ}, HasDerivAt k d 0 → k 0 = 1 →
      (LopezRosClosedToFirstOrder L X k ↔ d.re = 0) := by
  have hflux := (torus_spatial_nonvertical_flux_iff L X hX.regular).mp (bbs L X hX)
  exact ⟨fun hh hg => intrinsic_gauss_and_immersion_phase_rigidity L X Y hX.regular hY ho hh hg hflux,
    fun hh hg => intrinsic_punctured_torus_fixed_parts_rigidity L X Y hX.regular hY ho hh hg hflux,
    fun hk hk0 => lopez_ros_first_order_closure_iff_rotation L X hX.regular hflux hk hk0⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_marked_helicoid_flux_rigidity
