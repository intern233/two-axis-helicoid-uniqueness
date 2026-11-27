import TwoAxisHelicoid.EmbeddedPitchGeometry
import TwoAxisHelicoid.MarkedMinimalGeometricSurface
import TwoAxisHelicoid.OriginalHelicoidRepresentative
import TwoAxisHelicoid.OriginalSurfaceNonperiodicity

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology Manifold

/-- The real geometric hypotheses hold for the actual immersion obtained
from a two-axis harmonic plane lift, in every covering chart. -/
theorem harmonic_quotient_pulled_regular {L : PeriodPair} {P : ℂ → Fin 3 → ℝ}
    (h : TwoAxisHarmonicConformalImmersion L P) (z : ℂ) (hz : z ∉ L.lattice) :
    let F := puncturedTorusPullback L (harmonicTorusImmersion h)
    (∀ j, HarmonicAt (fun w => F w j) z) ∧ ConformalCoordinateDerivatives F z ∧ Function.Injective (fderiv ℝ F z) := by
  let F := puncturedTorusPullback L (harmonicTorusImmersion h)
  have e : F =ᶠ[𝓝 z] P := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    change w ∉ L.lattice at hw
    simpa only [F,puncturedTorusPullback,dite_eq_left hw] using! harmonicTorusImmersion_projection h hw
  refine ⟨fun j => (harmonicAt_congr_nhds (e.mono fun w hw => congrFun hw j)).mpr (h.harmonic z hz j),?_,?_⟩
  · apply (conformalCoordinateDerivatives_iff_dot ((h.differentiable z hz).congr_of_eventuallyEq e)).mpr
    rw [e.fderiv_eq]
    exact (conformalCoordinateDerivatives_iff_dot (h.differentiable z hz)).mp (h.conformal z hz)
  · change Function.Injective (fderiv ℝ F z)
    rw [e.fderiv_eq]
    exact h.immersion z hz

/-- Every proposed unit-pitch member of the Appendix B sequence is
literally the image of a smooth embedded genus-one minimal surface
with the required original end, marked axes and no screw period. -/
theorem embedded_pitch_actual_geometric_representative_with_pitch (W : PitchNormalizedBasicImmersion)
    (hW : W ∈ embeddedPitchFamily) :
    ∃ s : OriginalHelicoidRepresentative, s.image = W.image ∧ s.axes.pitch = 2*(verticalA W.t-1)/W.c ∧ |s.axes.pitch| = 1 ∧
      s.axes.horizontalPoint = 0 ∧ s.axes.horizontalDirection = 1 ∧
      ∀ (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) (d : ℝ), d ≠ 0 → (∀ v, R v 2 = v 2+d) →
        R '' range s.position ≠ range s.position := by
  obtain ⟨h,hα,hu,he,_,hhor,hver,hend⟩ := embedded_pitch_family_unit_helicoid_geometry W hW
  let L := rhombicPeriodPair W.t W.ht
  let F := harmonicTorusImmersion h
  let α := 2*(verticalA W.t-1)/W.c
  have hx (r : ℝ) : r • (![1,0,0] : Fin 3 → ℝ) = ![r,0,0] := by
    ext j
    fin_cases j <;> simp
  let axes : OriginalHelicoidAxes (range F) := {
    horizontalDirection := 1, unit := norm_one, horizontalPoint := 0
    horizontal := fun r => by simpa only [Complex.one_re,Complex.one_im,zero_add,hx] using hhor r
    vertical := hver, pitch := α, pitch_ne := hα }
  let S := markedMinimalGeometricSurface L F he axes (fun z hz => (harmonic_quotient_pulled_regular h z hz).1)
    (fun z hz => (harmonic_quotient_pulled_regular h z hz).2.1) (fun z hz => (harmonic_quotient_pulled_regular h z hz).2.2)
  have hz : (![0,0,0] : Fin 3 → ℝ) = 0 := by ext j; fin_cases j <;> rfl
  let s : OriginalHelicoidRepresentative := { S with
    graphEnd := by
      change HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,0] ∘ F)
      rw [hz]
      exact hend }
  refine ⟨s,?_,rfl,hu,rfl,rfl,fun R _ hd hR => s.no_nonzero_screw_step R hd hR⟩
  change range (coordinateToEuclidean ∘ harmonicTorusImmersion h) = _
  rw [Set.range_comp,harmonicTorusImmersion_range,image_image]
  rfl

theorem embedded_pitch_actual_geometric_representative (W : PitchNormalizedBasicImmersion)
    (hW : W ∈ embeddedPitchFamily) :
    ∃ s : OriginalHelicoidRepresentative, s.image = W.image ∧ |s.axes.pitch| = 1 ∧
      s.axes.horizontalPoint = 0 ∧ s.axes.horizontalDirection = 1 ∧
      ∀ (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) (d : ℝ), d ≠ 0 → (∀ v, R v 2 = v 2+d) →
        R '' range s.position ≠ range s.position := by
  obtain ⟨s,e,_,h⟩ := embedded_pitch_actual_geometric_representative_with_pitch W hW
  exact ⟨s,e,h⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_pitch_actual_geometric_representative
