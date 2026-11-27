import TwoAxisHelicoid.HarmonicTorusRigidityData
import TwoAxisHelicoid.PeriodicManifoldDifferential
import TwoAxisHelicoid.ActualTorusManifoldDifferential
import TwoAxisHelicoid.ProperImmersionCompleteness
import TwoAxisHelicoid.NullEuclideanMetric
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace Manifold
open scoped Topology ContDiff Manifold

theorem harmonic_marked_torus_contMDiff (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hh : ∀ z ∉ L.lattice, ∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ω X := by
  have he : X = torusFilledPosition L X ∘ Subtype.val := funext fun q => (torusFilledPosition_eq L X q).symm
  rw [he]
  intro q
  have h : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ω (torusFilledPosition L X) q.1 := by
    apply periodTorusLift_contMDiffAt_of_contDiffAt
    exact contDiffAt_pi.mpr fun j => (HarmonicAt.analyticAt (hh _ (puncturedPeriodTorus_chart_not_lattice L q) j)).contDiffAt
  exact h.comp q (contMDiff_subtype_val (U := puncturedPeriodTorusOpen L)).contMDiffAt

theorem harmonic_marked_torus_hasMFDerivAt (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hh : ∀ z ∉ L.lattice, ∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z)
    (q : PuncturedPeriodTorus L) : HasMFDerivAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q
      (fderiv ℝ (puncturedTorusPullback L X) (chartAt ℂ q q)) := by
  let z := chartAt ℂ q q
  have hp := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) (puncturedPeriodTorusOpen L) (x := q)
  have he : (fun w : ℂ => X ((chartAt ℂ q).symm w)) =ᶠ[𝓝 z] puncturedTorusPullback L X := by
    filter_upwards [hp,L.isClosed_lattice.isOpen_compl.mem_nhds (puncturedPeriodTorus_chart_not_lattice L q)] with w hw hn
    change w ∉ L.lattice at hn
    have hproj : ((chartAt ℂ q).symm w).1 = periodTorusProjection L w := by
      rw [← periodTorus_chart_symm_eq_projection L q.1]
      exact hw.symm
    change X ((chartAt ℂ q).symm w) = puncturedTorusPullback L X w
    rw [show puncturedTorusPullback L X w = X (puncturedPlaneProjection L ⟨w,hn⟩) by simp [puncturedTorusPullback,hn]]
    exact congrArg X (Subtype.ext hproj)
  have ha : AnalyticAt ℝ (puncturedTorusPullback L X) z :=
    analyticAt_pi_iff.mpr fun j => HarmonicAt.analyticAt (hh _ (puncturedPeriodTorus_chart_not_lattice L q) j)
  have h := ha.differentiableAt.hasFDerivAt.congr_of_eventuallyEq he
  refine ⟨(harmonic_marked_torus_contMDiff L X hh).continuous.continuousAt,?_⟩
  simpa only [writtenInExtChartAt,mfld_simps] using! h.hasFDerivWithinAt (s := range 𝓘(ℝ,ℂ))

/-- The completeness hypothesis in the geometric flux theorem follows
from closed embedding, actual harmonicity and regularity in the torus
charts. Completeness is for the induced Riemannian length distance. -/
theorem harmonic_marked_torus_complete (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hh : ∀ z ∉ L.lattice, ∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z)
    (hi : ∀ z ∉ L.lattice, Function.Injective (fderiv ℝ (puncturedTorusPullback L X) z))
    (he : IsClosedEmbedding (coordinateToEuclidean ∘ X)) :
    ∃ (hX : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 3)) 1 (coordinateToEuclidean ∘ X))
      (hD : ∀ q, Function.Injective (mvfderiv 𝓘(ℝ,ℂ) (coordinateToEuclidean ∘ X) q)),
      @CompleteSpace (PuncturedPeriodTorus L) (euclideanImmersionEMetricSpace (coordinateToEuclidean ∘ X) hX hD).toUniformSpace := by
  have hX := coordinateToEuclidean.contMDiff.comp ((harmonic_marked_torus_contMDiff L X hh).of_le (by simp : (1:WithTop ℕ∞) ≤ ω))
  have hD (q : PuncturedPeriodTorus L) : Function.Injective (mvfderiv 𝓘(ℝ,ℂ) (coordinateToEuclidean ∘ X) q) := by
    unfold mvfderiv
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (coordinateToEuclidean (X q))).injective.comp
    change Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 3)) (coordinateToEuclidean ∘ X) q)
    rw [(coordinateToEuclidean.hasFDerivAt.hasMFDerivAt.comp q (harmonic_marked_torus_hasMFDerivAt L X hh q)).mfderiv]
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective.comp (hi _ (puncturedPeriodTorus_chart_not_lattice L q))
  refine ⟨hX,hD,?_⟩
  simpa only using! proper_euclideanImmersion_complete _ hX hD he.isProperMap

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_marked_torus_complete
