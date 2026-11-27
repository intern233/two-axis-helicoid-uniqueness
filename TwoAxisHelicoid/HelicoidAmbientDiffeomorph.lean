import TwoAxisHelicoid.HelicoidAmbientIsotopy
import TwoAxisHelicoid.NormalFiberDiffeomorph
import TwoAxisHelicoid.SmoothSupportedHomeomorph
import TwoAxisHelicoid.HelicoidFiberChartSmooth

namespace TwoAxisHelicoid
open Set
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- Each time slice of the actual ambient straightening has a smooth
inverse as well as a smooth forward map, including across the tube edge. -/
theorem helicoidAmbientIsotopy_smooth {χ : ℝ → ℝ} {C U time : ℝ}
    (hχ : FiberCutoff χ C (1/2)) {u : ℝ × ℝ → ℝ}
    (hχs : ContDiff ℝ (∞ : WithTop ℕ∞) χ) (hus : ContDiff ℝ (∞ : WithTop ℕ∞) u)
    (hu : ∀ p, |u p| ≤ U) (hsmall : U*C < 1) (htime : time ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (helicoidAmbientIsotopy hχ hus.continuous hu hsmall htime) ∧
      ContDiff ℝ (∞ : WithTop ℕ∞) (helicoidAmbientIsotopy hχ hus.continuous hu hsmall htime).symm := by
  apply extendSupportedHomeomorph_smooth
  · intro y hy
    change ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun y => helicoidFiberChart
      (normalFiberHomeomorph hχ hus.continuous hu hsmall htime (helicoidFiberChart.symm y))) y
    exact helicoidFiberChart_contDiff.contDiffAt.comp y
      ((normalFiberShift_contDiff hχs hus time).contDiffAt.comp y
        (helicoidFiberChart_symm_contDiffAt hy))
  · intro y hy
    change ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun y => helicoidFiberChart
      ((normalFiberHomeomorph hχ hus.continuous hu hsmall htime).symm (helicoidFiberChart.symm y))) y
    exact helicoidFiberChart_contDiff.contDiffAt.comp y
      ((normalFiberHomeomorph_symm_contDiff hχ hχs hus hu hsmall htime).contDiffAt.comp y
        (helicoidFiberChart_symm_contDiffAt hy))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidAmbientIsotopy_smooth
