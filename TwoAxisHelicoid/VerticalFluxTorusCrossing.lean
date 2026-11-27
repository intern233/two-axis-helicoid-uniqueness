import TwoAxisHelicoid.LopezRosTorusDoublePoint
import TwoAxisHelicoid.OneEndTorusGaussDivisor

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology

/-- Under the vertical-flux hypothesis the actual single-valued López–Ros
family exists and has interior double points at every sufficiently large
positive multiplier. The location is derived from the end and the
immersion, without axis symmetries or any interior divisor hypotheses. -/
theorem vertical_flux_one_handle_family_eventually_crosses
    (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z ∧
      Function.Injective (fderiv ℝ (puncturedTorusPullback L X) z))
    (hh : meromorphicOrderAt (fun z => torusImmersionForms L X z 2) 0 = (-2:ℤ))
    {κ : ℂ} {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0)
    (hend : ∀ᶠ z in 𝓝[≠] (0:ℂ), logDeriv (nullGauss ∘ torusImmersionForms L X) z = κ/z^2+R z)
    (hflux : ¬ HasIntrinsicNonverticalFlux L X) :
    ∃ (Y : ℂ → PuncturedPeriodTorus L → Fin 3 → ℝ) (a b : ℂ) (ha : a ∉ L.lattice),
      Y 1 = X ∧ (∀ k q, Y k q 2 = X q 2) ∧ OneEndInteriorGaussDivisor L (torusImmersionForms L X) a b ∧
      (∀ k ≠ 0, ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L (Y k) w j) z) ∧
        ConformalCoordinateDerivatives (puncturedTorusPullback L (Y k)) z ∧
        Function.Injective (fderiv ℝ (puncturedTorusPullback L (Y k)) z) ∧
        HasFDerivAt (puncturedTorusPullback L (Y k)) (nullRealDerivative (lopezRosCoefficients k (torusImmersionForms L X z))) z) ∧
      ∀ V ∈ 𝓝 (puncturedPlaneProjection L ⟨a,ha⟩), ∀ᶠ k : ℝ in atTop,
        ∃ u ∈ V, ∃ v ∈ V, u ≠ v ∧ Y (k:ℂ) u = Y (k:ℂ) v := by
  have data := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2.1)
  have nonzero (z : ℂ) (hz : z ∉ L.lattice) : torusImmersionForms L X z ≠ 0 :=
    immersionComplexCoefficient_regular (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((hX z hz).1 j))).differentiableAt (hX z hz).2.2
  obtain ⟨a,b,D⟩ := one_end_torus_has_simple_gauss_divisor L (torusImmersionForms L X)
    data.1 (torusImmersionForms_periodic L X) data.2.1 nonzero hh hR hend
  obtain ⟨Y,h1,h2,hY⟩ := vertical_flux_lopez_ros_immersions L X hX hflux
  refine ⟨Y,a,b,D.zero_regular,h1,h2,D,hY,?_⟩
  intro V hV
  exact lopez_ros_torus_position_eventually_not_injective L X (fun z hz => ⟨(hX z hz).1,(hX z hz).2.1⟩)
    D.zero_regular D.minus_nonzero D.height_zero D.simple_height_zero (fun k : ℝ => Y (k:ℂ))
    (fun k hk z hz => (hY _ (Complex.ofReal_ne_zero.mpr hk.ne') z hz).2.2.2) hV

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.vertical_flux_one_handle_family_eventually_crosses
