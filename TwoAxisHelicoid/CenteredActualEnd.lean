import TwoAxisHelicoid.CenteredActualImmersion
import TwoAxisHelicoid.ClosedImmersionHelicoidalEnd

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology Manifold

theorem centeredActualTorusImmersion_hasHelicoidalC1End {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    HasHelicoidalC1End (centeredActualTorusImmersion ht ha hc hG hH) := by
  let R := Homeomorph.addRight (actualGlobalImmersion t a c ht 1)
  apply HasHelicoidalC1End.of_isometry R
  · intro v w
    apply Finset.sum_congr rfl
    intro j _
    change (v j+actualGlobalImmersion t a c ht 1 j-(w j+actualGlobalImmersion t a c ht 1 j))^2 = _
    ring
  · have he : R ∘ centeredActualTorusImmersion ht ha hc hG hH =
        (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) => actualTorusImmersion ht ha hc hG hH q.1) := by
      funext q
      exact sub_add_cancel _ _
    rw [he]
    exact actualTorusImmersion_hasHelicoidalC1End ht ha hc hG hH

theorem coordinateMeanCurvature_congr {X Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (he : X =ᶠ[𝓝 z] Y) : coordinateMeanCurvature X z = coordinateMeanCurvature Y z := by
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have hdd := (he.iteratedFDeriv ℝ 2).self_of_nhds
  simp only [coordinateMeanCurvature,hd,hdd]

/-- The actual centered quotient map has exactly the constructed minimal
primitive as its local expression in its manifold atlas. -/
theorem centeredActualTorusImmersion_chart_eventuallyEq {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    centeredActualTorusImmersion ht ha hc hG hH ∘ (chartAt ℂ q).symm =ᶠ[𝓝 (chartAt ℂ q q)]
      centeredActualPrimitive t a c ht := by
  let L := rhombicPeriodPair t ht
  have hcharts := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := ℂ) (puncturedPeriodTorusOpen L) (x := q)
  filter_upwards [hcharts] with w hw
  dsimp only [Function.comp_def] at hw
  change actualTorusImmersion ht ha hc hG hH ((chartAt ℂ q).symm w).1-
      actualGlobalImmersion t a c ht 1 = centeredActualPrimitive t a c ht w
  have he : actualTorusImmersion ht ha hc hG hH ((chartAt ℂ q).symm w).1 =
      actualTorusImmersion ht ha hc hG hH ((chartAt ℂ q.1).symm w) := by
    simpa only using! congrArg (actualTorusImmersion ht ha hc hG hH) hw.symm
  rw [he,periodTorus_chart_symm_eq_projection (rhombicPeriodPair t ht) q.1]
  rfl

theorem centeredActualTorusImmersion_chart_mean_curvature_zero {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    coordinateMeanCurvature (centeredActualTorusImmersion ht ha hc hG hH ∘ (chartAt ℂ q).symm)
      (chartAt ℂ q q) = 0 := by
  rw [coordinateMeanCurvature_congr (centeredActualTorusImmersion_chart_eventuallyEq ht ha hc hG hH q)]
  exact centeredActualPrimitive_mean_curvature_zero ht ha hc hG hH
    (puncturedPeriodTorus_chart_not_lattice _ q)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.centeredActualTorusImmersion_hasHelicoidalC1End
#print axioms TwoAxisHelicoid.centeredActualTorusImmersion_chart_mean_curvature_zero
