import TwoAxisHelicoid.ActualGlobalImmersion
import TwoAxisHelicoid.PeriodTorusDescent

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology

/-- Descent of the constructed, genuinely periodic map to the actual torus. -/
noncomputable def actualTorusImmersion {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) : PeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ :=
  periodTorusLift (rhombicPeriodPair t ht) (actualGlobalImmersion t a c ht)
    (actualGlobalImmersion_add_lattice ht ha hc hG hH)

@[simp] theorem actualTorusImmersion_projection {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) (z : ℂ) :
    actualTorusImmersion ht ha hc hG hH (periodTorusProjection (rhombicPeriodPair t ht) z) =
      actualGlobalImmersion t a c ht z := rfl

theorem actualTorusImmersion_continuous_punctured {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    Continuous (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      actualTorusImmersion ht ha hc hG hH q.1) := by
  apply periodTorusLift_continuous_punctured
  intro z hz
  exact ((actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.1 z hz).continuousAt

/-- Each point of the punctured quotient has a genuine quotient coordinate
chart in which the descended map is the real part of a holomorphic primitive
with the actual manuscript coordinate differential and injective real derivative. -/
theorem actualTorusImmersion_local_coordinates {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0)
    (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    ∃ (z : ℂ) (e : OpenPartialHomeomorph ℂ (PeriodTorus (rhombicPeriodPair t ht)))
      (F : ℂ → Fin 3 → ℂ),
      z ∉ (rhombicPeriodPair t ht).lattice ∧ z ∈ e.source ∧ e z = q.1 ∧
      (e : ℂ → PeriodTorus (rhombicPeriodPair t ht)) = periodTorusProjection (rhombicPeriodPair t ht) ∧
      AnalyticAt ℂ F z ∧ HasDerivAt F (coordinateData t a c ht z) z ∧
      (actualTorusImmersion ht ha hc hG hH ∘ e) =ᶠ[𝓝 z] (fun w => coordinateRealPart (F w)) ∧
      HasFDerivAt (actualTorusImmersion ht ha hc hG hH ∘ e)
        (nullRealDerivative (coordinateData t a c ht z)) z ∧
      Function.Injective (fderiv ℝ (actualTorusImmersion ht ha hc hG hH ∘ e) z) := by
  obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
  have hproj : periodTorusProjection (rhombicPeriodPair t ht) z = q.1 := hz
  have hnot : z ∉ (rhombicPeriodPair t ht).lattice := by
    intro h
    apply q.2
    rw [← hproj,periodTorusProjection_eq_zero]
    exact h
  obtain ⟨e,hze,he⟩ := periodTorusProjection_isLocalHomeomorph (rhombicPeriodPair t ht) z
  obtain ⟨F,hFa,hFd,hFe⟩ := actualGlobalImmersion_local_holomorphic ht ha hc hG hH hnot
  have hcomp : actualTorusImmersion ht ha hc hG hH ∘ e = actualGlobalImmersion t a c ht := by
    rw [← he]
    rfl
  have hD := (actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.2.2 z hnot
  refine ⟨z,e,F,hnot,hze,?_,he.symm,hFa,hFd,?_,?_,?_⟩
  · rw [← he]
    exact hproj
  · rw [hcomp]
    exact hFe
  · rw [hcomp]
    exact hD.1
  · rw [hcomp]
    exact hD.2.1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualTorusImmersion_local_coordinates
