import TwoAxisHelicoid.ActualTorusHeightChart
import TwoAxisHelicoid.HarmonicIntegerTorusGeometry

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology
set_option maxHeartbeats 1000000

/-- Every integer branch of an actual two-axis harmonic conformal map
has a genuine analytic thin height chart on its punctured torus. The same chart satisfies the analytic differential and
arbitrarily thin tube estimates; neither is an extra hypothesis. -/
theorem harmonic_integer_torus_analytic_thin_chart
    {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω : ℂ, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    ∃ (e : OpenPartialHomeomorph (PuncturedPeriodTorus (rhombicPeriodPair t ht)) ℂ)
      (f : ℂ → ℂ) (b R : ℝ), AnalyticAt ℂ f 0 ∧
      (∀ S : ℝ, ∃ C : Set (PuncturedPeriodTorus (rhombicPeriodPair t ht)), IsCompact C ∧
        ∀ q ∉ C, q ∈ e.source ∧ S < ‖e q‖) ∧
      (∀ ξ : ℂ, R < ‖ξ‖ → HasFDerivAt
        (fun ξ => heightCenteredTorusPrimitive (rhombicPeriodPair t ht) (2*(a-m)/c) b X hp (e.symm ξ).1)
        (nullRealDerivative (weierstrassTriple (exp (I*ξ+infinityCorrection f ξ)) 1)) ξ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ ξ : ℂ, S < ‖ξ‖ →
        coordinateToTube (heightCenteredTorusPrimitive (rhombicPeriodPair t ht) (2*(a-m)/c) b X hp (e.symm ξ).1)
          ∈ helicoidTubeEquiv.target ∧
        |helicoidSignedDistance (coordinateToTube
          (heightCenteredTorusPrimitive (rhombicPeriodPair t ht) (2*(a-m)/c) b X hp (e.symm ξ).1))| ≤ ε := by
  let L := rhombicPeriodPair t ht
  let := periodTorus_compactSpace L
  let := periodTorus_t2Space L
  let α : ℝ := 2*(a-m)/c
  have hα : α ≠ 0 := integer_helicoidal_pitch_ne_zero ha hc m
  obtain ⟨K,f,b,R,hK,hf,hKa,hKL,hKR,hD,hthin⟩ :=
    harmonic_integer_data_normalized_analytic_thin_end ht ha hc m hX hh hg
  let H : ℂ → ℂ := fun z => (α : ℂ)*actualComplexHeight t a c ht z
  have hH : Tendsto H (𝓝[≠] 0) (cobounded ℂ) :=
    (complex_mul_real_tendsto_cobounded hα).comp (actualComplexHeight_tendsto (a := a) ht hc)
  have hHc : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ContinuousAt H z := by
    filter_upwards [rhombic_puncture_eventually_off_lattice ht] with z hz
    exact ((actualComplexHeight_hasDerivAt ht hz).const_mul (α : ℂ)).continuousAt
  obtain ⟨h,heH,heK,hs,htar⟩ := puncture_inverse_open_chart hH hK hKL hKR hHc
    (hKa.mono (fun _ hh => hh.continuousAt))
  obtain ⟨eQ,heQ0,heQ⟩ := periodTorusProjection_isLocalHomeomorph L (0 : ℂ)
  have hQ0 : eQ 0 = 0 := by
    rw [← heQ]
    exact (periodTorusProjection_eq_zero L 0).mpr L.lattice.zero_mem
  have hQo : IsOpenMap (eQ : ℂ → PeriodTorus L) := by
    rw [← heQ]
    exact QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap
  have hne : Nonempty (PuncturedPeriodTorus L) := by
    refine ⟨⟨periodTorusProjection L 1,?_⟩⟩
    intro hh
    exact real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0 : ℝ) < 1) (by norm_num)
      ((periodTorusProjection_eq_zero L 1).mp hh)
  obtain ⟨e,htail,hinv⟩ := projected_puncture_height_chart hne eQ heQ0 hQ0 hQo h hs htar
    (heH.symm ▸ hH) (heK.symm ▸ hK)
  have heq : (fun ξ => heightCenteredTorusPrimitive L α b X hp (e.symm ξ).1) =ᶠ[cobounded ℂ]
      (fun ξ => heightCenteredPrimitive α b X (K ξ)) := by
    filter_upwards [hinv] with ξ hξ
    rw [hξ.2,heK,← heQ]
    rfl
  have helocal := complex_cobounded_eventuallyEq_nhds heq
  obtain ⟨B,_hB,hB⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp (heq.and helocal)
  refine ⟨e,f,b,max R B,hf,htail,?_,?_⟩
  · intro ξ hξ
    exact (hD ξ ((le_max_left _ _).trans_lt hξ)).congr_of_eventuallyEq
      (hB ((le_max_right _ _).trans hξ.le)).2
  · intro ε hε
    obtain ⟨S,hS⟩ := hthin ε hε
    refine ⟨max S B,?_⟩
    intro ξ hξ
    have hh : heightCenteredTorusPrimitive (rhombicPeriodPair t ht) (2*(a-m)/c) b X hp (e.symm ξ).1 =
        heightCenteredPrimitive (2*(a-m)/c) b X (K ξ) := (hB ((le_max_right _ _).trans hξ.le)).1
    rw [hh]
    exact hS ξ ((le_max_left _ _).trans_lt hξ)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_torus_analytic_thin_chart
