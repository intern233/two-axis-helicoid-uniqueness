import TwoAxisHelicoid.HarmonicIntegerCoordinateData
import TwoAxisHelicoid.AnalyticAxisNormalization
import TwoAxisHelicoid.HeightInverseRegularity
import TwoAxisHelicoid.HeightEndAxis

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

noncomputable def heightCenteredPrimitive (α b : ℝ) (X : ℂ → Fin 3 → ℝ) (z : ℂ) : Fin 3 → ℝ :=
  verticalRotation I (α • (verticalRotation I (X z)-![0,0,b]))

/-- Arbitrarily thin analytic ends for the full integer family of actual
two-axis harmonic conformal maps. The integer is unrestricted; in
particular the conclusion does not assume the branch to be proved later. -/
theorem harmonic_integer_data_normalized_analytic_thin_end
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    ∃ (K f : ℂ → ℂ) (b R : ℝ),
      Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧ AnalyticAt ℂ f 0 ∧
      (∀ᶠ ξ : ℂ in cobounded ℂ, AnalyticAt ℂ K ξ) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (((2*(a-m)/c : ℝ) : ℂ)*actualComplexHeight t a c ht z) = z) ∧
      (∀ᶠ ξ : ℂ in cobounded ℂ, ((2*(a-m)/c : ℝ) : ℂ)*actualComplexHeight t a c ht (K ξ) = ξ) ∧
      (∀ ξ : ℂ, R < ‖ξ‖ → HasFDerivAt
        (fun ξ => heightCenteredPrimitive (2*(a-m)/c) b X (K ξ))
        (nullRealDerivative (weierstrassTriple (exp (I*ξ+infinityCorrection f ξ)) 1)) ξ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ ξ : ℂ, S < ‖ξ‖ →
        coordinateToTube (heightCenteredPrimitive (2*(a-m)/c) b X (K ξ)) ∈ helicoidTubeEquiv.target ∧
        |helicoidSignedDistance (coordinateToTube (heightCenteredPrimitive (2*(a-m)/c) b X (K ξ)))| ≤ ε := by
  let α : ℝ := 2*(a-m)/c
  have hα : α ≠ 0 := integer_helicoidal_pitch_ne_zero ha hc m
  have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  have hXd := harmonic_integer_gauss_data_has_coordinate_differential ht ha hc m hX hh hg
  obtain ⟨K,f,b,R,hK,hf,hf0,hKL,hcoord⟩ := integer_primitive_analytic_height_end_coordinate m ht ha hc hXd
  let Y : ℂ → Fin 3 → ℝ := fun ξ => verticalRotation I (X (K ξ))
  have hKR : ∀ᶠ ξ : ℂ in cobounded ℂ, actualComplexHeight t a c ht (K ξ) = ξ := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with ξ hξ
    exact (hcoord ξ hξ).1
  have haxisEv : ∀ᶠ ξ : ℂ in cobounded ℂ, ξ.im = 0 → Y ξ 0 = 0 ∧ Y ξ 1 = 0 := by
    filter_upwards [actual_height_inverse_preserves_axis ht hK hKL hKR,
      hK.eventually (rhombic_puncture_eventually_off_lattice ht)] with ξ hξ hξn
    intro hi
    have hz := hX.vertical_axis_zero hξn (hξ hi)
    simp [Y,verticalRotation_apply,hz.1,hz.2]
  obtain ⟨A,_hA,hA⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp haxisEv
  have haxis : ∃ A : ℝ, ∀ x : ℝ, A < |x| → Y (x : ℂ) 0 = 0 ∧ Y (x : ℂ) 1 = 0 := by
    refine ⟨A,?_⟩
    intro x hx
    have hn : A ≤ ‖(x : ℂ)‖ := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx.le
    exact hA hn (by simp)
  obtain ⟨g,S,hg,hD,hthin⟩ := analytic_axis_end_normalized_thin hα b R hf hf0
    (fun ξ hξ => (hcoord ξ hξ).2.1) (fun ξ hξ => (hcoord ξ hξ).2.2) haxis
  have hKa := actual_height_inverse_eventually_analytic ht hc hK hKR
  have hdiv := complex_div_real_tendsto_cobounded hα
  refine ⟨(fun ξ => K (ξ/(α : ℂ))),g,b,S,hK.comp hdiv,hg,?_,?_,?_,hD,hthin⟩
  · filter_upwards [hdiv.eventually hKa] with ξ hξ
    have hd : AnalyticAt ℂ (fun z : ℂ => z/(α : ℂ)) ξ :=
      analyticAt_id.div analyticAt_const hαc
    exact hξ.comp (f := fun z : ℂ => z/(α : ℂ)) hd
  · filter_upwards [hKL] with z hz
    change K (((α : ℂ)*actualComplexHeight t a c ht z)/(α : ℂ)) = z
    have he : ((α : ℂ)*actualComplexHeight t a c ht z)/(α : ℂ) = actualComplexHeight t a c ht z := by
      field_simp
    rwa [he]
  · filter_upwards [hdiv.eventually hKR] with ξ hξ
    change (α : ℂ)*actualComplexHeight t a c ht (K (ξ/(α : ℂ))) = ξ
    rw [hξ]
    field_simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_data_normalized_analytic_thin_end
