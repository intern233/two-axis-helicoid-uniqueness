import TwoAxisHelicoid.CoordinateMetricEnd
import TwoAxisHelicoid.PuncturePathLength

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

theorem coordinateMetric_continuousAt {t a c : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    ContinuousAt (fun w => Real.sqrt (nullMetric (coordinateData t a c ht w))) z := by
  have hcoord := (coordinateData_analyticAt (a := a) (c := c) ht hz).continuousAt
  have hj (j : Fin 3) : ContinuousAt (fun w => (coordinateData t a c ht w j).re) z :=
    Complex.continuous_re.continuousAt.comp ((continuous_apply j).continuousAt.comp hcoord)
  exact (((hj 0).pow 2).add ((hj 1).pow 2) |>.add ((hj 2).pow 2)).sqrt

/-- Every smooth path approaching the puncture has infinite length in the
actual induced conformal metric. This is the end-completeness part; no global
period closure, properness or embeddedness is asserted here. -/
theorem actual_end_curve_infinite_length {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 1) (hc : c ≠ 0)
    {γ v : ℝ → ℂ} (hd : ∀ u < 1, HasDerivAt γ (v u) u)
    (hv : ContinuousOn v (Iio 1))
    (hreg : ∀ u < 1, γ u ∉ (rhombicPeriodPair t ht).lattice)
    (hlim : Tendsto γ (𝓝[<] (1:ℝ)) (𝓝 (0:ℂ))) :
    ∃ b < (1:ℝ), Tendsto
      (fun s => ∫ u : ℝ in b..s,
        Real.sqrt (nullMetric (coordinateData t a c ht (γ u)))*‖v u‖)
      (𝓝[<] (1:ℝ)) atTop := by
  have hn (u : ℝ) (hu : u < 1) : γ u ≠ 0 := by
    intro he
    exact hreg u hu (he ▸ (rhombicPeriodPair t ht).lattice.zero_mem)
  have hpunct : Tendsto γ (𝓝[<] (1:ℝ)) (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hlim,?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hn u hu
  have hbound := hpunct.eventually (coordinateMetric_puncture_lower_bound ht ha hc)
  obtain ⟨b₀,hb₀,hbnd⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hbound
  obtain ⟨b,hb₀b,hb1⟩ := exists_between (show b₀ < (1:ℝ) from hb₀)
  let ρ : ℝ → ℝ := fun u => Real.sqrt (nullMetric (coordinateData t a c ht (γ u)))
  have hρ : ContinuousOn ρ (Iio 1) := by
    intro u hu
    exact ((coordinateMetric_continuousAt ht (hreg u hu)).comp
      (f := γ) (hd u hu).continuousAt).continuousWithinAt
  refine ⟨b,hb1,?_⟩
  apply weighted_path_length_tendsto_top (C := |c|/2) hb1
    (div_pos (abs_pos.mpr hc) (by norm_num))
    (fun u hu => hd u hu.2) (hv.mono (fun _ hu => hu.2))
    (hρ.mono (fun _ hu => hu.2)) (fun u hu => hn u hu.2) _ hpunct
  intro u hu
  have h := hbnd ⟨hb₀b.trans_le hu.1,hu.2⟩
  change |c|/2/‖γ u‖^2 ≤ ρ u
  rw [div_div]
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_end_curve_infinite_length
