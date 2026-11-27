import TwoAxisHelicoid.ActualLocalImmersion
import TwoAxisHelicoid.NullMetricBound

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

theorem coordinateMetric_ge_height {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 1) (hc : c ≠ 0) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    |c| * ‖(rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a‖ ≤
      Real.sqrt (nullMetric (coordinateData t a c ht z)) := by
  have h := sqrt_nullMetric_ge_third_norm
    (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz)
  simpa [coordinateData,norm_mul] using h

theorem weierstrass_pole_lower_bound {t : ℝ} (ht : 0 < t) (a : ℂ) :
    ∀ᶠ z : ℂ in 𝓝[≠] 0,
      (1/2:ℝ)/‖z‖^2 ≤ ‖(rhombicPeriodPair t ht).weierstrassP z-
        (rhombicPeriodPair t ht).weierstrassP a‖ := by
  let L := rhombicPeriodPair t ht
  have hP := (L.analyticAt_weierstrassPExcept 0).continuousAt
  have hc : ContinuousAt (fun z : ℂ => z^2*(L.weierstrassPExcept 0 z-L.weierstrassP a)) 0 := by
    fun_prop
  have hs : ∀ᶠ z : ℂ in 𝓝 0, ‖z^2*(L.weierstrassPExcept 0 z-L.weierstrassP a)‖ < (1/2:ℝ) := by
    have h := hc.norm.eventually (eventually_lt_nhds
      (by norm_num : ‖(0:ℂ)^2*(L.weierstrassPExcept 0 0-L.weierstrassP a)‖ < (1/2:ℝ)))
    exact h
  filter_upwards [hs.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hsmall hz
  have hz0 : z ≠ 0 := hz
  have hPz : L.weierstrassP z = L.weierstrassPExcept 0 z+1/z^2 := by
    simpa using (L.weierstrassPExcept_add (0:L.lattice) z).symm
  have he : z^2*(L.weierstrassP z-L.weierstrassP a) =
      1+z^2*(L.weierstrassPExcept 0 z-L.weierstrassP a) := by
    rw [hPz]
    field_simp
    ring
  have htri := norm_sub_norm_le (1:ℂ) (-z^2*(L.weierstrassPExcept 0 z-L.weierstrassP a))
  simp only [norm_one,neg_mul,norm_neg,sub_neg_eq_add] at htri
  rw [← he] at htri
  simp only [norm_mul,norm_pow] at htri hsmall
  apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hz0) 2)).mpr
  change (1/2:ℝ) ≤ ‖L.weierstrassP z-L.weierstrassP a‖*‖z‖^2
  nlinarith

theorem coordinateMetric_puncture_lower_bound {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 1) (hc : c ≠ 0) :
    ∀ᶠ z : ℂ in 𝓝[≠] 0,
      |c|/(2*‖z‖^2) ≤ Real.sqrt (nullMetric (coordinateData t a c ht z)) := by
  let L := rhombicPeriodPair t ht
  have hreg := L.compl_lattice_sdiff_singleton_mem_nhds 0
  have hreg' : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ∉ (L.lattice : Set ℂ) \ {0} :=
    nhdsWithin_le_nhds hreg
  filter_upwards [weierstrass_pole_lower_bound ht (a:ℂ),
    hreg',self_mem_nhdsWithin] with z hp hz hz0
  have hnz : z ≠ 0 := hz0
  have hzL : z ∉ L.lattice := fun h => hz ⟨h,hnz⟩
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg c)
  have hh := coordinateMetric_ge_height ht ha hc hzL
  calc
    |c|/(2*‖z‖^2) = |c| * ((1/2:ℝ)/‖z‖^2) := by ring
    _ ≤ _ := hm.trans hh

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.coordinateMetric_puncture_lower_bound
