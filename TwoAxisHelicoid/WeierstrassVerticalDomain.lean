import TwoAxisHelicoid.WeierstrassAllMonotone
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaG

theorem rhombic_weierstrassP_strictAnti_to_one {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (fun x : ℝ => ((rhombicPeriodPair t ht).weierstrassP x).re) (Ioc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
  · intro x hx
    exact (rhombic_weierstrassP_real_hasDerivAt_of_pos ht ht hx.1
      (lt_of_le_of_lt hx.2 (by norm_num))).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(rhombic_weierstrassP_real_hasDerivAt_of_pos ht ht hx.1 (by linarith [hx.2])).deriv]
    exact rhombic_weierstrassP_derivative_real_neg_of_pos ht ht hx.1 hx.2

theorem rhombic_weierstrassP_tendsto_top {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x : ℝ => ((rhombicPeriodPair t ht).weierstrassP x).re) (𝓝[>] 0) atTop := by
  let L := rhombicPeriodPair t ht
  have hcomplex : ContinuousAt (fun x : ℝ => L.weierstrassPExcept 0 x) 0 :=
    (L.analyticAt_weierstrassPExcept 0).continuousAt.comp (f := Complex.ofReal)
      Complex.continuous_ofReal.continuousAt
  have hc : ContinuousAt (fun x : ℝ => (L.weierstrassPExcept 0 x).re) 0 :=
    Complex.continuous_re.continuousAt.comp hcomplex
  have hpow : Tendsto (fun x : ℝ => (x⁻¹)^2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp tendsto_inv_nhdsGT_zero
  have hs := hc.tendsto.mono_left nhdsWithin_le_nhds |>.add_atTop hpow
  apply hs.congr'
  filter_upwards [] with x
  have hp : L.weierstrassPExcept 0 x+1/(x:ℂ)^2 = L.weierstrassP x := by
    simpa using L.weierstrassPExcept_add (0:L.lattice) (x:ℂ)
  have he : (1:ℂ)/(x:ℂ)^2 = (((x⁻¹)^2:ℝ):ℂ) := by push_cast; ring
  rw [he] at hp
  have hr := congrArg Complex.re hp
  simpa only [Complex.add_re,Complex.ofReal_re] using hr

theorem rhombic_weierstrassP_level_iff {t : ℝ} (ht : 0 < t) (u : ℝ) :
    (∃! a : ℝ, a ∈ Ioo (0:ℝ) 1 ∧ ((rhombicPeriodPair t ht).weierstrassP a).re = u) ↔
      ((rhombicPeriodPair t ht).weierstrassP 1).re < u := by
  let P : ℝ → ℝ := fun x => ((rhombicPeriodPair t ht).weierstrassP x).re
  have hmono := rhombic_weierstrassP_strictAnti_to_one ht
  constructor
  · rintro ⟨a,ha,_⟩
    have h := hmono ⟨ha.1.1,ha.1.2.le⟩ (by norm_num : (1:ℝ) ∈ Ioc 0 1) ha.1.2
    simpa only [ha.2,Complex.ofReal_one] using h
  · intro hu
    have hgt : ∀ᶠ y in 𝓝[>] (0:ℝ), u < P y :=
      (rhombic_weierstrassP_tendsto_top ht).eventually (eventually_gt_atTop u)
    have hlt : ∀ᶠ y in 𝓝[>] (0:ℝ), y < 1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    have hpos : ∀ᶠ y in 𝓝[>] (0:ℝ), 0 < y := self_mem_nhdsWithin
    obtain ⟨y,⟨hy0,hy1⟩,hyp⟩ := ((hpos.and hlt).and hgt).exists
    have hc : ContinuousOn P (Icc y 1) := by
      intro x hx
      exact (rhombic_weierstrassP_real_hasDerivAt_of_pos ht ht (hy0.trans_le hx.1)
        (lt_of_le_of_lt hx.2 (by norm_num))).continuousAt.continuousWithinAt
    obtain ⟨a,ha,hap⟩ := intermediate_value_Icc' hy1.le hc ⟨hu.le,hyp.le⟩
    have ha1 : a < 1 := by
      apply lt_of_le_of_ne ha.2
      intro he
      have hp1 : P 1 = u := by simpa only [he] using hap
      exact hu.ne hp1
    refine ⟨a,⟨⟨hy0.trans_le ha.1,ha1⟩,hap⟩,?_⟩
    intro b hb
    apply hmono.injOn ⟨hb.1.1,hb.1.2.le⟩ ⟨hy0.trans_le ha.1,ha.2⟩
    exact hb.2.trans hap.symm

theorem thetaG_zero_iff_wp_level {t : ℝ} (ht : 0 < t) {a : ℝ}
    (ha : a ∈ Ioo (0:ℝ) 1) :
    thetaG t a = 0 ↔ ((rhombicPeriodPair t ht).weierstrassP a).re =
      Real.pi/t-(thetaEtaExpression t).re := by
  have h := thetaG_eq_weierstrassP_of_pos ht ht a
    (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2]))
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re] at hr
  constructor
  · intro hz
    rw [hz,Complex.zero_re] at hr
    linarith
  · intro hz
    apply Complex.ext
    · simp only [Complex.zero_re]
      linarith
    · exact thetaG_real t a

theorem existsUnique_thetaG_zero_iff {t : ℝ} (ht : 0 < t) :
    (∃! a : ℝ, a ∈ Ioo (0:ℝ) 1 ∧ thetaG t a = 0) ↔ (thetaG t 1).re < 0 := by
  have he (a : ℝ) : (a ∈ Ioo (0:ℝ) 1 ∧ thetaG t a = 0) ↔
      (a ∈ Ioo (0:ℝ) 1 ∧ ((rhombicPeriodPair t ht).weierstrassP a).re =
        Real.pi/t-(thetaEtaExpression t).re) := by
    by_cases ha : a ∈ Ioo (0:ℝ) 1
    · simp only [ha,true_and,thetaG_zero_iff_wp_level ht ha]
    · simp only [ha,false_and]
  rw [existsUnique_congr he,rhombic_weierstrassP_level_iff ht]
  have h := thetaG_eq_weierstrassP_of_pos ht ht 1
    (real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num))
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.ofReal_one] at hr
  constructor <;> intro hh <;> linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_weierstrassP_level_iff
