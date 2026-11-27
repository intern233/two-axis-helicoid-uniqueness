import TwoAxisHelicoid.EllipticFHeat
import TwoAxisHelicoid.WeierstrassAllMonotone
import Mathlib.Analysis.Analytic.Uniqueness

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

theorem weierstrass_second_order_of_noncritical (L : PeriodPair) {z : ℂ}
    (hz : z ∉ L.lattice) (hdz : L.derivWeierstrassP z ≠ 0) :
    deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂/2 := by
  have hp := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  rw [L.deriv_weierstrassP] at hp
  have hd := (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  have hleft := hd.pow 2
  have hright := (((hp.pow 3).const_mul 4).sub (hp.const_mul L.g₂)).sub_const L.g₃
  have he : (fun w => L.derivWeierstrassP w ^ 2) =ᶠ[𝓝 z]
      fun w => 4*L.weierstrassP w^3-L.g₂*L.weierstrassP w-L.g₃ := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact L.derivWeierstrassP_sq w hw
  have h := hleft.unique (hright.congr_of_eventuallyEq he)
  simp only [Nat.cast_ofNat,show (2-1:ℕ)=1 by decide,pow_one,show (3-1:ℕ)=2 by decide] at h
  apply mul_left_cancel₀ hdz
  linear_combination (1/2:ℂ)*h

theorem rhombic_weierstrass_second_order {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    deriv (rhombicPeriodPair t ht).derivWeierstrassP z =
      6*(rhombicPeriodPair t ht).weierstrassP z^2-(rhombicPeriodPair t ht).g₂/2 := by
  let L := rhombicPeriodPair t ht
  have hhalf : (1/2:ℂ) ∉ L.lattice := by
    simpa using real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (1/2:ℝ)<2)
  have hn : L.derivWeierstrassP (1/2:ℂ) ≠ 0 := by
    have h := rhombic_weierstrassP_derivative_real_neg_of_pos ht ht
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
    intro he
    norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at h
    rw [he] at h
    exact (lt_irrefl 0) h
  have hconn : IsPreconnected (L.lattice:Set ℂ)ᶜ := by
    refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact countable_of_Lindelof_of_discrete (X := L.lattice)
  have ha : AnalyticOnNhd ℂ (deriv L.derivWeierstrassP) (L.lattice:Set ℂ)ᶜ :=
    L.analyticOnNhd_derivWeierstrassP.deriv
  have hb : AnalyticOnNhd ℂ (fun w => 6*L.weierstrassP w^2-L.g₂/2) (L.lattice:Set ℂ)ᶜ := by
    intro w hw
    exact (analyticAt_const.mul ((L.analyticOnNhd_weierstrassP w hw).pow 2)).sub analyticAt_const
  have he : deriv L.derivWeierstrassP =ᶠ[𝓝 (1/2:ℂ)]
      fun w => 6*L.weierstrassP w^2-L.g₂/2 := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hhalf,
      (L.analyticOnNhd_derivWeierstrassP _ hhalf).continuousAt.eventually_ne hn] with w hw hdw
    exact weierstrass_second_order_of_noncritical L hw hdw
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb hconn hhalf he hz

theorem ellipticC_weierstrass_formula {t : ℝ} (ht : 0 < t) :
    ellipticC t ht = (6*(rhombicPeriodPair t ht).weierstrassP 1^2-
      (rhombicPeriodPair t ht).g₂/2).re := by
  unfold ellipticC
  have hz : (1:ℂ) ∉ (rhombicPeriodPair t ht).lattice :=
    real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)
  rw [rhombic_weierstrass_second_order ht hz]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_weierstrass_second_order
