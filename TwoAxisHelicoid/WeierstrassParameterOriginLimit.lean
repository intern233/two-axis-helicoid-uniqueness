import TwoAxisHelicoid.WeierstrassParameterHeat
import Mathlib.Analysis.Complex.RemovableSingularity

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology
attribute [local irreducible] thetaScaledJet thetaEtaExpression

private noncomputable def originThetaTimeJet (t : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  thetaScaledJet t (j+2) z/(2*(Real.pi:ℂ))+(Real.pi/8:ℂ)*thetaScaledJet t j z

private theorem originThetaTimeJet_time {t : ℝ} (ht : 0 < t) (j : ℕ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => thetaScaledJet s j z) (originThetaTimeJet t j z) t :=
  thetaScaledJet_parameter_hasDerivAt ht j z

private theorem originThetaTimeJet_space {t : ℝ} (ht : 0 < t) (j : ℕ) (z : ℂ) :
    HasDerivAt (originThetaTimeJet t j) (originThetaTimeJet t (j+1) z) z :=
  ((thetaScaledJet_hasDerivAt ht (j+2) z).div_const (2*(Real.pi:ℂ))).add
    ((thetaScaledJet_hasDerivAt ht j z).const_mul (Real.pi/8:ℂ))

private theorem originThetaTimeJet_iter {t : ℝ} (ht : 0 < t) (j n : ℕ) :
    iteratedDeriv n (originThetaTimeJet t j) = originThetaTimeJet t (j+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    simpa only [Nat.add_assoc] using (originThetaTimeJet_space ht (j+n) z).deriv

/-- Direct differentiation of the defining quotient at zero. -/
private theorem origin_eta_ratio_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt thetaEtaExpression
      (-((originThetaTimeJet t 3 0*thetaScaledJet t 1 0-
          thetaScaledJet t 3 0*originThetaTimeJet t 1 0)/
        (3*(thetaScaledJet t 1 0)^2))) t := by
  have hd := ((originThetaTimeJet_time ht 3 0).div (originThetaTimeJet_time ht 1 0)
    (thetaScaledJet_one_ne_zero_of_pos ht)).const_mul (-(1/3:ℂ))
  have eq : thetaEtaExpression = fun s : ℝ => -(1/3:ℂ)*(thetaScaledJet s 3 0/thetaScaledJet s 1 0) := by
    funext s
    unfold thetaEtaExpression
    ring
  rw [eq]
  convert hd using 1
  field_simp [thetaScaledJet_one_ne_zero_of_pos ht]

private theorem origin_theta_log_time_regular {t : ℝ} (ht : 0 < t) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      (fun z => thetaScaledJet t 0 z * R z) =ᶠ[𝓝 0] originThetaTimeJet t 0 := by
  let F := thetaScaledJet t 0
  let T := originThetaTimeJet t 0
  let D := dslope F 0
  let E := dslope T 0
  have fd : Differentiable ℂ F := fun z => (thetaScaledJet_hasDerivAt ht 0 z).differentiableAt
  have td : Differentiable ℂ T := fun z => (originThetaTimeJet_space ht 0 z).differentiableAt
  have dd : Differentiable ℂ D := differentiableOn_univ.mp <|
    (Complex.differentiableOn_dslope (s := univ) (c := 0) (by simp)).mpr fd.differentiableOn
  have ed : Differentiable ℂ E := differentiableOn_univ.mp <|
    (Complex.differentiableOn_dslope (s := univ) (c := 0) (by simp)).mpr td.differentiableOn
  have d0 : D 0 ≠ 0 := by
    rw [show D 0 = deriv F 0 from dslope_same F 0, (thetaScaledJet_hasDerivAt ht 0 0).deriv]
    exact thetaScaledJet_one_ne_zero_of_pos ht
  have t0 : T 0 = 0 := by
    simp [T,originThetaTimeJet,thetaScaledJet_zero_at_zero,thetaScaledJet_two_at_zero]
  have fx (z : ℂ) : z * D z = F z := by
    simpa only [sub_zero, smul_eq_mul, F, thetaScaledJet_zero_at_zero] using sub_smul_dslope F 0 z
  have tx (z : ℂ) : z * E z = T z := by
    simpa only [sub_zero, smul_eq_mul, t0] using sub_smul_dslope T 0 z
  refine ⟨fun z => E z / D z, (ed.analyticAt 0).div (dd.analyticAt 0) d0, ?_⟩
  filter_upwards [(dd 0).continuousAt.eventually_ne d0] with z dz
  change F z * (E z / D z) = T z
  rw [← fx z, ← tx z]
  field_simp [dz]

private theorem origin_time_product_jet {t : ℝ} (ht : 0 < t) {z : ℂ} {R : ℂ → ℂ}
    (hr : AnalyticAt ℂ R z)
    (same : (fun w => thetaScaledJet t 0 w * R w) =ᶠ[𝓝 z] originThetaTimeJet t 0) (n : ℕ) :
    originThetaTimeJet t n z = ∑ i ∈ Finset.range (n+1),
      (n.choose i:ℂ) * thetaScaledJet t i z * iteratedDeriv (n-i) R z := by
  have h := (same.iteratedDeriv_eq n).symm
  rw [iteratedDeriv_fun_mul (thetaScaledJet_analyticAt ht 0 z).contDiffAt hr.contDiffAt,
    originThetaTimeJet_iter ht] at h
  simpa only [thetaScaledJet_iteratedDeriv ht, Nat.zero_add] using h

private theorem origin_second_time_log_zero {t : ℝ} (ht : 0 < t) {R : ℂ → ℂ}
    (hr : AnalyticAt ℂ R 0)
    (same : (fun w => thetaScaledJet t 0 w * R w) =ᶠ[𝓝 0] originThetaTimeJet t 0) :
    iteratedDeriv 2 R 0 = -deriv thetaEtaExpression t := by
  have h1 : originThetaTimeJet t 1 0 = thetaScaledJet t 1 0 * R 0 := by
    simpa [Finset.sum_range_succ, thetaScaledJet_zero_at_zero] using origin_time_product_jet ht hr same 1
  have h3 : originThetaTimeJet t 3 0 = thetaScaledJet t 3 0 * R 0 +
      3 * thetaScaledJet t 1 0 * iteratedDeriv 2 R 0 := by
    have h := origin_time_product_jet ht hr same 3
    norm_num [Finset.sum_range_succ, Nat.choose, thetaScaledJet_zero_at_zero,
      thetaScaledJet_two_at_zero] at h
    linear_combination h
  rw [(origin_eta_ratio_deriv ht).deriv,neg_neg]
  apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero _ (thetaScaledJet_one_ne_zero_of_pos ht)))).mpr
  linear_combination -(thetaScaledJet t 1 0)*h3 + (thetaScaledJet t 3 0)*h1

private theorem actual_parameter_eq_time_log {t : ℝ} (ht : 0 < t) {z : ℂ} {R : ℂ → ℂ}
    (hn : thetaScaledJet t 0 z ≠ 0) (hr : AnalyticAt ℂ R z)
    (same : (fun w => thetaScaledJet t 0 w * R w) =ᶠ[𝓝 z] originThetaTimeJet t 0) :
    deriv (fun s : ℝ => actualWeierstrassPFamily s z) t =
      -iteratedDeriv 2 R z - deriv thetaEtaExpression t := by
  have h0 := same.self_of_nhds.symm
  have h1 : originThetaTimeJet t 1 z =
      thetaScaledJet t 1 z * R z + thetaScaledJet t 0 z * deriv R z := by
    have h := origin_time_product_jet ht hr same 1
    norm_num [Finset.sum_range_succ] at h
    linear_combination h
  have h2 : originThetaTimeJet t 2 z = thetaScaledJet t 2 z * R z +
      2 * thetaScaledJet t 1 z * deriv R z + thetaScaledJet t 0 z * iteratedDeriv 2 R z := by
    have h := origin_time_product_jet ht hr same 2
    norm_num [Finset.sum_range_succ, Nat.choose] at h
    linear_combination h
  have localEq : (fun s : ℝ => actualWeierstrassPFamily s z) =ᶠ[𝓝 t]
      (fun s : ℝ => (thetaScaledJet s 1 z/thetaScaledJet s 0 z)^2 -
        thetaScaledJet s 2 z/thetaScaledJet s 0 z - thetaEtaExpression s) := by
    filter_upwards [eventually_gt_nhds ht,
      (originThetaTimeJet_time ht 0 z).continuousAt.eventually_ne hn] with s hs hn'
    have hz := mt (thetaScaledJet_zero_iff_lattice_of_pos hs hs z).mpr hn'
    have he := thetaLogSecond_eq_weierstrassP_add_eta_of_pos hs hs hz
    rw [thetaLogSecond_scaled] at he
    simp only [actualWeierstrassPFamily, dite_eq_left hs]
    linear_combination -he
  have hd := ((((originThetaTimeJet_time ht 1 z).div (originThetaTimeJet_time ht 0 z) hn).pow 2).sub
    ((originThetaTimeJet_time ht 2 z).div (originThetaTimeJet_time ht 0 z) hn)).sub
    (origin_eta_ratio_deriv ht).differentiableAt.hasDerivAt
  rw [localEq.deriv_eq]
  have hd' : HasDerivAt (fun s : ℝ => (thetaScaledJet s 1 z/thetaScaledJet s 0 z)^2 -
      thetaScaledJet s 2 z/thetaScaledJet s 0 z - thetaEtaExpression s) _ t := hd
  rw [hd'.deriv, h0, h1, h2]
  simp only [Pi.div_apply, Nat.reduceSub, pow_one]
  field_simp [hn]
  ring

/-- Appendix A.1, line 1929. The derivative of the actual lattice function
with respect to the real height has limit zero at its pole. -/
theorem actualWeierstrassPFamily_parameter_deriv_tendsto_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun z : ℂ => deriv (fun s : ℝ => actualWeierstrassPFamily s z) t)
      (𝓝[≠] (0:ℂ)) (𝓝 0) := by
  obtain ⟨R, hr, same⟩ := origin_theta_log_time_regular ht
  have zero := origin_second_time_log_zero ht hr same
  have hr2 : ContinuousAt (iteratedDeriv 2 R) 0 := by
    rw [show 2 = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]
    exact hr.deriv.deriv.continuousAt
  have cont : ContinuousAt (fun z => -iteratedDeriv 2 R z - deriv thetaEtaExpression t) 0 :=
    hr2.neg.sub continuousAt_const
  have limit := cont.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  change Tendsto _ _ (𝓝 (-iteratedDeriv 2 R 0 - deriv thetaEtaExpression t)) at limit
  rw [zero,neg_neg,sub_self] at limit
  apply limit.congr'
  filter_upwards [hr.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    same.eventually_nhds.filter_mono nhdsWithin_le_nhds,
    mem_nhdsWithin_of_mem_nhds ((rhombicPeriodPair t ht).compl_lattice_sdiff_singleton_mem_nhds 0),
    self_mem_nhdsWithin] with z hR hsame hi nz
  have hz : z ∉ (rhombicPeriodPair t ht).lattice := fun hz => hi ⟨hz,nz⟩
  exact (actual_parameter_eq_time_log ht (mt (thetaScaledJet_zero_iff_lattice_of_pos ht ht z).mp hz)
    hR hsame).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualWeierstrassPFamily_parameter_deriv_tendsto_zero
