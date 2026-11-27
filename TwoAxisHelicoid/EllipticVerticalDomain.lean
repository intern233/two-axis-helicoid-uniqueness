import TwoAxisHelicoid.EllipticFGlobalDerivative
import TwoAxisHelicoid.EllipticFEndpoint
import TwoAxisHelicoid.WeierstrassVerticalDomain

namespace TwoAxisHelicoid
open Set Complex

theorem existsUnique_ellipticFReal_root : ∃! t : ℝ, 0 < t ∧ ellipticFReal t = 0 := by
  have hc : ContinuousOn ellipticFReal (Icc (70945978/100000000) (70945980/100000000)) := by
    intro t ht
    exact (ellipticFReal_differentiableAt (by linarith [ht.1])).continuousAt.continuousWithinAt
  obtain ⟨t,ht,hz⟩ := intermediate_value_Icc
    (by norm_num : (70945978/100000000:ℝ) ≤ 70945980/100000000) hc
    ⟨ellipticFReal_left_endpoint_neg.le,ellipticFReal_right_endpoint_pos.le⟩
  have ht0 : 0 < t := by linarith [ht.1]
  refine ⟨t,⟨ht0,hz⟩,?_⟩
  intro s hs
  exact ellipticFReal_strictMono_of_pos.injOn hs.1 ht0 (hs.2.trans hz.symm)

theorem ellipticFReal_root_location {t : ℝ} (ht : 0 < t) (hz : ellipticFReal t = 0) :
    (70945978/100000000:ℝ) < t ∧ t < 70945980/100000000 := by
  constructor
  · by_contra hn
    have hm := ellipticFReal_strictMono_of_pos.monotoneOn ht
      (by norm_num : (0:ℝ) < 70945978/100000000) (le_of_not_gt hn)
    linarith [ellipticFReal_left_endpoint_neg]
  · by_contra hn
    have hm := ellipticFReal_strictMono_of_pos.monotoneOn
      (by norm_num : (0:ℝ) < 70945980/100000000) ht (le_of_not_gt hn)
    linarith [ellipticFReal_right_endpoint_pos]

noncomputable def ellipticCriticalT : ℝ := existsUnique_ellipticFReal_root.exists.choose

theorem ellipticCriticalT_pos : 0 < ellipticCriticalT :=
  existsUnique_ellipticFReal_root.exists.choose_spec.1

theorem ellipticCriticalT_zero : ellipticFReal ellipticCriticalT = 0 :=
  existsUnique_ellipticFReal_root.exists.choose_spec.2

theorem ellipticCriticalT_location :
    (70945978/100000000:ℝ) < ellipticCriticalT ∧ ellipticCriticalT < 70945980/100000000 :=
  ellipticFReal_root_location ellipticCriticalT_pos ellipticCriticalT_zero

theorem ellipticFReal_neg_iff {t : ℝ} (ht : 0 < t) :
    ellipticFReal t < 0 ↔ t < ellipticCriticalT := by
  rw [← ellipticCriticalT_zero]
  exact ellipticFReal_strictMono_of_pos.lt_iff_lt ht ellipticCriticalT_pos

theorem ellipticFReal_pos_iff {t : ℝ} (ht : 0 < t) :
    0 < ellipticFReal t ↔ ellipticCriticalT < t := by
  rw [← ellipticCriticalT_zero]
  exact ellipticFReal_strictMono_of_pos.lt_iff_lt ellipticCriticalT_pos ht

theorem thetaG_one_eq_ellipticFReal (t : ℝ) :
    (thetaG t 1).re = ellipticFReal t-Real.pi/t := by
  simp only [thetaG,ellipticFReal,thetaLogSecond,Complex.ofReal_one,Complex.sub_re,Complex.ofReal_re]

theorem thetaG_one_reciprocal_real {t : ℝ} (ht : 0 < t) :
    (thetaG t 1).re = -ellipticFReal (1/t)/t^2 := by
  rw [thetaG_one_eq_ellipticFReal,ellipticFReal_reciprocal ht]
  ring

noncomputable def ellipticVerticalUpper : ℝ := 1/ellipticCriticalT

theorem ellipticVerticalUpper_pos : 0 < ellipticVerticalUpper :=
  one_div_pos.mpr ellipticCriticalT_pos

/-- The actual vertical period equation has exactly one solution in the
geometric interval precisely on this full height interval. -/
theorem existsUnique_thetaG_zero_full_domain {t : ℝ} (ht : 0 < t) :
    (∃! a : ℝ, a ∈ Ioo (0:ℝ) 1 ∧ thetaG t a = 0) ↔ t < ellipticVerticalUpper := by
  rw [existsUnique_thetaG_zero_iff ht,thetaG_one_reciprocal_real ht,
    div_lt_iff₀ (sq_pos_of_pos ht),zero_mul,neg_lt_zero,
    ellipticFReal_pos_iff (one_div_pos.mpr ht)]
  unfold ellipticVerticalUpper
  rw [lt_div_iff₀ ht,lt_div_iff₀ ellipticCriticalT_pos]
  rw [mul_comm]

theorem ellipticVerticalUpper_location :
    100000000/70945980 < ellipticVerticalUpper ∧ ellipticVerticalUpper < 100000000/70945978 := by
  unfold ellipticVerticalUpper
  constructor
  · rw [lt_div_iff₀ ellipticCriticalT_pos]
    nlinarith [ellipticCriticalT_location.2]
  · rw [div_lt_iff₀ ellipticCriticalT_pos]
    nlinarith [ellipticCriticalT_location.1]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.existsUnique_thetaG_zero_full_domain
