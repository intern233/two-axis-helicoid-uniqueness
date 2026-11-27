import TwoAxisHelicoid.RootImplicitDerivative
import TwoAxisHelicoid.RootPeriodDerivativeContinuity
import TwoAxisHelicoid.ScalarBivariateDerivative
import TwoAxisHelicoid.RootDerivativeIntegral

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
attribute [local irreducible] thetaHorizontalPeriod

noncomputable def rootPeriodAlong (t : ℝ) : ℝ := thetaHorizontalPeriod t (rootVerticalAReal t)

theorem rootPeriodAlong_hasDerivAt {t : ℝ} (ht : t ∈ Ioo (rootTLower : ℝ) rootTUpper) :
    HasDerivAt rootPeriodAlong (rootPeriodDt t (rootVerticalAReal t)+
      deriv rootVerticalAReal t*rootPeriodDa t (rootVerticalAReal t)) t := by
  have ha := (rootVerticalAReal_spec ⟨ht.1.le,ht.2.le⟩).1
  have hrect := rootRectangle_mem_nhds ht ha
  have hnh : Ioo (rootTLower : ℝ) rootTUpper ×ˢ Ioo (rootALower : ℝ) rootAUpper ∈
      𝓝 (t,rootVerticalAReal t) := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨ht,ha⟩
  have hdt : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,rootVerticalAReal t),
      HasDerivAt (fun s => thetaHorizontalPeriod s p.2) (rootPeriodDt p.1 p.2) p.1 := by
    filter_upwards [hnh] with p hp
    exact root_period_t_hasDerivAt hp.1 hp.2.1.le hp.2.2.le
  have hda : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,rootVerticalAReal t),
      HasDerivAt (thetaHorizontalPeriod p.1) (rootPeriodDa p.1 p.2) p.2 := by
    filter_upwards [hnh] with p hp
    exact root_period_a_hasDerivAt hp.1.1.le hp.1.2.le hp.2
  have hd := scalar_bivariate_curve_hasDerivAt hdt hda
    (root_period_partials_continuousOn.2.continuousAt hrect)
    (root_period_partials_continuousOn.1.continuousAt hrect)
    (hasDerivAt_id t) (rootVerticalAReal_hasDerivAt ht).differentiableAt.hasDerivAt
  unfold rootPeriodAlong
  simpa only [id_eq,one_mul] using hd

theorem rootPeriodAlong_deriv_neg {t : ℝ} (ht : t ∈ Ioo (rootTLower : ℝ) rootTUpper) :
    deriv rootPeriodAlong t < 0 := by
  rw [(rootPeriodAlong_hasDerivAt ht).deriv]
  have ha := (rootVerticalAReal_spec ⟨ht.1.le,ht.2.le⟩).1
  have hn := root_derivative_integrals_negative ht.1.le ht.2.le ha.1.le ha.2.le
  exact add_neg hn.2 (mul_neg_of_pos_of_neg (rootVerticalAReal_deriv_pos ht) hn.1)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rootPeriodAlong_deriv_neg
