import TwoAxisHelicoid.ImplicitScalarDerivative
import TwoAxisHelicoid.RootGDerivativeContinuity

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
attribute [local irreducible] thetaG thetaJet thetaQuotient

noncomputable def rootVerticalAReal (t : ℝ) : ℝ :=
  if h : t ∈ Icc (rootTLower : ℝ) rootTUpper then (rootVerticalA ⟨t,h⟩ : ℝ) else 0

theorem rootVerticalAReal_eq {t : ℝ} (ht : t ∈ Icc (rootTLower : ℝ) rootTUpper) :
    rootVerticalAReal t = (rootVerticalA ⟨t,ht⟩ : ℝ) := by
  simp only [rootVerticalAReal, dite_eq_left ht]

theorem rootVerticalAReal_spec {t : ℝ} (ht : t ∈ Icc (rootTLower : ℝ) rootTUpper) :
    rootVerticalAReal t ∈ Ioo (rootALower : ℝ) rootAUpper ∧ thetaG t (rootVerticalAReal t) = 0 := by
  rw [rootVerticalAReal_eq ht]
  exact rootVerticalA_spec ⟨t,ht⟩

theorem rootVerticalAReal_continuousOn :
    ContinuousOn rootVerticalAReal (Icc (rootTLower : ℝ) rootTUpper) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert continuous_subtype_val.comp rootVerticalA_continuous using 1
  funext t
  exact rootVerticalAReal_eq t.property

theorem rootRectangle_mem_nhds {t a : ℝ}
    (ht : t ∈ Ioo (rootTLower : ℝ) rootTUpper) (ha : a ∈ Ioo (rootALower : ℝ) rootAUpper) :
    rootRectangle ∈ 𝓝 (t,a) :=
  prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) (Icc_mem_nhds ha.1 ha.2)

theorem rootVerticalAReal_hasDerivAt {t : ℝ} (ht : t ∈ Ioo (rootTLower : ℝ) rootTUpper) :
    HasDerivAt rootVerticalAReal
      (-(thetaGt t (rootVerticalAReal t)).re/(thetaGa t (rootVerticalAReal t)).re) t := by
  have htc : t ∈ Icc (rootTLower : ℝ) rootTUpper := ⟨ht.1.le,ht.2.le⟩
  have ha := (rootVerticalAReal_spec htc).1
  have hrect := rootRectangle_mem_nhds ht ha
  apply implicit_scalar_hasDerivAt
    (F := fun s b => (thetaG s b).re)
    (Ft := fun s b => (thetaGt s b).re) (Fa := fun s b => (thetaGa s b).re)
  · filter_upwards [hrect] with p hp
    exact root_vertical_t_hasDerivAt hp.1.1 hp.1.2 hp.2.1 hp.2.2
  · filter_upwards [hrect] with p hp
    exact root_vertical_real_hasDerivAt hp.1.1 hp.1.2 hp.2.1 hp.2.2
  · exact (Complex.continuous_re.comp_continuousOn thetaGt_rootRectangle_continuousOn).continuousAt hrect
  · exact (Complex.continuous_re.comp_continuousOn thetaGa_rootRectangle_continuousOn).continuousAt hrect
  · exact ne_of_lt (root_vertical_derivative_negative ht.1.le ht.2.le ha.1.le ha.2.le)
  · exact rootVerticalAReal_continuousOn.continuousAt (Icc_mem_nhds ht.1 ht.2)
  · filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    rw [(rootVerticalAReal_spec hs).2]
    rfl

theorem rootVerticalAReal_deriv_pos {t : ℝ} (ht : t ∈ Ioo (rootTLower : ℝ) rootTUpper) :
    0 < deriv rootVerticalAReal t := by
  rw [(rootVerticalAReal_hasDerivAt ht).deriv]
  have ha := (rootVerticalAReal_spec ⟨ht.1.le,ht.2.le⟩).1
  have he := rootDerivativeParameters.sound rootDerivativeParameters_valid ht.1.le ht.2.le ha.1.le ha.2.le
  exact div_pos_of_neg_of_neg (neg_neg_of_pos (lt_of_lt_of_le (by norm_num) he.gt_lower))
    (root_vertical_derivative_negative ht.1.le ht.2.le ha.1.le ha.2.le)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rootVerticalAReal_hasDerivAt
