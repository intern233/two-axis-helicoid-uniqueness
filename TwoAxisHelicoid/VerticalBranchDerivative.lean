import TwoAxisHelicoid.VerticalBranchContinuity
import TwoAxisHelicoid.ImplicitScalarDerivative

namespace TwoAxisHelicoid
open Set Filter Complex
open scoped Topology
attribute [local irreducible] thetaJet thetaQuotient thetaG verticalA

theorem verticalA_hasDerivAt {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    HasDerivAt verticalA (-(thetaGt t (verticalA t)).re/(thetaGa t (verticalA t)).re) t := by
  have ha := (verticalA_spec ht).1
  have hrect : (Ioi (0:ℝ) ×ˢ Ioo (0:ℝ) 1) ∈ 𝓝 (t,verticalA t) :=
    prod_mem_nhds (Ioi_mem_nhds ht.1) (Ioo_mem_nhds ha.1 ha.2)
  apply implicit_scalar_hasDerivAt
    (F := fun s b => (thetaG s b).re)
    (Ft := fun s b => (thetaGt s b).re) (Fa := fun s b => (thetaGa s b).re)
  · filter_upwards [hrect] with p hp
    exact thetaG_real_t_hasDerivAt hp.1 hp.2.1 (by linarith [hp.2.2])
  · filter_upwards [hrect] with p hp
    exact thetaG_real_a_hasDerivAt hp.1 hp.2.1 (by linarith [hp.2.2])
  · exact Complex.continuous_re.continuousAt.comp (thetaGt_joint_continuousAt ht.1 ha.1 (by linarith [ha.2]))
  · exact Complex.continuous_re.continuousAt.comp (thetaGa_joint_continuousAt ht.1 ha.1 (by linarith [ha.2]))
  · exact (thetaGa_re_neg_unit ht.1 ha.1 ha.2).ne
  · exact verticalA_continuousAt ht
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [(verticalA_spec hs).2]
    rfl

theorem verticalA_deriv_continuousAt {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    ContinuousAt (deriv verticalA) t := by
  have ha := (verticalA_spec ht).1
  have hp : ContinuousAt (fun s : ℝ => (s,verticalA s)) t :=
    continuousAt_id.prodMk (verticalA_continuousAt ht)
  have hct := (thetaGt_joint_continuousAt ht.1 ha.1 (by linarith [ha.2])).comp
    (f := fun s : ℝ => (s,verticalA s)) hp
  have hca := (thetaGa_joint_continuousAt ht.1 ha.1 (by linarith [ha.2])).comp
    (f := fun s : ℝ => (s,verticalA s)) hp
  have hc : ContinuousAt (fun s => -(thetaGt s (verticalA s)).re/(thetaGa s (verticalA s)).re) t :=
    (Complex.continuous_re.continuousAt.comp hct).neg.div
      (Complex.continuous_re.continuousAt.comp hca) (thetaGa_re_neg_unit ht.1 ha.1 ha.2).ne
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact (verticalA_hasDerivAt hs).deriv

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.verticalA_hasDerivAt
#print axioms TwoAxisHelicoid.verticalA_deriv_continuousAt
