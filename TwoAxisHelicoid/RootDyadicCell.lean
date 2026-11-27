import TwoAxisHelicoid.RootDyadicNode
import TwoAxisHelicoid.HorizontalCertificate

namespace TwoAxisHelicoid
open ComplexBall Metric
attribute [local irreducible] thetaA thetaJet

structure RootDyadicCell where
  center : DyadicBall
  disk : DyadicBall
  diskFunction : DyadicThetaATrace
  nodes : Fin 32 → RootDyadicNode
  output : DyadicBall

namespace RootDyadicCell

def diskBound (w : RootDyadicCell) : ℚ :=
  (w.diskFunction.output.toBall rootDyadicConfig.prec).center.absUpper+
    (w.diskFunction.output.toBall rootDyadicConfig.prec).radius

def Valid (p : RootDyadicParameters) (x h R : ℚ) (w : RootDyadicCell) : Prop :=
  0 ≤ h ∧ h < R ∧
  (w.center.toBall rootDyadicConfig.prec).coarsens
    (horizontalCenterBall rootDyadicConfig (p.height.toBall rootDyadicConfig.prec) x) ∧
  (w.disk.toBall rootDyadicConfig.prec).coarsens ((w.center.toBall rootDyadicConfig.prec).inflate R) ∧
  w.diskFunction.Valid rootDyadicConfig 8 65536 p.q.output p.abscissa p.coefficient.output w.disk ∧
  (∀ i : Fin 32, (w.nodes i).Valid p w.center h (rationalQuadrature32.node i) (rationalQuadrature32.weight i)) ∧
  (w.output.toBall rootDyadicConfig.prec).coarsens
    ((sumBalls (fun i => ((w.nodes i).output.toBall rootDyadicConfig.prec))).inflate
      (quadratureErrorBound rationalQuadrature32 32 h R w.diskBound))

instance (p : RootDyadicParameters) (x h R : ℚ) (w : RootDyadicCell) :
    Decidable (w.Valid p x h R) := by unfold Valid; infer_instance

theorem sound {tlo thi alo ahi : ℚ} {t a : ℝ} (p : RootDyadicParameters)
    (hp : p.Valid tlo thi alo ahi)
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ))
    (x h R : ℚ) (w : RootDyadicCell) (hw : w.Valid p x h R) :
    (w.output.toBall rootDyadicConfig.prec).Contains
      (normalizedIntegral (thetaA t a) ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (h : ℝ)) ∧
    DiffContOnCl ℂ (thetaA t a)
      (ball ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (R : ℝ)) := by
  rcases hw with ⟨hh0, hhR, hcenter, hdisk, hdf, hnodes, hout⟩
  rcases p.sound hp htl htu hal hau with ⟨ht, hq, ha, hc⟩
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hbt := coarsen_contains (realInterval_contains htl htu) hp.2.1
  have hcenter' := coarsen_contains (horizontalCenterBall_contains hbt rootDyadicConfig x) hcenter
  let c : ℂ := (x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)
  have hh : (0 : ℝ) ≤ h := by exact_mod_cast hh0
  have hhR' : (h : ℝ) < R := by exact_mod_cast hhR
  have hbound : ∀ z ∈ closedBall c (R : ℝ),
      z ∈ thetaRegular t ∧ ‖thetaA t a z‖ ≤ (w.diskBound : ℝ) := by
    intro z hz
    have hdz := coarsen_contains (inflate_contains hcenter' (mem_closedBall_iff_norm.mp hz)) hdisk
    have hf := w.diskFunction.sound rootDyadicConfig 8 65536 hq ha hc hdz
      (root_dyadic_tail_zero ht) (root_dyadic_tail_one ht) hdf
    exact ⟨hf.2, norm_le hf.1⟩
  have han : DiffContOnCl ℂ (thetaA t a) (ball c (R : ℝ)) :=
    (thetaA_differentiableOn htpos a).diffContOnCl_ball (fun z hz => (hbound z hz).1)
  have hM0 : (0 : ℝ) ≤ w.diskBound := (norm_nonneg _).trans
    (hbound c (mem_closedBall_self (hh.trans hhR'.le))).2
  have herr := QuadratureRule.analytic_error_bound rationalQuadrature32_exact
    rationalQuadrature32_nodes hh hhR' hM0 han
    (fun z hz => (hbound z (sphere_subset_closedBall hz)).2)
  have herr' : ‖normalizedIntegral (thetaA t a) c (h : ℝ)-
      rationalQuadrature32.apply (thetaA t a) c (h : ℝ)‖ ≤
      (quadratureErrorBound rationalQuadrature32 32 h R w.diskBound : ℝ) := by
    simpa only [quadratureErrorBound, Rat.cast_mul, Rat.cast_add, Rat.cast_one,
      Rat.cast_div, Rat.cast_pow, Rat.cast_sub] using herr
  have hsum := sumBalls_contains (fun i => (w.nodes i).sound p w.center ht hq ha hc hcenter'
    h (rationalQuadrature32.node i) (rationalQuadrature32.weight i) (hnodes i))
  have hsum' : (sumBalls (fun i => ((w.nodes i).output.toBall rootDyadicConfig.prec))).Contains
      (rationalQuadrature32.apply (thetaA t a) c (h : ℝ)) := by
    simpa only [QuadratureRule.apply, Complex.ofReal_ratCast] using hsum
  exact ⟨coarsen_contains (inflate_contains hsum' herr') hout, han⟩

end RootDyadicCell
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RootDyadicCell.sound
