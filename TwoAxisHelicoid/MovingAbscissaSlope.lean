import TwoAxisHelicoid.VerticalSquareLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

theorem moving_abscissa_slope_limit {f df : ℝ → ℝ → ℝ}
    (hd : ∀ t, 0 < t → ∀ a ∈ Ioo (0:ℝ) 2, HasDerivAt (f t) (df t a) a)
    (hzero : ∀ t, 0 < t → f t 1 = 0)
    (hc : ContinuousAt (fun p : ℝ × ℝ => df p.1 p.2) (ellipticVerticalUpper,1)) :
    Tendsto (fun t : ℝ => f t (verticalA t)/(verticalA t-1)) (𝓝[<] ellipticVerticalUpper)
      (𝓝 (df ellipticVerticalUpper 1)) := by
  have he (t : ℝ) (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
      ∃ c ∈ Ioo (verticalA t) 1, df t c = f t (verticalA t)/(verticalA t-1) := by
    have ha := (verticalA_spec ht).1
    have hunit (a : ℝ) (h : a ∈ Icc (verticalA t) 1) : a ∈ Ioo (0:ℝ) 2 :=
      ⟨ha.1.trans_le h.1,by linarith [h.2]⟩
    obtain ⟨c,hc,hh⟩ := exists_hasDerivAt_eq_slope (f t) (df t) ha.2
      (fun a h => (hd t ht.1 a (hunit a h)).continuousAt.continuousWithinAt)
      (fun a h => hd t ht.1 a (hunit a ⟨h.1.le,h.2.le⟩))
    refine ⟨c,hc,?_⟩
    rw [hh,hzero t ht.1,zero_sub,show 1-verticalA t = -(verticalA t-1) by ring,neg_div_neg_eq]
  let c := fun t : ℝ => if ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper then (he t ht).choose else 1
  have hcs (t : ℝ) (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
      c t ∈ Ioo (verticalA t) 1 ∧ df t (c t) = f t (verticalA t)/(verticalA t-1) := by
    simpa only [c,dite_eq_left ht] using (he t ht).choose_spec
  have hclim : Tendsto c (𝓝[<] ellipticVerticalUpper) (𝓝 1) := by
    apply verticalA_tendsto_one.squeeze' tendsto_const_nhds
    · filter_upwards [verticalDomain_eventually_left] with t ht
      exact (hcs t ht).1.1.le
    · filter_upwards [verticalDomain_eventually_left] with t ht
      exact (hcs t ht).1.2.le
  have harg := (tendsto_id'.mpr nhdsWithin_le_nhds).prodMk_nhds hclim
  apply (hc.tendsto.comp harg).congr'
  filter_upwards [verticalDomain_eventually_left] with t ht
  exact (hcs t ht).2

theorem thetaGa_branch_gap_ratio_limit :
    Tendsto (fun t : ℝ => (thetaGa t (verticalA t)).re/(verticalA t-1))
      (𝓝[<] ellipticVerticalUpper) (𝓝 (ellipticC ellipticVerticalUpper ellipticVerticalUpper_pos)) := by
  have h := moving_abscissa_slope_limit
    (f := fun t a => (thetaGa t a).re) (df := fun t a => (thetaLogFourth t a).re)
    (fun _ ht _ ha => thetaGa_real_hasDerivAt ht ha.1 ha.2)
    (fun t _ => by rw [thetaGa_one]; rfl)
    (thetaLogFourth_real_joint_continuousAt ellipticVerticalUpper_pos (by norm_num) (by norm_num))
  simpa only [Complex.ofReal_one,thetaLogFourth_one_re ellipticVerticalUpper_pos] using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaGa_branch_gap_ratio_limit
