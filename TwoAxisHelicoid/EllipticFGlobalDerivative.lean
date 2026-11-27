import TwoAxisHelicoid.EllipticFSmallHeight

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

theorem ellipticFReal_hasDerivAt_small {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1/2) :
    HasDerivAt ellipticFReal
      ((deriv ellipticFReal (1/t)+2*t*ellipticFReal (1/t)-Real.pi*t^2)/t^4) t := by
  have hi : 1/2 ≤ 1/t := (le_div_iff₀ ht).mpr (by linarith)
  have hinv : HasDerivAt (fun s : ℝ => 1/s) (-1/t^2) t := by
    simpa only [one_div,neg_div] using hasDerivAt_inv ht.ne'
  have hcomp := (ellipticFReal_hasDerivAt hi).differentiableAt.hasDerivAt.comp t hinv
  have hd := ((hasDerivAt_const t Real.pi).div (hasDerivAt_id t) ht.ne').sub
    (hcomp.div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht.ne'))
  have he : ellipticFReal =ᶠ[𝓝 t] fun s => Real.pi/s-ellipticFReal (1/s)/s^2 := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact ellipticFReal_reciprocal hs
  simp only [Function.comp_def,Pi.pow_apply,id_eq] at hd
  convert hd.congr_of_eventuallyEq he using 1
  field_simp
  ring

theorem ellipticFReal_differentiableAt {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ ellipticFReal t := by
  by_cases h : 1/2 ≤ t
  · exact (ellipticFReal_hasDerivAt h).differentiableAt
  · exact (ellipticFReal_hasDerivAt_small ht (le_of_not_ge h)).differentiableAt

theorem ellipticFReal_deriv_pos_of_pos {t : ℝ} (ht : 0 < t) :
    0 < deriv ellipticFReal t := by
  by_cases h : 1/2 ≤ t
  · exact ellipticFReal_deriv_pos h
  · have ht2 : t ≤ 1/2 := le_of_not_ge h
    have hi : 2 ≤ 1/t := (le_div_iff₀ ht).mpr (by linarith)
    have hD := ellipticFReal_deriv_pos (show 1/2 ≤ 1/t by linarith)
    have hF := ellipticFReal_gt_two hi
    have hp : Real.pi*t < 2 := by nlinarith [Real.pi_lt_four]
    have hm : 0 < t*(2*ellipticFReal (1/t)-Real.pi*t) := mul_pos ht (by linarith)
    rw [(ellipticFReal_hasDerivAt_small ht ht2).deriv]
    exact div_pos (by nlinarith) (pow_pos ht 4)

theorem ellipticFReal_strictMono_of_pos : StrictMonoOn ellipticFReal (Ioi (0:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro t ht
    exact (ellipticFReal_differentiableAt ht).continuousAt.continuousWithinAt
  · intro t ht
    exact ellipticFReal_deriv_pos_of_pos (interior_subset ht)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_strictMono_of_pos
