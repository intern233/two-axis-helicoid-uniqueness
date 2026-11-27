import TwoAxisHelicoid.ThetaJointDerivative
import TwoAxisHelicoid.ThetaADerivative

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 2000000
attribute [local irreducible] thetaJet thetaTerm thetaQuotient

noncomputable def thetaLz (t a : ℝ) (z : ℂ) : ℂ :=
  Real.pi*(thetaQuotient t 1 (Real.pi*(z-a)/2)-thetaQuotient t 1 (Real.pi*z/2))+
    ((a-1)*Real.pi^2/2 : ℂ)*(thetaQuotient t 2 (Real.pi*z/2)-
      (thetaQuotient t 1 (Real.pi*z/2))^2)

theorem thetaA_curve_hasDerivAt {u b : ℝ → ℝ} {z : ℝ → ℂ}
    {s du db : ℝ} {dz : ℂ} (hu : HasDerivAt u du s) (hb : HasDerivAt b db s)
    (hz : HasDerivAt z dz s) (ht : 0 < u s)
    (hzero : thetaJet (u s) 1 0 ≠ 0)
    (ha : thetaJet (u s) 0 (Real.pi*b s/2) ≠ 0)
    (hv : thetaJet (u s) 0 (Real.pi*z s/2) ≠ 0)
    (hm : thetaJet (u s) 0 (Real.pi*(z s-b s)/2) ≠ 0) :
    HasDerivAt (fun r : ℝ => thetaA (u r) (b r) (z r))
      (thetaA (u s) (b s) (z s)*((du : ℂ)*thetaLt (u s) (b s) (z s)+
        (db : ℂ)*thetaLa (u s) (b s) (z s)+dz*thetaLz (u s) (b s) (z s))) s := by
  have hva := (hb.ofReal_comp.const_mul (Real.pi : ℂ)).div_const 2
  have hvz := (hz.const_mul (Real.pi : ℂ)).div_const 2
  have hvm := ((hz.sub hb.ofReal_comp).const_mul (Real.pi : ℂ)).div_const 2
  have hd0 := thetaJet_curve_hasDerivAt hu (hasDerivAt_const s (0 : ℂ)) ht 1
  have hda := thetaJet_curve_hasDerivAt hu hva ht 0
  have hdz0 := thetaJet_curve_hasDerivAt hu hvz ht 0
  have hdz1 := thetaJet_curve_hasDerivAt hu hvz ht 1
  have hdm := thetaJet_curve_hasDerivAt hu hvm ht 0
  have hp := ((hd0.const_mul (Real.pi : ℂ)).div
    (hda.const_mul 2) (mul_ne_zero (by norm_num) ha)).pow 2
  have hr := (hdm.div hdz0 hv).pow 2
  have he := (((hb.ofReal_comp.sub_const 1).mul_const (Real.pi : ℂ)).mul
    (hdz1.div hdz0 hv)).cexp
  have hd := (hp.mul hr).mul he
  convert hd using 1
  · funext r
    simp only [thetaA, thetaQuotient, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.sub_apply]
  · simp [thetaA, thetaLt, thetaLa, thetaLz, thetaQuotient]
    field_simp
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaA_curve_hasDerivAt
