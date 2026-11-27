import TwoAxisHelicoid.ThetaHeat

/-!
The actual theta expressions used by the interval certificates.
Derivative formulas require precisely the stated nonzero denominators;
their uniform nonvanishing over certificate boxes is a separate obligation.
-/

namespace TwoAxisHelicoid
open Complex

noncomputable def thetaQuotient (t : ℝ) (j : ℕ) (v : ℂ) : ℂ :=
  thetaJet t j v / thetaJet t 0 v

noncomputable def thetaG (t a : ℝ) : ℂ :=
  (Real.pi^2 / 4 : ℂ) *
    ((thetaQuotient t 1 (Real.pi*a/2))^2 - thetaQuotient t 2 (Real.pi*a/2)) -
      (Real.pi/t : ℝ)

noncomputable def thetaA (t a : ℝ) (z : ℂ) : ℂ :=
  ((Real.pi * thetaJet t 1 0) / (2 * thetaJet t 0 (Real.pi*a/2)))^2 *
    (thetaJet t 0 (Real.pi*(z-a)/2) / thetaJet t 0 (Real.pi*z/2))^2 *
    Complex.exp ((a-1)*Real.pi*thetaQuotient t 1 (Real.pi*z/2))

theorem thetaJet_affine_hasDerivAt {t : ℝ} (ht : 0 < t) (j : ℕ)
    (c d : ℂ) (a : ℝ) :
    HasDerivAt (fun b : ℝ => thetaJet t j (c*b+d))
      (thetaJet t (j+1) (c*a+d) * c) a := by
  have harg := (((hasDerivAt_id a).ofReal_comp).const_mul c).add_const d
  simpa only [Function.comp_def, id_eq, Complex.ofReal_one, mul_one] using
    (thetaJet_hasDerivAt ht j (c*a+d)).comp a harg

theorem thetaQuotient_hasDerivAt {t : ℝ} (ht : 0 < t) (j : ℕ) (v : ℂ)
    (hv : thetaJet t 0 v ≠ 0) :
    HasDerivAt (thetaQuotient t j)
      (thetaQuotient t (j+1) v - thetaQuotient t j v * thetaQuotient t 1 v) v := by
  have hd := (thetaJet_hasDerivAt ht j v).div (thetaJet_hasDerivAt ht 0 v) hv
  convert hd using 1
  · rfl
  · simp only [thetaQuotient]
    field_simp

theorem thetaQuotient_parameter_hasDerivAt {t : ℝ} (ht : 0 < t) (j : ℕ) (v : ℂ)
    (hv : thetaJet t 0 v ≠ 0) :
    HasDerivAt (fun s : ℝ => thetaQuotient s j v)
      ((Real.pi/8 : ℂ) *
        (thetaQuotient t (j+2) v - thetaQuotient t j v * thetaQuotient t 2 v)) t := by
  have hd := (thetaJet_parameter_hasDerivAt ht j v).div
    (thetaJet_parameter_hasDerivAt ht 0 v) hv
  convert hd using 1
  · rfl
  · simp only [thetaQuotient]
    field_simp
    ring

theorem thetaQuotient_a_hasDerivAt {t : ℝ} (ht : 0 < t) (j : ℕ) (a : ℝ)
    (ha : thetaJet t 0 (Real.pi*a/2) ≠ 0) :
    HasDerivAt (fun b : ℝ => thetaQuotient t j (Real.pi*b/2))
      ((Real.pi/2 : ℂ) * (thetaQuotient t (j+1) (Real.pi*a/2) -
        thetaQuotient t j (Real.pi*a/2) * thetaQuotient t 1 (Real.pi*a/2))) a := by
  have hcast (b : ℝ) : (Real.pi*b/2 : ℂ) = ((Real.pi*b/2 : ℝ) : ℂ) := by push_cast; rfl
  have harg : HasDerivAt (fun b : ℝ => Real.pi*b/2) (Real.pi/2) a := by
    convert ((hasDerivAt_id a).const_mul Real.pi).div_const 2 using 1 <;> simp
  have hd := ((thetaQuotient_hasDerivAt ht j _ (by simpa only [hcast] using ha)).comp_ofReal).scomp a harg
  convert hd using 1
  · funext b
    rw [hcast]
    rfl
  · simp only [Complex.real_smul]
    push_cast
    ring

theorem thetaG_a_hasDerivAt {t : ℝ} (ht : 0 < t) (a : ℝ)
    (ha : thetaJet t 0 (Real.pi*a/2) ≠ 0) :
    HasDerivAt (thetaG t)
      ((Real.pi^3/8 : ℂ) *
        (3*thetaQuotient t 1 (Real.pi*a/2)*thetaQuotient t 2 (Real.pi*a/2) -
          2*(thetaQuotient t 1 (Real.pi*a/2))^3 - thetaQuotient t 3 (Real.pi*a/2))) a := by
  have h1 := thetaQuotient_a_hasDerivAt ht 1 a ha
  have h2 := thetaQuotient_a_hasDerivAt ht 2 a ha
  have hd := (((h1.pow 2).sub h2).const_mul (Real.pi^2/4 : ℂ)).sub_const ((Real.pi/t : ℝ) : ℂ)
  convert hd using 1
  · rfl
  · norm_num
    ring

theorem thetaG_parameter_hasDerivAt {t : ℝ} (ht : 0 < t) (a : ℝ)
    (ha : thetaJet t 0 (Real.pi*a/2) ≠ 0) :
    HasDerivAt (fun s : ℝ => thetaG s a)
      ((Real.pi^3/32 : ℂ) *
        (2*thetaQuotient t 1 (Real.pi*a/2) *
          (thetaQuotient t 3 (Real.pi*a/2) -
            thetaQuotient t 1 (Real.pi*a/2)*thetaQuotient t 2 (Real.pi*a/2)) -
          (thetaQuotient t 4 (Real.pi*a/2) - (thetaQuotient t 2 (Real.pi*a/2))^2)) +
        (Real.pi/t^2 : ℝ)) t := by
  have h1 := thetaQuotient_parameter_hasDerivAt ht 1 (Real.pi*a/2) ha
  have h2 := thetaQuotient_parameter_hasDerivAt ht 2 (Real.pi*a/2) ha
  have hp := ((hasDerivAt_const t Real.pi).div (hasDerivAt_id t) (ne_of_gt ht)).ofReal_comp
  have hd := (((h1.pow 2).sub h2).const_mul (Real.pi^2/4 : ℂ)).sub hp
  convert hd using 1
  · rfl
  · norm_num
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaG_a_hasDerivAt
#print axioms TwoAxisHelicoid.thetaG_parameter_hasDerivAt
