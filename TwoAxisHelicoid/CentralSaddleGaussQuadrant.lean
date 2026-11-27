import TwoAxisHelicoid.CentralRatioRectangle
import TwoAxisHelicoid.CentralHalfPeriodGaussValue

namespace TwoAxisHelicoid
open Complex Set

/-- The signs apply throughout the half-rectangle up to the saddle.
At central physical height the same signs determine the Gauss tangent. -/
theorem central_saddle_gauss_quadrant {t a : ℝ} (tb : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ab : a∈Icc (rootALower:ℝ) rootAUpper) (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (root : thetaG t a=0)
    (mid : (actualComplexHeight t a 1 ht ((1+I*t)/2)).re=0)
    (left : CheckedCentralRatioJets false true (1/2) 0 (7/16))
    (right : CheckedCentralRatioJets false true (3/5) 0 (7/16))
    (bottom : CheckedCentralRatioJets false false 0 (1/2) (3/5))
    (top : CheckedCentralRatioJets false false (7/16) (1/2) (3/5))
    (third : CheckedCentralRatioJets true true (1/2) 0 (7/16)) :
    let F := centralPhaseThetaRatio t a
    let G := thetaGauss t a 1
    let H := actualComplexHeight t a 1 ht
    ∀ x∈Ioc (1/2:ℝ) a, ∀ y∈Ioc (0:ℝ) (t/2), let z := (x:ℂ)+I*y
      (F z).re<0 ∧ 0<(F z).im ∧ ((H z).re=0 → (G z).re<0 ∧ (G z).im<0) := by
  intro F G H
  let m : ℂ := (1+I*t)/2
  have ax : (1/2:ℝ)<a := (by norm_num [rootALower] : (1/2:ℝ)<rootALower).trans_le ab.1
  have bx : a≤(3/5:ℝ) := ab.2.trans (by norm_num [rootAUpper])
  have my : t/2≤(7/16:ℝ) := by have k := tb.2; norm_num [rootTUpper] at k; linarith
  have big : 43/50≤t := (by norm_num [rootTLower] : (43/50:ℝ)≤rootTLower).trans tb.1
  have X {x : ℝ} (hx : x∈Icc (1/2:ℝ) a) : x∈Icc (1/2:ℝ) (3/5) := ⟨hx.1,hx.2.trans bx⟩
  have Y {y : ℝ} (hy : y∈Icc (0:ℝ) (t/2)) : y∈Icc (0:ℝ) (7/16) := ⟨hy.1,hy.2.trans my⟩
  obtain ⟨s,sp,scaled⟩ := central_level_gauss_theta_ratio ht ha root mid
  rw [central_half_period_gauss_value tb ab ht ha] at scaled
  have ri := congrArg re scaled
  change (-I).re=(I*(s:ℂ)*F m).re at ri
  simp [Complex.mul_re,Complex.mul_im] at ri
  have zero : (F m).im=0 := ri.resolve_left sp.ne'
  have midPoint : ((1/2:ℝ):ℂ)+I*(t/2:ℝ)=m := by dsimp [m]; push_cast; ring
  obtain ⟨second,three⟩ := central_ratio_rectangle_derivative_signs tb ab ht ha left right bottom top third
  have quadrant := rectangle_quadrant_of_real_jets (f:=F) ax (half_pos ht) (centralPhaseThetaRatio_conj t a)
    (fun x hx y hy => centralPhaseThetaRatio_analyticAt ht (central_ratio_rectangle_regular tb ht ha
      (by simpa using X hx) (by simpa using Y hy))) (fun x hx => by
      rcases hx.2.lt_or_eq with lt|rfl
      · exact (centralPhaseThetaRatio_real_segment big ha ⟨(by norm_num : (0:ℝ)<1/2).trans_le hx.1,lt⟩).le
      · simp [F,centralPhaseThetaRatio_saddle]) (by rw [midPoint,zero])
      (fun x hx y hy => second x (X hx) y (Y hy)) (fun y hy => (three y (Y hy)).le)
  intro x hx y hy z
  obtain ⟨lt,gt⟩ := quadrant x hx y hy
  refine ⟨lt,gt,fun level => ?_⟩
  obtain ⟨k,kp,e⟩ := central_level_gauss_theta_ratio ht ha root level
  change G z=I*(k:ℂ)*F z at e
  change (F z).re<0 at lt
  change 0<(F z).im at gt
  rw [e]
  constructor
  · simpa [Complex.mul_re,Complex.mul_im] using neg_lt_zero.mpr (mul_pos kp gt)
  · simpa [Complex.mul_re,Complex.mul_im] using mul_neg_of_pos_of_neg kp lt

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_saddle_gauss_quadrant
