import TwoAxisHelicoid.EllipticPeriodDerivative

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] thetaA thetaAtMidline thetaJet fullComplexPeriod

theorem fullComplexPeriod_t_hasDerivAt_integral {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (fun s => fullComplexPeriod s a)
      ((1/2:ℂ)*(∫ x : ℝ in (-1)..1, thetaAtMidline t a ((x:ℂ)+I*((t/2:ℝ):ℂ)))) t := by
  have hti : t ∈ Ioo (t/2) (3*t/2) := by constructor <;> linarith
  have hpos (s : ℝ) (hs : s ∈ Icc (t/2) (3*t/2)) : 0 < s := by linarith [hs.1]
  let S : Set (ℝ × ℝ) := Icc (t/2) (3*t/2) ×ˢ Icc (-1:ℝ) 1
  have hc := horizontal_composite_continuousOn (S := S) (u := Prod.fst)
    (b := fun _ => a) (x := Prod.snd) continuous_fst.continuousOn continuousOn_const
    continuous_snd.continuousOn (fun p hp => hpos p.1 hp.1) (fun _ _ => ha)
  have hd : ∀ s ∈ Ioo (t/2) (3*t/2), ∀ x ∈ Icc (-1:ℝ) 1,
      HasDerivAt (fun r : ℝ => thetaA r a ((x:ℂ)+I*((r/2:ℝ):ℂ)))
        (thetaAtMidline s a ((x:ℂ)+I*((s/2:ℝ):ℂ))) s := by
    intro s hs x _
    have hs0 := hpos s ⟨hs.1.le,hs.2.le⟩
    have hp : HasDerivAt (fun r : ℝ => (x:ℂ)+I*((r/2:ℝ):ℂ)) (I/2) s := by
      convert ((((hasDerivAt_id s).div_const 2).ofReal_comp).const_mul I).const_add (x:ℂ) using 1 <;> simp [div_eq_mul_inv]
    have h := thetaA_curve_hasDerivAt (hasDerivAt_id s) (hasDerivAt_const s a) hp hs0
      (thetaJet_one_at_zero_ne_zero_of_pos hs0) (theta_vertical_denominator hs0 ha.1 ha.2)
      (horizontal_midline_regular hs0 x) (horizontal_shift_regular hs0 a x)
    simpa only [id_eq,thetaAtMidline,Complex.ofReal_one,Complex.ofReal_zero,
      one_mul,zero_mul,add_zero] using h
  unfold fullComplexPeriod
  exact (hasDerivAt_intervalIntegral_compact hti (by norm_num : (-1:ℝ) ≤ 1) hc.1 hc.2.2 hd).const_mul (1/2:ℂ)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.fullComplexPeriod_t_hasDerivAt_integral
