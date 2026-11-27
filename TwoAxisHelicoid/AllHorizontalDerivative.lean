import TwoAxisHelicoid.AllHorizontalContinuity
import TwoAxisHelicoid.CompactIntegralDerivative

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter
open scoped Topology
attribute [local irreducible] thetaA thetaJet thetaQuotient

theorem horizontal_period_a_hasDerivAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (thetaHorizontalPeriod t) (horizontalPeriodDa t a) a := by
  let l := a/2
  let u := (a+2)/2
  have hlu : a ∈ Ioo l u := by dsimp [l,u]; constructor <;> linarith [ha.1,ha.2]
  have hunit (s : ℝ) (hs : s ∈ Icc l u) : s ∈ Ioo (0:ℝ) 2 := by
    dsimp [l,u] at hs
    constructor <;> linarith [ha.1,ha.2,hs.1,hs.2]
  let S : Set (ℝ × ℝ) := Icc l u ×ˢ Icc (-1:ℝ) 0
  have hc := horizontal_composite_continuousOn (S := S) (u := fun _ => t)
    (b := Prod.fst) (x := Prod.snd) continuousOn_const continuous_fst.continuousOn
    continuous_snd.continuousOn (fun _ _ => ht) (fun p hp => hunit p.1 hp.1)
  have hd : ∀ s ∈ Ioo l u, ∀ x ∈ Icc (-1:ℝ) 0,
      HasDerivAt (fun b : ℝ => thetaA t b ((x:ℂ)+I*((t/2:ℝ):ℂ)))
        (thetaAa t s ((x:ℂ)+I*((t/2:ℝ):ℂ))) s := by
    intro s hs x _
    have hs2 := hunit s ⟨hs.1.le,hs.2.le⟩
    exact thetaA_a_hasDerivAt ht s _ (theta_vertical_denominator ht hs2.1 hs2.2)
      (horizontal_midline_regular ht x) (horizontal_shift_regular ht s x)
  have hi := hasDerivAt_intervalIntegral_compact hlu (by norm_num : (-1:ℝ) ≤ 0) hc.1 hc.2.1 hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hi
  have heq : thetaHorizontalPeriod t = (fun b : ℝ =>
      (∫ x : ℝ in (-1)..0, thetaA t b ((x:ℂ)+I*((t/2:ℝ):ℂ))).re) :=
    funext (horizontal_period_half ht)
  rw [heq]
  exact hr

theorem horizontal_period_t_hasDerivAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (fun s => thetaHorizontalPeriod s a) (horizontalPeriodDt t a) t := by
  have hti : t ∈ Ioo (t/2) (3*t/2) := by constructor <;> linarith
  have hpos (s : ℝ) (hs : s ∈ Icc (t/2) (3*t/2)) : 0 < s := by linarith [hs.1]
  let S : Set (ℝ × ℝ) := Icc (t/2) (3*t/2) ×ˢ Icc (-1:ℝ) 0
  have hc := horizontal_composite_continuousOn (S := S) (u := Prod.fst)
    (b := fun _ => a) (x := Prod.snd) continuous_fst.continuousOn continuousOn_const
    continuous_snd.continuousOn (fun p hp => hpos p.1 hp.1) (fun _ _ => ha)
  have hd : ∀ s ∈ Ioo (t/2) (3*t/2), ∀ x ∈ Icc (-1:ℝ) 0,
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
  have hi := hasDerivAt_intervalIntegral_compact hti (by norm_num : (-1:ℝ) ≤ 0) hc.1 hc.2.2 hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hi
  apply hr.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
  exact horizontal_period_half (hpos s ⟨hs.1.le,hs.2.le⟩) a

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_period_t_hasDerivAt
