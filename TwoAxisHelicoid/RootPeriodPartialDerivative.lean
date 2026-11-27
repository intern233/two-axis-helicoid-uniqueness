import TwoAxisHelicoid.RootCompositeContinuity
import TwoAxisHelicoid.CompactIntegralDerivative

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter
open scoped Topology
attribute [local irreducible] thetaA thetaJet thetaQuotient

noncomputable def rootPeriodDa (t a : ℝ) : ℝ :=
  (∫ x : ℝ in (-1)..0, thetaAa t a ((x : ℂ)+I*((t/2 : ℝ) : ℂ))).re

noncomputable def rootPeriodDt (t a : ℝ) : ℝ :=
  (∫ x : ℝ in (-1)..0, thetaAtMidline t a ((x : ℂ)+I*((t/2 : ℝ) : ℂ))).re

theorem root_period_a_hasDerivAt {t a : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (ha : a ∈ Ioo (rootALower : ℝ) rootAUpper) :
    HasDerivAt (thetaHorizontalPeriod t) (rootPeriodDa t a) a := by
  let S : Set (ℝ × ℝ) := Icc (rootALower : ℝ) rootAUpper ×ˢ Icc (-1 : ℝ) 0
  have hc := root_composite_continuousOn (S := S) (u := fun _ => t) (b := Prod.fst) (x := Prod.snd)
    continuousOn_const continuous_fst.continuousOn continuous_snd.continuousOn
    (fun _ _ => ⟨htl,htu⟩) (fun _ hp => hp.1)
  have hd : ∀ s ∈ Ioo (rootALower : ℝ) rootAUpper, ∀ x ∈ Icc (-1 : ℝ) 0,
      HasDerivAt (fun b : ℝ => thetaA t b ((x : ℂ)+I*((t/2 : ℝ) : ℂ)))
        (thetaAa t s ((x : ℂ)+I*((t/2 : ℝ) : ℂ))) s := by
    intro s hs x _
    have he := rootDerivativeParameters.sound rootDerivativeParameters_valid htl htu hs.1.le hs.2.le
    exact thetaA_a_hasDerivAt (lt_of_lt_of_le (by norm_num [rootTLower]) htl) s _
      he.abscissa_ne (root_horizontal_regular htl htu x) (root_horizontal_shift_regular htl htu s x)
  have hi := hasDerivAt_intervalIntegral_compact ha (by norm_num : (-1 : ℝ) ≤ 0) hc.1 hc.2.1 hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hi
  have heq : thetaHorizontalPeriod t = (fun b : ℝ =>
      (∫ x : ℝ in (-1)..0, thetaA t b ((x : ℂ)+I*((t/2 : ℝ) : ℂ))).re) := by
    funext b
    exact root_horizontal_period_half htl htu b
  rw [heq]
  exact hr

theorem root_period_t_hasDerivAt {t a : ℝ}
    (ht : t ∈ Ioo (rootTLower : ℝ) rootTUpper)
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    HasDerivAt (fun s => thetaHorizontalPeriod s a) (rootPeriodDt t a) t := by
  let S : Set (ℝ × ℝ) := Icc (rootTLower : ℝ) rootTUpper ×ˢ Icc (-1 : ℝ) 0
  have hc := root_composite_continuousOn (S := S) (u := Prod.fst) (b := fun _ => a) (x := Prod.snd)
    continuous_fst.continuousOn continuousOn_const continuous_snd.continuousOn
    (fun _ hp => hp.1) (fun _ _ => ⟨hal,hau⟩)
  have hd : ∀ s ∈ Ioo (rootTLower : ℝ) rootTUpper, ∀ x ∈ Icc (-1 : ℝ) 0,
      HasDerivAt (fun r : ℝ => thetaA r a ((x : ℂ)+I*((r/2 : ℝ) : ℂ)))
        (thetaAtMidline s a ((x : ℂ)+I*((s/2 : ℝ) : ℂ))) s := by
    intro s hs x _
    have he := rootDerivativeParameters.sound rootDerivativeParameters_valid hs.1.le hs.2.le hal hau
    have hp : HasDerivAt (fun r : ℝ => (x : ℂ)+I*((r/2 : ℝ) : ℂ)) (I/2) s := by
      convert ((((hasDerivAt_id s).div_const 2).ofReal_comp).const_mul I).const_add (x : ℂ) using 1 <;> simp [div_eq_mul_inv]
    have h := thetaA_curve_hasDerivAt (hasDerivAt_id s) (hasDerivAt_const s a) hp
      (lt_of_lt_of_le (by norm_num [rootTLower]) hs.1.le) he.zero_ne he.abscissa_ne
      (root_horizontal_regular hs.1.le hs.2.le x) (root_horizontal_shift_regular hs.1.le hs.2.le a x)
    simpa only [id_eq, thetaAtMidline, Complex.ofReal_one, Complex.ofReal_zero,
      one_mul, zero_mul, add_zero] using h
  have hi := hasDerivAt_intervalIntegral_compact ht (by norm_num : (-1 : ℝ) ≤ 0) hc.1 hc.2.2 hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hi
  apply hr.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact root_horizontal_period_half hs.1.le hs.2.le a

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_period_a_hasDerivAt
#print axioms TwoAxisHelicoid.root_period_t_hasDerivAt
