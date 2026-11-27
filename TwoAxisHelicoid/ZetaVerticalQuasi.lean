import TwoAxisHelicoid.ZetaPoleRegular
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval
attribute [local irreducible] thetaZeta thetaEtaExpression

noncomputable def zetaImaginaryQuasi (t : ℝ) : ℂ :=
  2*I*((t : ℂ)*thetaEtaExpression t-Real.pi)

theorem thetaZeta_add_vertical {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaZeta t (z+2*I*t) = thetaZeta t z+zetaImaginaryQuasi t := by
  have hτ : (1+I*(t : ℂ)) ∈ (rhombicPeriodPair t ht).lattice :=
    (rhombicPeriodPair t ht).ω₂_mem_lattice
  have hzτ : z+(1+I*t) ∉ (rhombicPeriodPair t ht).lattice := by
    intro hh
    apply hz
    simpa only [add_sub_cancel_right] using (rhombicPeriodPair t ht).lattice.sub_mem hh hτ
  have h := thetaZeta_add_half_of_pos ht ht hzτ
  rw [show z+(1+I*t)+(1+I*t) = (z+2*I*t)+2 by ring,
    thetaZeta_add_two,thetaZeta_add_half_of_pos ht ht hz] at h
  unfold zetaImaginaryQuasi
  linear_combination h

theorem rhombic_noninteger_vertical_not_mem {t x : ℝ} (ht : 0 < t)
    (hx : |x| < 1) (hn : x ≠ 0) (y : ℝ) :
    (x : ℂ)+(y : ℂ)*I ∉ (rhombicPeriodPair t ht).lattice := by
  intro hz
  obtain ⟨m,n,hr,_⟩ := (rhombic_mem_lattice_iff ht _).mp hz
  norm_num at hr
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hx
  have hmlo : (-1 : ℤ) < 2*m+n := by exact_mod_cast (hr ▸ hlo)
  have hmhi : 2*m+n < (1 : ℤ) := by exact_mod_cast (hr ▸ hhi)
  have he : 2*m+n = 0 := by omega
  have he' : (2 : ℝ)*m+n = 0 := by exact_mod_cast he
  exact hn (hr.trans he')

theorem thetaZeta_vertical_continuous {t x : ℝ} (ht : 0 < t)
    (hx : |x| < 1) (hn : x ≠ 0) : Continuous (fun y : ℝ => thetaZeta t ((x : ℂ)+(y : ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (thetaZeta_hasDerivAt_of_pos ht ht
    (rhombic_noninteger_vertical_not_mem ht hx hn y)).continuousAt.comp
      (f := fun y : ℝ => (x : ℂ)+(y : ℂ)*I) (by fun_prop)

noncomputable def zetaAxisDifference (t a y : ℝ) : ℂ :=
  thetaZeta t (-(a : ℂ)+(y : ℂ)*I)-thetaZeta t ((a : ℂ)+(y : ℂ)*I)

theorem zetaAxisDifference_continuous {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) :
    Continuous (zetaAxisDifference t a) := by
  have hp : |a| < 1 := by simpa [abs_of_pos ha.1] using ha.2
  have hm : |-a| < 1 := by simpa using hp
  change Continuous (fun y : ℝ => thetaZeta t (-(a : ℂ)+(y : ℂ)*I)-thetaZeta t ((a : ℂ)+(y : ℂ)*I))
  convert (thetaZeta_vertical_continuous ht hm (neg_ne_zero.mpr ha.1.ne')).sub
      (thetaZeta_vertical_continuous ht hp ha.1.ne') using 1
  funext y
  simp only [Pi.sub_apply,Complex.ofReal_neg]

theorem zetaAxisDifference_periodic {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) :
    Function.Periodic (zetaAxisDifference t a) (2*t) := by
  have hp : |a| < 1 := by simpa [abs_of_pos ha.1] using ha.2
  have hm : |-a| < 1 := by simpa using hp
  intro y
  unfold zetaAxisDifference
  have hplus := thetaZeta_add_vertical ht (rhombic_noninteger_vertical_not_mem ht hp ha.1.ne' y)
  have hminus := thetaZeta_add_vertical ht
    (rhombic_noninteger_vertical_not_mem ht hm (neg_ne_zero.mpr ha.1.ne') y)
  have he1 : -(a : ℂ)+((y+2*t : ℝ) : ℂ)*I = (-(a : ℂ)+(y : ℂ)*I)+2*I*t := by push_cast; ring
  have he2 : (a : ℂ)+((y+2*t : ℝ) : ℂ)*I = ((a : ℂ)+(y : ℂ)*I)+2*I*t := by push_cast; ring
  rw [he1,he2,hplus]
  rw [Complex.ofReal_neg] at hminus
  rw [hminus]
  ring

theorem zetaAxisDifference_integral_centered {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) :
    (∫ y : ℝ in 0..2*t, zetaAxisDifference t a y) =
      ∫ y : ℝ in -t..t, zetaAxisDifference t a y := by
  have h := (zetaAxisDifference_periodic ht ha).intervalIntegral_add_eq 0 (-t)
  rw [zero_add,show -t+2*t=t by ring] at h
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_add_vertical
#print axioms TwoAxisHelicoid.zetaAxisDifference_integral_centered
