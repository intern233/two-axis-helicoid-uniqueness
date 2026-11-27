import TwoAxisHelicoid.RhombicPrimitivePatches

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
set_option maxHeartbeats 1200000

theorem rhombicWedgePrimitive_lower_increment {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    {z : ℂ} (hz : z ∈ complexOpenRect (-2) 0 (-t) 0) :
    rhombicWedgePrimitive t f (z+(1+I*t))-rhombicWedgePrimitive t f z = rhombicUpPeriod t f := by
  let p := conj (originalPeriodPath t (-1))
  have hpL : p ∈ complexOpenRect (-2) 0 (-t) 0 := by
    norm_num [p,originalPeriodPath,complexOpenRect,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
    constructor <;> linarith
  have hbridge (w : ℂ) (hw : w ∈ complexOpenRect (-2) 0 (-t) 0) :
      w ∈ complexOpenRect (-2) 0 (-t) t := ⟨hw.1,⟨hw.2.1,hw.2.2.trans ht⟩⟩
  have hshift (w : ℂ) (hw : w ∈ complexOpenRect (-2) 0 (-t) 0) :
      HasDerivAt (fun w => rhombicWedgePrimitive t f (w+(1+I*t))) (f w) w := by
    have hwH : w+(1+I*t) ∈ complexHorizontalStrip 0 t := by
      change 0 < (w+(1+I*t)).im ∧ (w+(1+I*t)).im < t
      norm_num [Complex.mul_im]
      constructor <;> linarith [hw.2.1,hw.2.2]
    have hd := (rhombicWedgePrimitive_hasDerivAt_strip ht hf hwH).comp w
      ((hasDerivAt_id w).add_const (1+I*t))
    simpa only [Function.comp_def,id_eq,mul_one,hp w (1+I*t) (rhombicPeriodPair t ht).ω₂_mem_lattice]
      using hd
  have he := primitives_difference_at_base (complexOpenRect_isOpen (-2) 0 (-t) 0)
    (complexOpenRect_convex (-2) 0 (-t) 0).isPreconnected hshift
    (fun w hw => rhombicWedgePrimitive_hasDerivAt_bridge ht hf (hbridge w hw)) hpL z hz
  have hpeq : p+(1+I*t) = conj (originalPeriodPath t 1) := by
    dsimp [p,originalPeriodPath]
    simp only [map_add,map_sub,map_neg,map_one,map_div₀,map_mul,map_ofNat,Complex.conj_I,Complex.conj_ofReal]
    norm_num
    ring
  change rhombicWedgePrimitive t f (z+(1+I*t))-rhombicWedgePrimitive t f z =
    rhombicWedgePrimitive t f (p+(1+I*t))-rhombicWedgePrimitive t f p at he
  rw [he,hpeq,rhombicUpPeriod_eq_primitive ht hf]

theorem rhombicWedgePrimitive_lower_real_matching {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    (hup : (rhombicUpPeriod t f).re = 0)
    {z : ℂ} (hz : z ∈ complexOpenRect (-2) 0 (-t) 0) :
    (rhombicWedgePrimitive t f (z+(1+I*t))).re = (rhombicWedgePrimitive t f z).re := by
  have he := congrArg Complex.re (rhombicWedgePrimitive_lower_increment ht hf hp hz)
  rw [Complex.sub_re,hup] at he
  exact sub_eq_zero.mp he

theorem rhombicWedgePrimitive_horizontal_real_period {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    (hdown : (rhombicDownPeriod t f).re = 0) (hup : (rhombicUpPeriod t f).re = 0)
    {z : ℂ} (hz : z ∈ complexHorizontalStrip 0 t) :
    (rhombicWedgePrimitive t f (z+2)).re = (rhombicWedgePrimitive t f z).re := by
  let r := originalPeriodPath t (-1)
  let s := originalPeriodPath t 1
  have hr : r ∈ complexHorizontalStrip 0 t := by
    change 0 < r.im ∧ r.im < t
    norm_num [r,originalPeriodPath,Complex.mul_im,Complex.mul_re,Complex.div_im,Complex.div_re]
    exact ht
  have hs : s ∈ complexOpenRect (-2) 0 (-t) 0 := by
    norm_num [s,originalPeriodPath,complexOpenRect,Complex.mul_im,Complex.mul_re,Complex.div_im,Complex.div_re]
    constructor <;> linarith
  have hshift (w : ℂ) (hw : w ∈ complexHorizontalStrip 0 t) :
      HasDerivAt (fun w => rhombicWedgePrimitive t f (w+2)) (f w) w := by
    have hwH : w+2 ∈ complexHorizontalStrip 0 t := by simpa [complexHorizontalStrip] using hw
    have hd := (rhombicWedgePrimitive_hasDerivAt_strip ht hf hwH).comp w
      ((hasDerivAt_id w).add_const (2 : ℂ))
    simpa only [Function.comp_def,id_eq,mul_one,hp w 2 (rhombicPeriodPair t ht).ω₁_mem_lattice] using hd
  have he := primitives_difference_at_base (complexHorizontalStrip_isOpen 0 t)
    (complexHorizontalStrip_convex 0 t).isPreconnected hshift
    (fun w hw => rhombicWedgePrimitive_hasDerivAt_strip ht hf hw) hr z hz
  have hsr : s+(1+I*t) = r+2 := by dsimp [s,r,originalPeriodPath]; norm_num; ring
  have hlow := rhombicWedgePrimitive_lower_real_matching ht hf hp hup hs
  rw [hsr] at hlow
  have hdown' := congrArg Complex.re (rhombicDownPeriod_eq_primitive ht hf)
  rw [hdown,Complex.sub_re] at hdown'
  have hreal := congrArg Complex.re he
  simp only [Complex.sub_re] at hreal
  change (rhombicWedgePrimitive t f (z+2)).re-(rhombicWedgePrimitive t f z).re =
    (rhombicWedgePrimitive t f (r+2)).re-(rhombicWedgePrimitive t f r).re at hreal
  change 0 = (rhombicWedgePrimitive t f s).re-(rhombicWedgePrimitive t f r).re at hdown'
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombicWedgePrimitive_horizontal_real_period
