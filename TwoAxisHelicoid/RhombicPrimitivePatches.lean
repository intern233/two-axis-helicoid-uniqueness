import TwoAxisHelicoid.StripPrimitives
import TwoAxisHelicoid.OriginalSlopingPeriod

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Topology Interval ComplexConjugate
set_option maxHeartbeats 1200000

noncomputable def rhombicPrimitiveBase (t : ℝ) : ℂ := -1/2+I*t/2
noncomputable def rhombicWedgePrimitive (t : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  wedgeIntegral (rhombicPrimitiveBase t) z f

noncomputable def rhombicDownPeriod (t : ℝ) (f : ℂ → ℂ) : ℂ :=
  ((1-I*t)/2)*(∫ s : ℝ in (-1)..1, f (originalPeriodPath t s))
noncomputable def rhombicUpPeriod (t : ℝ) (f : ℂ → ℂ) : ℂ :=
  ((1+I*t)/2)*(∫ s : ℝ in (-1)..1, f (conj (originalPeriodPath t s)))

theorem rhombic_horizontal_strip_not_mem {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ complexHorizontalStrip 0 t) : z ∉ (rhombicPeriodPair t ht).lattice := by
  intro h
  obtain ⟨m,n,_,hn⟩ := (rhombic_mem_lattice_iff ht z).mp h
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by nlinarith [hz.1])
  have hn1 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by nlinarith [hz.2])
  omega

theorem rhombicPrimitiveBase_mem {t : ℝ} (ht : 0 < t) :
    rhombicPrimitiveBase t ∈ complexOpenRect (-2) 0 0 t := by
  norm_num [rhombicPrimitiveBase,complexOpenRect,Complex.mul_re,Complex.mul_im]
  exact ht

theorem rhombicWedgePrimitive_hasDerivAt_strip {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    {z : ℂ} (hz : z ∈ complexHorizontalStrip 0 t) :
    HasDerivAt (rhombicWedgePrimitive t f) (f z) z :=
  holomorphic_horizontal_strip_has_primitive
    (fun w hw => (hf w (rhombic_horizontal_strip_not_mem ht hw)).differentiableAt.differentiableWithinAt)
    (rhombicPrimitiveBase_mem ht).2 z hz

theorem rhombicWedgePrimitive_hasDerivAt_bridge {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    {z : ℂ} (hz : z ∈ complexOpenRect (-2) 0 (-t) t) :
    HasDerivAt (rhombicWedgePrimitive t f) (f z) z := by
  have hb := rhombicPrimitiveBase_mem ht
  apply holomorphic_rectangle_has_primitive
    (fun w hw => (hf w (rhombic_open_rectangle_not_mem ht hw)).differentiableAt.differentiableWithinAt)
    (show rhombicPrimitiveBase t ∈ complexOpenRect (-2) 0 (-t) t from
      ⟨hb.1,by constructor <;> linarith [hb.2.1,hb.2.2]⟩) z hz

theorem conjugatePeriodPath_mem_rectangle {t : ℝ} (ht : 0 < t) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    conj (originalPeriodPath t s) ∈ complexOpenRect (-2) 0 (-t) t := by
  have h := originalPeriodPath_mem_rectangle ht hs
  change (conj (originalPeriodPath t s)).re ∈ Ioo (-2) 0 ∧
    (conj (originalPeriodPath t s)).im ∈ Ioo (-t) t
  rw [Complex.conj_re,Complex.conj_im]
  exact ⟨h.1,by constructor <;> linarith [h.2.1,h.2.2]⟩

theorem originalPeriodPath_hasDerivAt (t s : ℝ) :
    HasDerivAt (originalPeriodPath t) ((1-I*t)/2) s := by
  convert ((((hasDerivAt_id s).ofReal_comp).mul_const (1-I*t)).div_const 2).const_add (-1 : ℂ) using 1
  · rfl
  · simp

theorem conjugatePeriodPath_hasDerivAt (t s : ℝ) :
    HasDerivAt (fun s => conj (originalPeriodPath t s)) ((1+I*t)/2) s := by
  have he : (fun s : ℝ => conj (originalPeriodPath t s)) =
      fun s : ℝ => -1+(s : ℂ)*(1+I*t)/2 := by
    funext s
    simp [originalPeriodPath,map_ofNat]
  rw [he]
  convert ((((hasDerivAt_id s).ofReal_comp).mul_const (1+I*t)).div_const 2).const_add (-1 : ℂ) using 1
  · rfl
  · simp

theorem rhombicDownPeriod_eq_primitive {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z) :
    rhombicDownPeriod t f = rhombicWedgePrimitive t f (originalPeriodPath t 1)-
      rhombicWedgePrimitive t f (originalPeriodPath t (-1)) := by
  have hmaps (s : ℝ) (hs : s ∈ uIcc (-1 : ℝ) 1) :=
    originalPeriodPath_mem_rectangle ht (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs)
  have hc : ContinuousOn (fun s => f (originalPeriodPath t s)) (uIcc (-1 : ℝ) 1) := by
    intro s hs
    exact (hf _ (rhombic_open_rectangle_not_mem ht (hmaps s hs))).continuousAt.comp_continuousWithinAt
      (by unfold originalPeriodPath; fun_prop)
  exact primitive_path_integral_eq_sub (fun s _ => originalPeriodPath_hasDerivAt t s)
    (fun s hs => rhombicWedgePrimitive_hasDerivAt_bridge ht hf (hmaps s hs)) hc.intervalIntegrable

theorem rhombicUpPeriod_eq_primitive {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z) :
    rhombicUpPeriod t f = rhombicWedgePrimitive t f (conj (originalPeriodPath t 1))-
      rhombicWedgePrimitive t f (conj (originalPeriodPath t (-1))) := by
  have hmaps (s : ℝ) (hs : s ∈ uIcc (-1 : ℝ) 1) :=
    conjugatePeriodPath_mem_rectangle ht (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs)
  have hc : ContinuousOn (fun s => f (conj (originalPeriodPath t s))) (uIcc (-1 : ℝ) 1) := by
    intro s hs
    have hpath : ContinuousWithinAt (fun s => conj (originalPeriodPath t s)) (uIcc (-1 : ℝ) 1) s :=
      (Complex.continuous_conj.comp (show Continuous (originalPeriodPath t) by
        unfold originalPeriodPath; fun_prop)).continuousWithinAt
    exact (hf _ (rhombic_open_rectangle_not_mem ht (hmaps s hs))).continuousAt.comp_continuousWithinAt
      (f := fun s => conj (originalPeriodPath t s)) hpath
  exact primitive_path_integral_eq_sub (fun s _ => conjugatePeriodPath_hasDerivAt t s)
    (fun s hs => rhombicWedgePrimitive_hasDerivAt_bridge ht hf (hmaps s hs)) hc.intervalIntegrable

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombicWedgePrimitive_hasDerivAt_strip
#print axioms TwoAxisHelicoid.rhombicUpPeriod_eq_primitive
