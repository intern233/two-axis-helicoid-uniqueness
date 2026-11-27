import TwoAxisHelicoid.RootVerticalContinuity
import TwoAxisHelicoid.RootHorizontalRegular
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace TwoAxisHelicoid
open Set MeasureTheory
attribute [local irreducible] thetaJet thetaTerm thetaQuotient thetaA

theorem thetaJet_root_comp_continuous {X : Type*} [TopologicalSpace X]
    (t : X → RootHeight) (ht : Continuous t) (v : X → ℂ) (hv : Continuous v)
    (hb : ∀ x, |(v x).im| ≤ 1) (j : ℕ) :
    Continuous (fun x => thetaJet (t x) j (v x)) := by
  have hp : (0 : ℝ) < (rootTLower : ℝ) := by norm_num [rootTLower]
  have hm : Continuous (fun x => ((t x : ℝ), v x)) :=
    (continuous_subtype_val.comp ht).prodMk hv
  exact (thetaJet_joint_continuousOn (y := 1) hp j).comp_continuous hm
    (fun x => ⟨(t x).property.1, hb x⟩)

theorem root_horizontal_integrand_continuous :
    Continuous (fun p : RootHeight × ℝ =>
      thetaA p.1 (rootVerticalA p.1) ((p.2 : ℂ)+Complex.I*(((p.1 : ℝ)/2 : ℝ) : ℂ))) := by
  have ha : Continuous (fun p : RootHeight × ℝ => (rootVerticalA p.1 : ℝ)) :=
    continuous_subtype_val.comp (rootVerticalA_continuous.comp continuous_fst)
  let v : RootHeight × ℝ → ℂ := fun p =>
    Real.pi*((p.2 : ℂ)+Complex.I*(((p.1 : ℝ)/2 : ℝ) : ℂ))/2
  let w : RootHeight × ℝ → ℂ := fun p =>
    Real.pi*(((p.2 : ℂ)+Complex.I*(((p.1 : ℝ)/2 : ℝ) : ℂ))-(rootVerticalA p.1 : ℝ))/2
  let r : RootHeight × ℝ → ℂ := fun p => Real.pi*(rootVerticalA p.1 : ℝ)/2
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hvb : ∀ p, |(v p).im| ≤ 1 := by
    intro p
    have hi := root_horizontal_argument_im p.1.property.1 p.1.property.2 p.2
    have hpos : 0 ≤ (v p).im := by dsimp [v]; linarith [hi.1]
    rw [abs_of_nonneg hpos]
    dsimp [v]
    linarith [hi.2]
  have hwb : ∀ p, |(w p).im| ≤ 1 := by
    intro p
    have he : (w p).im = (v p).im := by simp [w, v, Complex.mul_im, Complex.mul_re]
    rw [he]
    exact hvb p
  have hrb : ∀ p, |(r p).im| ≤ 1 := by intro p; simp [r]
  have h0 := thetaJet_root_comp_continuous Prod.fst continuous_fst v hv hvb 0
  have h1 := thetaJet_root_comp_continuous Prod.fst continuous_fst v hv hvb 1
  have hm := thetaJet_root_comp_continuous Prod.fst continuous_fst w hw hwb 0
  have hsa := thetaJet_root_comp_continuous Prod.fst continuous_fst r hr hrb 0
  have hs1 := thetaJet_root_comp_continuous Prod.fst continuous_fst
    (fun _ : RootHeight × ℝ => (0 : ℂ)) continuous_const (by intro p; norm_num) 1
  have hne0 : ∀ p : RootHeight × ℝ, thetaJet p.1 0 (v p) ≠ 0 := by
    intro p
    exact root_horizontal_regular p.1.property.1 p.1.property.2 p.2
  have hnea : ∀ p : RootHeight × ℝ, thetaJet p.1 0 (r p) ≠ 0 := by
    intro p
    exact root_vertical_denominator p.1.property.1 p.1.property.2
      (rootVerticalA p.1).property.1 (rootVerticalA p.1).property.2
  have hden : ∀ p : RootHeight × ℝ, (2 : ℂ)*thetaJet p.1 0 (r p) ≠ 0 :=
    fun p => mul_ne_zero (by norm_num) (hnea p)
  have hc : Continuous (fun p : RootHeight × ℝ =>
      ((Real.pi*thetaJet p.1 1 0)/(2*thetaJet p.1 0 (r p)))^2) :=
    ((continuous_const.mul hs1).div (continuous_const.mul hsa) hden).pow 2
  have hrat := (hm.div h0 hne0).pow 2
  have hexp : Continuous (fun p : RootHeight × ℝ => Complex.exp
      (((rootVerticalA p.1 : ℝ)-1 : ℂ)*Real.pi*(thetaJet p.1 1 (v p)/thetaJet p.1 0 (v p)))) := by
    apply Complex.continuous_exp.comp
    exact ((Complex.continuous_ofReal.comp ha).sub continuous_const).mul continuous_const |>.mul (h1.div h0 hne0)
  convert (hc.mul hrat).mul hexp using 1
  funext p
  simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  simp only [thetaA, thetaQuotient, v, w, r]

theorem root_horizontal_period_continuous :
    Continuous (fun t : RootHeight => thetaHorizontalPeriod t (rootVerticalA t)) := by
  let : CompactSpace RootHeight := isCompact_iff_compactSpace.mp isCompact_Icc
  have h := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun (t : RootHeight) (x : ℝ) =>
      thetaA t (rootVerticalA t) ((x : ℂ)+Complex.I*(((t : ℝ)/2 : ℝ) : ℂ)))
    root_horizontal_integrand_continuous (s := Icc (-1 : ℝ) 1) isCompact_Icc
  have hi : Continuous (fun t : RootHeight => ∫ x : ℝ in (-1)..1,
      thetaA t (rootVerticalA t) ((x : ℂ)+Complex.I*(((t : ℝ)/2 : ℝ) : ℂ))) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc] using h
  exact continuous_const.mul (Complex.continuous_re.comp hi)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_horizontal_period_continuous
