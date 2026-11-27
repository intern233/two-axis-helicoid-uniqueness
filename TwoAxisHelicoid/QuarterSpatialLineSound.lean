import TwoAxisHelicoid.QuarterSpatialLineData
import TwoAxisHelicoid.LowSlabEdgeSound
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TwoAxisHelicoid
open Complex Set ComplexBall
attribute [local irreducible] thetaA

noncomputable def quarterSpatialRate (first vertical : Bool) (z : ℂ) : ℝ :=
  let p := certifiedClosedParameters
  let j : Fin 3 := if first then 0 else 1
  ((if vertical then I else 1)*coordinateData p.t p.a 1 p.height_pos z j).re

theorem QuarterSpatialTrace.rate_bounds (w : QuarterSpatialTrace) {first d v : Bool} {e l r a b : ℚ}
    (ok : w.check first d v e l r a b) {x : ℝ} (hx : x∈Icc (l:ℝ) r) :
    quarterSpatialRate first d (centralBandEdgePoint v e x)∈Icc (a:ℝ) b := by
  let S := slopingFluxAnalyticSetup
  let p := certifiedClosedParameters
  obtain ⟨positive,negative,box,lo,hi⟩ := ok
  let z := centralBandEdgePoint v e x
  obtain ⟨lb,q,aval,coeff,_⟩ := sloping_flux_root_parameter_enclosures
    (Ioo_subset_Icc_self certifiedClosedParameters_bounds.1) (Ioo_subset_Icc_self certifiedClosedParameters_bounds.2)
  have inside : (w.box.toBall S.config.prec).Contains z := coarsen_contains (low_slab_edge_contains hx) box
  have pv := (w.positive.sound S.config S.terms S.error q aval coeff inside
    (S.tail_bound_one slopingFluxAnalyticSetup_valid lb 0) (S.tail_bound_one slopingFluxAnalyticSetup_valid lb 1) positive).1
  have mv := (w.negative.sound S.config S.terms S.error q aval coeff (DyadicBall.neg_contains inside)
    (S.tail_bound_one slopingFluxAnalyticSetup_valid lb 0) (S.tail_bound_one slopingFluxAnalyticSetup_valid lb 1) negative).1
  let P := w.positive.output.toBall S.config.prec
  let M := w.negative.output.toBall S.config.prec
  let U := thetaA p.t p.a z
  let V := thetaA p.t p.a (-z)
  have coords {B : ComplexBall} {u : ℂ} (c : B.Contains u) :
      |u.re-(B.center.re:ℝ)|≤B.radius ∧ |u.im-(B.center.im:ℝ)|≤B.radius :=
    ⟨(abs_re_le_norm (u-B.center.val)).trans c,(abs_im_le_norm (u-B.center.val)).trans c⟩
  obtain ⟨ur,ui⟩ := coords (B:=P) (u:=U) pv
  obtain ⟨vr,vi⟩ := coords (B:=M) (u:=V) mv
  have bound : (a:ℝ)≤(w.center first d:ℝ)-((P.radius:ℝ)+M.radius)/2 ∧
      (w.center first d:ℝ)+((P.radius:ℝ)+M.radius)/2≤(b:ℝ) := by exact_mod_cast And.intro lo hi
  have eq : quarterSpatialRate first d z =
      (if first then (if d then U.im+V.im else -(U.re+V.re))/2
       else (if d then V.re-U.re else V.im-U.im)/2) := by
    cases first <;> cases d <;> simp [quarterSpatialRate,coordinateData,U,V,p,Complex.mul_re,Complex.mul_im] <;> ring
  change quarterSpatialRate first d z∈Icc (a:ℝ) b
  rw [eq]
  have cent : ((w.center first d:ℚ):ℝ)=
      (if first then (if d then (P.center.im:ℝ)+M.center.im else -((P.center.re:ℝ)+M.center.re))/2
       else (if d then (M.center.re:ℝ)-P.center.re else (M.center.im:ℝ)-P.center.im)/2) := by
    cases first <;> cases d <;> simp [QuarterSpatialTrace.center,P,M,S]
  rw [cent] at bound
  cases first <;> cases d <;> simp only [Bool.false_eq_true,ite_false,ite_true] at bound ⊢
  all_goals constructor <;> linarith [(abs_le.mp ur).1,(abs_le.mp ur).2,(abs_le.mp ui).1,(abs_le.mp ui).2,
    (abs_le.mp vr).1,(abs_le.mp vr).2,(abs_le.mp vi).1,(abs_le.mp vi).2,bound.1,bound.2]

theorem CheckedQuarterSpatialLine.ordered {f d v e l r a b L U}
    (cert : CheckedQuarterSpatialLine f d v e l r a b L U) : l<r := by
  induction cert with
  | cell _ lr _ => exact lr
  | join _ _ first last => exact first.trans last

theorem CheckedQuarterSpatialLine.sound {first d v e l r a b L U}
    (cert : CheckedQuarterSpatialLine first d v e l r a b L U) :
    let rate := fun x : ℝ => quarterSpatialRate first d (centralBandEdgePoint v e x)
    (∀ x∈Icc (l:ℝ) r, rate x∈Icc (a:ℝ) b) ∧
      ∀ f : ℝ → ℝ, (∀ x∈Icc (l:ℝ) r, HasDerivAt f (rate x) x) → f r-f l∈Icc (L:ℝ) U := by
  intro rate
  induction cert with
  | @cell l r lo hi w lr cert =>
    have order : (l:ℝ)<r := by exact_mod_cast lr
    have val (x : ℝ) (hx : x∈Icc (l:ℝ) r) : rate x∈Icc (lo:ℝ) hi := w.rate_bounds cert hx
    refine ⟨val,?_⟩
    intro f df
    obtain ⟨x,hx,eq⟩ := exists_hasDerivAt_eq_slope f rate order
      (fun u hu => (df u hu).continuousAt.continuousWithinAt) (fun u hu => df u (Ioo_subset_Icc_self hu))
    have result := val x (Ioo_subset_Icc_self hx)
    rw [eq] at result
    simpa only [Rat.cast_mul,Rat.cast_sub,mem_Icc] using
      And.intro ((le_div_iff₀ (sub_pos.mpr order)).mp result.1) ((div_le_iff₀ (sub_pos.mpr order)).mp result.2)
  | @join l m r a b c f u w x y cl cr left right =>
    have lm : (l:ℝ)≤m := by exact_mod_cast cl.ordered.le
    have mr : (m:ℝ)≤r := by exact_mod_cast cr.ordered.le
    refine ⟨?_,?_⟩
    · intro z hz
      rcases le_total z (m:ℝ) with le|le
      · have v := left.1 z ⟨hz.1,le⟩
        exact ⟨(by exact_mod_cast min_le_left a c : ((min a c:ℚ):ℝ)≤a).trans v.1,
          v.2.trans (by exact_mod_cast le_max_left b f)⟩
      · have v := right.1 z ⟨le,hz.2⟩
        exact ⟨(by exact_mod_cast min_le_right a c : ((min a c:ℚ):ℝ)≤c).trans v.1,
          v.2.trans (by exact_mod_cast le_max_right b f)⟩
    · intro f df
      have u := left.2 f (fun u hu => df u ⟨hu.1,hu.2.trans mr⟩)
      have v := right.2 f (fun u hu => df u ⟨lm.trans hu.1,hu.2⟩)
      simp only [Rat.cast_add,mem_Icc]
      constructor <;> linarith [u.1,u.2,v.1,v.2]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.QuarterSpatialTrace.rate_bounds
#print axioms TwoAxisHelicoid.CheckedQuarterSpatialLine.sound
