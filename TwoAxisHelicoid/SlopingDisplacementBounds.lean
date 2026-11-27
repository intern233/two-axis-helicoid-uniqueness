import TwoAxisHelicoid.TraceDataSlopingDisplacement
import TwoAxisHelicoid.SlopingFluxBounds
import TwoAxisHelicoid.SlopingFluxRootParameters
import TwoAxisHelicoid.RealPrimitivePeriods
import TwoAxisHelicoid.OriginalPeriodRegularity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TwoAxisHelicoid
open Complex Set

/-- Derivative of the transverse spatial coordinate along the original
half-generator, expressed by its two separately checked theta kernels. -/
noncomputable def slopingTransverseRate (t a s : ℝ) : ℝ :=
  -(((1-I*t)/2)*(thetaA t a (originalPeriodPath t s)-thetaA t a (originalPeriodPath t (-s)))).im/2

theorem sloping_transverse_spatial_derivative {t a : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    HasDerivAt (fun u => X (originalPeriodPath t u) 1) (slopingTransverseRate t a s) s := by
  have off := rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht ⟨by linarith [hs.1],hs.2⟩)
  have deriv := (actual_coordinate_primitive_component ht d off 1).comp_hasDerivAt s (originalPeriodPath_hasDerivAt t s)
  let v : ℂ := (1-I*t)/2
  let k := thetaA t a (originalPeriodPath t s)-thetaA t a (originalPeriodPath t (-s))
  change HasDerivAt _ (v*(I*(1:ℂ)/2*(thetaA t a (originalPeriodPath t s)-thetaA t a (-originalPeriodPath t s)))).re s at deriv
  rw [thetaA_originalPath_neg] at deriv
  change HasDerivAt _ (v*(I*1/2*k)).re s at deriv
  change HasDerivAt _ (-(v*k).im/2) s
  rwa [show v*(I*1/2*k)=I*(v*k)/2 by ring,Complex.div_ofNat_re,Complex.I_mul_re] at deriv

namespace TraceData

private theorem difference_product_interpret (w : SlopingFluxCell) (prec : Nat) (v : DyadicBall) :
    (w.differenceProduct prec v).interpret =
      (v.interpret.toBall prec).mul ((w.plusTheta.output.interpret.toBall prec).sub (w.minusTheta.output.interpret.toBall prec)) := by
  simp only [SlopingFluxCell.differenceProduct,ComplexBall.interpret,QComplex.interpret,
    DyadicBall.toBall,DyadicBall.interpret,QComplex.mul,QComplex.absUpper,rat_abs_eq,
    ComplexBall.sub,ComplexBall.add,ComplexBall.neg,QComplex.add,QComplex.neg,
    TwoAxisHelicoid.DyadicBall.toBall,TwoAxisHelicoid.ComplexBall.mul,TwoAxisHelicoid.ComplexBall.sub,TwoAxisHelicoid.ComplexBall.add,
    TwoAxisHelicoid.ComplexBall.neg,TwoAxisHelicoid.QComplex.mul,TwoAxisHelicoid.QComplex.absUpper,TwoAxisHelicoid.QComplex.add,TwoAxisHelicoid.QComplex.neg]
  rfl

theorem SlopingFluxCell.transverse_rate_bounds (w : SlopingFluxCell) {t a s : ℝ}
    (ht : t∈Icc (rootTLower:ℝ) rootTUpper) (ha : a∈Icc (rootALower:ℝ) rootAUpper)
    {l r lo hi : ℚ} (hs : s∈Icc (l:ℝ) r)
    (check : w.check slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output l r=true)
    (bound : w.transverseBounds slopingFluxDataSetup.config.prec slopingFluxWeight.output lo hi) :
    slopingTransverseRate t a s ∈ Icc (lo:ℝ) hi := by
  obtain ⟨ht',hq,ha',hc,hv⟩ := sloping_flux_root_parameter_enclosures ht ha
  obtain ⟨hp,hm⟩ := w.kernel_enclosures slopingFluxAnalyticSetup slopingFluxAnalyticSetup_valid slopingFluxParams
    slopingFluxWeight.output ht' hq ha' hc hv hs.1 hs.2 check
  let B := w.differenceProduct slopingFluxDataSetup.config.prec slopingFluxWeight.output
  let z := ((1-I*t)/2)*(thetaA t a (originalPeriodPath t s)-thetaA t a (originalPeriodPath t (-s)))
  have mem : B.interpret.Contains z := by
    rw [show B.interpret=_ from difference_product_interpret ..]
    exact TwoAxisHelicoid.ComplexBall.mul_contains hv (TwoAxisHelicoid.ComplexBall.sub_contains hp hm)
  have proj := (Complex.abs_im_le_norm (z-B.interpret.center.val)).trans mem
  change |z.im-(B.center.im:ℝ)|≤(B.radius:ℝ) at proj
  obtain ⟨left,right⟩ := abs_le.mp proj
  have bounds : 2*(lo:ℝ)≤ -((B.center.im:ℝ)+B.radius) ∧ -((B.center.im:ℝ)-B.radius)≤2*(hi:ℝ) := by
    change 2*lo ≤ -(B.center.im+B.radius) ∧ -(B.center.im-B.radius) ≤ 2*hi at bound
    exact_mod_cast bound
  change (lo:ℝ)≤ -z.im/2 ∧ -z.im/2≤(hi:ℝ)
  constructor <;> linarith [bounds.1,bounds.2]

/-- A checked mesh bounds the displacement of every actual primitive,
including both sides of the mean-value bound on each rational cell. -/
theorem CheckedSlopingDisplacement.sound {t a : ℝ}
    (ht : t∈Icc (rootTLower:ℝ) rootTUpper) (ha : a∈Icc (rootALower:ℝ) rootAUpper)
    {f : ℝ → ℝ} (df : ∀ s∈Icc (0:ℝ) 1, HasDerivAt f (slopingTransverseRate t a s) s)
    {l r b c : ℚ} (cert : CheckedSlopingDisplacement slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output l r b c) :
    f r-f l∈Icc (b:ℝ) c := by
  induction cert with
  | cell w l r lo hi domain data bounds =>
    have d0 : (0:ℝ)≤(l:ℝ) := by exact_mod_cast domain.1
    have lr : (l:ℝ)<r := by exact_mod_cast domain.2.1
    have d1 : (r:ℝ)≤1 := by exact_mod_cast domain.2.2
    have sub := Icc_subset_Icc d0 d1
    obtain ⟨s,hs,eq⟩ := exists_hasDerivAt_eq_slope f (slopingTransverseRate t a) lr
      (fun x hx => (df x (sub hx)).continuousAt.continuousWithinAt)
      (fun x hx => df x (sub (Ioo_subset_Icc_self hx)))
    have both := w.transverse_rate_bounds ht ha (Ioo_subset_Icc_self hs) data bounds
    rw [eq] at both
    simpa only [Rat.cast_mul,Rat.cast_sub,mem_Icc] using
      And.intro ((le_div_iff₀ (sub_pos.mpr lr)).mp both.1) ((div_le_iff₀ (sub_pos.mpr lr)).mp both.2)
  | join _ _ left right =>
    simp only [Rat.cast_add,mem_Icc]
    constructor <;> linarith [left.1,left.2,right.1,right.2]
  | weaken _ lo hi ih =>
    exact ⟨(by exact_mod_cast lo : (_:ℝ)≤_).trans ih.1,ih.2.trans (by exact_mod_cast hi)⟩

end TraceData
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.TraceData.CheckedSlopingDisplacement.sound
