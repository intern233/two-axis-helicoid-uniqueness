import TwoAxisHelicoid.SlopingDerivativeTraceData
import TwoAxisHelicoid.FirstSpatialDiskTrace
import TwoAxisHelicoid.EllipticPeriodDerivative
import TwoAxisHelicoid.DerivativeExpressions

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaJet thetaA

private theorem sloping_kernel_slope_value (t a : ℝ) (z v : ℂ) :
    slopingKernelSlopeExpression.value (complexInputList [a,thetaA t a z,thetaJet t 0 (Real.pi*z/2),
      thetaJet t 1 (Real.pi*z/2),thetaJet t 2 (Real.pi*z/2),thetaJet t 0 (Real.pi*(z-a)/2),
      thetaJet t 1 (Real.pi*(z-a)/2),v])= -v^2*(thetaA t a z*thetaLz t a z) := by
  simp only [slopingKernelSlopeExpression,
    BallExpression.value_pow,BallExpression.value_div,BallExpression.value_sub,BallExpression.value_rational,
    BallExpression.value,complexInputList,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    thetaLz,thetaQuotient,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  ring

theorem SlopingDerivativeTrace.sound (w : SlopingDerivativeTrace) {l r : ℚ} (ok : w.Valid l r)
    {t a s : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper) (ha : a∈Icc (rootALower:ℝ) rootAUpper)
    (hs : s∈Icc (l:ℝ) r) :
    0<(-(((1-I*t)/2)^2)*(deriv (thetaA t a) (originalPeriodPath t s))).im := by
  let S := slopingFluxAnalyticSetup
  let v : ℂ := (1-I*t)/2
  let z := originalPeriodPath t s
  obtain ⟨par,point,base,second,shifted,nonzero,checked,positive⟩ := ok
  obtain ⟨lo,q,ab,co,vel⟩ := sloping_flux_root_parameter_enclosures ht ha
  have regT : 0<t := lt_of_lt_of_le (by norm_num [rootTLower]) ht.1
  have regA : (a:ℂ)∈thetaRegular t := fun h =>
    real_not_mem_rhombic_lattice_of_pos regT (lt_of_lt_of_le (by norm_num [rootALower]) ha.1)
      (lt_of_le_of_lt ha.2 (by norm_num [rootAUpper])) ((thetaJet_zero_iff_rhombic_lattice_of_pos regT a).mp h)
  have hpar := ComplexBall.coarsen_contains (ComplexBall.realInterval_contains hs.1 hs.2) par
  have pt := w.point.sound S.config _ _ (threeDyadic_contains vel hpar (DyadicBall.zero_contains S.config.prec)) _ point
  have pv : (TraceData.slopingFluxPointExpression true).interpret.value (threeValues v (s:ℂ) 0)=z := by
    change (BallExpression.add (.neg (.rational 1)) (.mul (.input 0) (.input 1))).value _ = _
    simp only [BallExpression.value,BallExpression.value_rational,threeValues,Rat.cast_one,z,v,originalPeriodPath]
    ring
  rw [pv] at pt
  have tail := S.tail_bound_one slopingFluxAnalyticSetup_valid lo
  have hA := w.base.sound S.config S.terms S.error q ab co pt (tail 0) (tail 1) base
  obtain ⟨arg,sh,iy,iy',sz,sm,z0,z1,m0,_,_⟩ := base
  have inp := threeDyadic_contains pt ab (DyadicBall.zero_contains S.config.prec)
  have hz := w.base.argument.sound S.config _ _ inp _ arg
  have hm := w.base.shiftedArgument.sound S.config _ _ inp _ sh
  rw [value_thetaArgumentExpression] at hz
  rw [value_thetaShiftedArgumentExpression] at hm
  have se := w.base.seed.sound S.config hz sz
  have me := w.base.shiftedSeed.sound S.config hm sm
  have zy := DyadicBall.im_le_one hz iy
  have my := DyadicBall.im_le_one hm iy'
  have zz0 := w.base.theta0.sound S.config 0 S.terms S.error q _ se (tail 0 _ zy) z0
  have zz1 := w.base.theta1.sound S.config 1 S.terms S.error q _ se (tail 1 _ zy) z1
  have mm0 := w.base.thetaShifted.sound S.config 0 S.terms S.error q _ me (tail 0 _ my) m0
  have mm1 := w.shiftedFirst.sound S.config 1 S.terms S.error q _ me (tail 1 _ my) shifted
  have rem2 := firstDiskTail.remainder_bound S.config (4/5) 1 2 5 1048576
    (DyadicThetaTail.valid_of_checks firstDiskTail_valid) (by norm_num) lo (by simpa only [Rat.cast_one] using zy)
  have zz2 := w.second.sound S.config 2 S.terms S.error q _ se rem2 second
  have smn := ComplexBall.ne_zero_of_lower_pos mm0 (DyadicBall.lower_pos_toBall nonzero)
  let vs := [((a:ℝ):ℂ),thetaA t a z,thetaJet t 0 (Real.pi*z/2),thetaJet t 1 (Real.pi*z/2),
    thetaJet t 2 (Real.pi*z/2),thetaJet t 0 (Real.pi*(z-a)/2),thetaJet t 1 (Real.pi*(z-a)/2),v]
  have env : ∀ i, ((dyadicInputList w.inputs i).toBall S.config.prec).Contains (complexInputList vs i) :=
    dyadicInputList_contains (.cons ab (.cons hA.1 (.cons zz0 (.cons zz1 (.cons zz2 (.cons mm0 (.cons mm1 (.cons vel .nil))))))))
  have out := w.result.sound S.config _ _ env _ checked
  change (w.result.output.toBall S.config.prec).Contains (slopingKernelSlopeExpression.value (complexInputList _)) at out
  dsimp only [vs] at out
  rw [sloping_kernel_slope_value,← thetaA_spatial_deriv regT a regA hA.2 smn] at out
  let b := w.result.output.toBall S.config.prec
  let v' := -v^2*deriv (thetaA t a) z
  have abs := (Complex.abs_im_le_norm (v'-b.center.val)).trans out
  change |v'.im-(b.center.im:ℝ)|≤(b.radius:ℝ) at abs
  have pos : (b.radius:ℝ)<b.center.im := by exact_mod_cast positive
  change 0<v'.im
  linarith [(abs_le.mp abs).1]

theorem CheckedSlopingPositiveAcceleration.sound {l r : ℚ} (cert : CheckedSlopingPositiveAcceleration l r)
    {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper) (ha : a∈Icc (rootALower:ℝ) rootAUpper) :
    ∀ s∈Icc (l:ℝ) r, 0<(-(((1-I*t)/2)^2)*deriv (thetaA t a) (originalPeriodPath t s)).im := by
  induction cert with
  | cell w l r c => exact fun _ h => w.sound c ht ha h
  | @join l m r _ _ a b =>
    intro s hs
    rcases le_total s (m:ℝ) with h|h
    · exact a s ⟨hs.1,h⟩
    · exact b s ⟨h,hs.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedSlopingPositiveAcceleration.sound
