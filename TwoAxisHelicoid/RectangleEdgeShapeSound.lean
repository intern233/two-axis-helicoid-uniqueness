import TwoAxisHelicoid.RectangleEdgeShapeData
import TwoAxisHelicoid.CertifiedFirstSpatialDisk
import TwoAxisHelicoid.ThetaLogHigher

namespace TwoAxisHelicoid
open Complex Set ComplexBall
attribute [local irreducible] thetaJet

noncomputable def rectangleEdgeShapeValue (b : Bool) (y : ℝ) : ℝ :=
  let t := certifiedClosedParameters.t
  if b then (thetaLogThird t (((1/2:ℝ):ℂ)+I*y)).im
  else Real.pi/t-(thetaLogSecond t (((5/8:ℝ):ℂ)+I*y)).re

private theorem rectangle_edge_jet_sound {b : Bool} {l r : ℚ} (w : RectangleEdgeJetTrace)
    (ok : rectangleShapeCheck b l r w) {y : ℝ} (ys : y∈Icc (l:ℝ) r) : 0<rectangleEdgeShapeValue b y := by
  let c : ℚ := if b then 1/2 else 5/8
  let z : ℂ := (c:ℂ)+I*y
  let p := certifiedClosedParameters
  let S := slopingFluxAnalyticSetup
  let q := TraceData.slopingFluxParams
  obtain ⟨box,arg,yi,sd,j0,j1,j2,j3,fx,pos⟩ := ok
  have eb : |y-((l+r)/2:ℚ)|≤((r-l)/2:ℚ) := by push_cast; exact abs_le.mpr ⟨by linarith [ys.1],by linarith [ys.2]⟩
  have inside : (w.box.toBall S.config.prec).Contains z := coarsen_contains (a:=centralBandEdgeBall true c l r) (by
    change ‖z-(⟨(c:ℝ),(((l+r)/2:ℚ):ℝ)⟩:ℂ)‖≤((r-l)/2:ℚ)
    rwa [show z-(⟨(c:ℝ),(((l+r)/2:ℚ):ℝ)⟩:ℂ)=I*((y-((l+r)/2:ℚ):ℝ):ℂ) by apply Complex.ext <;> simp [z],
      norm_mul,norm_I,one_mul,norm_real,Real.norm_eq_abs]) box
  obtain ⟨ht,ha⟩ := certifiedClosedParameters_bounds
  obtain ⟨lo,hq,_⟩ := sloping_flux_root_parameter_enclosures (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self ha)
  have ht' := coarsen_contains (realInterval_contains ht.1.le ht.2.le) firstDiskNumbers.2.2.2
  have av := w.argument.sound S.config _ _ (threeDyadic_contains inside (DyadicBall.zero_contains _) (DyadicBall.zero_contains _)) _ arg
  rw [value_thetaArgumentExpression] at av
  have seed := w.seed.sound S.config av sd
  have bound := DyadicBall.im_le_one av yi
  let u := Real.pi*z/2
  have e0 := w.j0.sound S.config 0 S.terms S.error hq _ seed (S.tail_bound_one slopingFluxAnalyticSetup_valid lo 0 _ bound) j0
  have e1 := w.j1.sound S.config 1 S.terms S.error hq _ seed (S.tail_bound_one slopingFluxAnalyticSetup_valid lo 1 _ bound) j1
  have e2 := w.j2.sound S.config 2 S.terms S.error hq _ seed
    (firstDiskTail.remainder_bound S.config (4/5) 1 2 5 1048576 (DyadicThetaTail.valid_of_checks firstDiskTail_valid)
      (by norm_num) lo (by simpa only [Rat.cast_one] using bound)) j2
  have e3 := w.j3.sound S.config 3 S.terms S.error hq _ seed
    (rectangleEdgeThirdTail.remainder_bound S.config (4/5) 1 3 5 1048576 (DyadicThetaTail.valid_of_checks rectangleEdgeThirdTail_valid)
      (by norm_num) lo (by simpa only [Rat.cast_one] using bound)) j3
  let V := fiveValues (p.t:ℂ) (thetaJet p.t 0 u) (thetaJet p.t 1 u) (thetaJet p.t 2 u) (thetaJet p.t 3 u)
  let B := w.value.output.toBall S.config.prec
  have val : B.Contains ((rectangleShapeExpression b).value V) :=
    w.value.sound S.config _ _ (fiveDyadic_contains ht' e0 e1 e2 e3) _ fx
  cases b
  · have ev : (rectangleShapeExpression false).value V=((Real.pi/p.t:ℝ):ℂ)-thetaLogSecond p.t z := by
      simp [rectangleShapeExpression,BallExpression.value,BallExpression.value_pow,BallExpression.value_div,
        BallExpression.value_sub,thetaLogSecond,thetaQuotient,V,u,fiveValues]
      ring_nf
      exact Or.inl True.intro
    rw [ev] at val
    have h := (re_bounds val).1
    have br : (B.radius:ℝ)<(B.center.re:ℝ) := by exact_mod_cast pos
    change 0<Real.pi/p.t-(thetaLogSecond p.t (((5/8:ℝ):ℂ)+I*y)).re
    have ze : z=((5/8:ℝ):ℂ)+I*y := by norm_num [z,c]
    rw [ze,sub_re,ofReal_re,Rat.cast_sub] at h
    linarith
  · have ev : (rectangleShapeExpression true).value V=thetaLogThird p.t z := by
      simp [rectangleShapeExpression,BallExpression.value,BallExpression.value_pow,BallExpression.value_div,
        BallExpression.value_sub,thetaLogThird,thetaQuotient,V,u,fiveValues]
      ring_nf
      exact Or.inl True.intro
    rw [ev] at val
    have h := (Complex.abs_im_le_norm (thetaLogThird p.t z-B.center.val)).trans val
    change |(thetaLogThird p.t z).im-(B.center.im:ℝ)|≤(B.radius:ℝ) at h
    have br : (B.radius:ℝ)<(B.center.im:ℝ) := by exact_mod_cast pos
    change 0<(thetaLogThird p.t (((1/2:ℝ):ℂ)+I*y)).im
    have ze : z=((1/2:ℝ):ℂ)+I*y := by norm_num [z,c]
    rw [ze] at h
    linarith [(abs_le.mp h).1]

theorem CheckedRectangleShape.sound {b l r} (c : CheckedRectangleShape b l r) :
    ∀ y∈Icc (l:ℝ) r, 0<rectangleEdgeShapeValue b y := by
  induction c with
  | leaf w ok => exact fun _ hy => rectangle_edge_jet_sound w ok hy
  | @join b l m r _ _ a d =>
    intro y hy
    rcases le_total y (m:ℝ) with yl|yr
    · exact a y ⟨hy.1,yl⟩
    · exact d y ⟨yr,hy.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedRectangleShape.sound
