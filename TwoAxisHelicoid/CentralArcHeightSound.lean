import TwoAxisHelicoid.CentralArcJetBounds
import TwoAxisHelicoid.CentralArcHeightData

namespace TwoAxisHelicoid
open Complex Set ComplexBall
attribute [local irreducible] thetaJet

noncomputable def centralSweepAbscissa (k : CentralHeightSweep) (a : ℝ) : ℝ :=
  if k.leftSide then 1/2 else a

noncomputable def centralSweepValue (k : CentralHeightSweep) (t a y : ℝ) : ℝ :=
  let z := (centralSweepAbscissa k a:ℂ)+I*y
  let v := Real.pi/t-(thetaLogSecond t z).re
  match k with
  | .leftEarly => -v
  | .leftLate | .saddleSlope => v
  | .saddleThird => (thetaLogFourth t z).re

private theorem central_sweep_inside {a y : ℝ} {l r : ℚ} (k : CentralHeightSweep)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hy : y∈Icc (l:ℝ) r) :
    (centralHeightSweepDisk k l r).Contains ((centralSweepAbscissa k a:ℂ)+I*y) := by
  unfold centralHeightSweepDisk centralSweepAbscissa
  split
  · apply rectangle_center_disk_contains _ hy
    norm_num
  · exact rectangle_center_disk_contains ha hy

private theorem CentralArcSlopeTrace.sound {t a y : ℝ} {k : CentralHeightSweep} {l r : ℚ}
    (ht : t∈Icc (rootTLower:ℝ) rootTUpper) (ha : a∈Icc (rootALower:ℝ) rootAUpper)
    (hy : y∈Icc (l:ℝ) r) (w : CentralArcSlopeTrace) (ok : w.Checks k l r) : 0<centralSweepValue k t a y := by
  let S := slopingFluxAnalyticSetup
  let z := (centralSweepAbscissa k a:ℂ)+I*y
  let u := Real.pi*z/2
  obtain ⟨nk,box,arg,yi,sd,j0,j1,j2,hv,pos⟩ := ok
  have inside := coarsen_contains (central_sweep_inside k ha hy) box
  have av := w.argument.sound S.config _ _ (threeDyadic_contains inside (DyadicBall.zero_contains _) (DyadicBall.zero_contains _)) _ arg
  rw [value_thetaArgumentExpression] at av
  have seed := w.seed.sound S.config av sd
  have bd := DyadicBall.im_le_one av yi
  obtain ⟨lo,q,_⟩ := sloping_flux_root_parameter_enclosures ht ha
  have j (n : ℕ) (hn : n≤4) := central_trace_jet lo q seed bd n hn
  have h0 := j 0 (by decide) w.j0 j0
  have h1 := j 1 (by decide) w.j1 j1
  have h2 := j 2 (by decide) w.j2 j2
  let V := fiveValues (t:ℂ) (thetaJet t 0 u) (thetaJet t 1 u) (thetaJet t 2 u) 0
  let B := w.value.output.toBall S.config.prec
  have v : B.Contains ((rectangleShapeExpression false).value V) :=
    w.value.sound _ _ _ (fiveDyadic_contains (central_trace_height_parameter ht) h0 h1 h2 (DyadicBall.zero_contains _)) _ hv
  have e : (rectangleShapeExpression false).value V=((Real.pi/t:ℝ):ℂ)-thetaLogSecond t z := by
    simp [rectangleShapeExpression,BallExpression.value,BallExpression.value_pow,BallExpression.value_div,
      BallExpression.value_sub,thetaLogSecond,thetaQuotient,V,u,fiveValues]
    ring_nf
    exact Or.inl True.intro
  rw [e] at v
  obtain ⟨low,high⟩ := re_bounds v
  simp only [sub_re,ofReal_re,Rat.cast_sub,Rat.cast_add] at low high
  cases k with
  | leftEarly =>
    have p : (B.radius:ℝ)< -(B.center.re:ℝ) := by exact_mod_cast pos
    change 0< -(Real.pi/t-(thetaLogSecond t z).re)
    linarith
  | saddleThird => exact False.elim (nk rfl)
  | leftLate | saddleSlope =>
    have p : (B.radius:ℝ)<(B.center.re:ℝ) := by exact_mod_cast pos
    change 0<Real.pi/t-(thetaLogSecond t z).re
    linarith

private theorem CentralArcFourthTrace.sound {t a y : ℝ} {l r : ℚ}
    (ht : t∈Icc (rootTLower:ℝ) rootTUpper) (ha : a∈Icc (rootALower:ℝ) rootAUpper)
    (hy : y∈Icc (l:ℝ) r) (w : CentralArcFourthTrace) (ok : w.Checks l r) :
    0<centralSweepValue .saddleThird t a y := by
  let S := slopingFluxAnalyticSetup
  let z := (a:ℂ)+I*y
  let u := Real.pi*z/2
  obtain ⟨box,arg,yi,sd,j0,j1,j2,j3,j4,hv,pos⟩ := ok
  have inside := coarsen_contains (central_sweep_inside .saddleThird ha hy) box
  have av := w.argument.sound S.config _ _ (threeDyadic_contains inside (DyadicBall.zero_contains _) (DyadicBall.zero_contains _)) _ arg
  rw [value_thetaArgumentExpression] at av
  have seed := w.seed.sound S.config av sd
  have bd := DyadicBall.im_le_one av yi
  obtain ⟨lo,q,_⟩ := sloping_flux_root_parameter_enclosures ht ha
  have j (n : ℕ) (hn : n≤4) := central_trace_jet lo q seed bd n hn
  let V := fiveValues (thetaJet t 0 u) (thetaJet t 1 u) (thetaJet t 2 u) (thetaJet t 3 u) (thetaJet t 4 u)
  let B := w.value.output.toBall S.config.prec
  have v : B.Contains (centralFourthExpression.value V) :=
    w.value.sound _ _ _ (fiveDyadic_contains (j 0 (by decide) w.j0 j0) (j 1 (by decide) w.j1 j1)
      (j 2 (by decide) w.j2 j2) (j 3 (by decide) w.j3 j3) (j 4 (by decide) w.j4 j4)) _ hv
  have e : centralFourthExpression.value V=thetaLogFourth t z := by
    simp [centralFourthExpression,BallExpression.value,BallExpression.value_pow,BallExpression.value_div,
      BallExpression.value_sub,thetaLogFourth,thetaQuotient,V,u,fiveValues]
    ring_nf
    exact Or.inl True.intro
  have p : (B.radius:ℝ)<(B.center.re:ℝ) := by exact_mod_cast pos
  rw [e] at v
  have bound := (re_bounds v).1
  rw [Rat.cast_sub] at bound
  change 0<(thetaLogFourth t z).re
  linarith

theorem CheckedCentralHeightSweep.sound {k l r} (checks : CheckedCentralHeightSweep k l r)
    {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper) (ha : a∈Icc (rootALower:ℝ) rootAUpper) :
    ∀ y∈Icc (l:ℝ) r, 0<centralSweepValue k t a y := by
  induction checks with
  | slope w ok => exact fun _ hy => w.sound ht ha hy ok
  | third w ok => exact fun _ hy => w.sound ht ha hy ok
  | @join k l m r _ _ left right =>
    intro y hy
    rcases le_total y (m:ℝ) with low|high
    · exact left y ⟨hy.1,low⟩
    · exact right y ⟨high,hy.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedCentralHeightSweep.sound
