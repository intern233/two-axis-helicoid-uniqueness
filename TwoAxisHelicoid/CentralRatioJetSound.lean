import TwoAxisHelicoid.CentralRatioDerivatives
import TwoAxisHelicoid.CentralArcJetBounds

namespace TwoAxisHelicoid
open Complex Set ComplexBall
attribute [local irreducible] thetaJet

private noncomputable def shiftJetValues (high : Bool) (t : ℝ) (v : ℂ) : ℕ → ℂ
  | 0 => thetaJet t 0 v | 1 => thetaJet t 1 v | 2 => thetaJet t 2 v
  | 3 => if high then thetaJet t 3 v else 0 | _+4 => 0

private theorem centralShiftJets_sound {t a : ℝ} {z : ℂ} {box : DyadicBall} (high plus : Bool) (w : CentralShiftJets)
    (tb : t∈Icc (rootTLower:ℝ) rootTUpper) (ab : a∈Icc (rootALower:ℝ) rootAUpper)
    (inside : (box.toBall slopingFluxAnalyticSetup.config.prec).Contains z) (ok : w.Checks box high plus) :
    let v := (Real.pi:ℂ)*(if plus then z+a else z-a)/2
    ∀ n, ((w.output n).toBall slopingFluxAnalyticSetup.config.prec).Contains (shiftJetValues high t v n) := by
  intro v
  let S := slopingFluxAnalyticSetup
  obtain ⟨arg,yi,sd,j0,j1,j2,j3⟩ := ok
  obtain ⟨lo,q,aval,_⟩ := sloping_flux_root_parameter_enclosures tb ab
  have av := w.argument.sound S.config _ _ (threeDyadic_contains inside aval (DyadicBall.zero_contains _)) _ arg
  have ev : (centralShiftExpression plus).value (threeValues z (a:ℂ) 0)=v := by
    cases plus <;> simp [centralShiftExpression,BallExpression.value,BallExpression.value_sub,v,threeValues] <;> ring
  rw [ev] at av
  have hs := w.seed.sound _ av sd
  have bound := DyadicBall.im_le_one av yi
  have jet (n : ℕ) (hn : n≤4) := central_trace_jet lo q hs bound n hn
  intro n
  rcases n with _ | (_ | (_ | (_ | n)))
  · exact jet 0 (by decide) w.j0 j0
  · exact jet 1 (by decide) w.j1 j1
  · exact jet 2 (by decide) w.j2 j2
  · cases high with
    | false =>
      cases eq : w.j3 with
      | none => simpa [CentralShiftJets.output,eq,shiftJetValues] using DyadicBall.zero_contains S.config.prec
      | some j => simp [eq,optionalThirdCheck] at j3
    | true =>
      cases eq : w.j3 with
      | none => simp [eq,optionalThirdCheck] at j3
      | some j =>
        simp only [eq,optionalThirdCheck] at j3
        simpa [CentralShiftJets.output,eq,shiftJetValues] using jet 3 (by decide) j j3
  · exact DyadicBall.zero_contains _

private theorem centralRatioInputs_contains {prec : ℕ} {c e : ℂ} {bc be : DyadicBall} {m p : ℕ → ℂ} {bm bp : ℕ → DyadicBall}
    (hc : (bc.toBall prec).Contains c) (he : (be.toBall prec).Contains e)
    (hm : ∀ n, ((bm n).toBall prec).Contains (m n)) (hp : ∀ n, ((bp n).toBall prec).Contains (p n)) :
    ∀ n, ((centralRatioInputs bc be bm bp n).toBall prec).Contains (centralRatioInputs c e m p n) := by
  intro n
  rcases n with _ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | n)))))))))
  all_goals first | exact hc | exact he | exact hm _ | exact hp _

noncomputable def centralRatioJetMargin (high : Bool) : ℝ :=
  (Real.pi/2)^(if high then 3 else 2 : ℕ)/1024

theorem centralRatioJetMargin_pos (high : Bool) : 0<centralRatioJetMargin high := by
  unfold centralRatioJetMargin
  positivity

private theorem central_jet_program_ignores_unused (high : Bool) (t : ℝ) (c e A B : ℂ) :
    jetProgramValue (centralRatioInputs c e (shiftJetValues high t A) (shiftJetValues high t B)) (centralRatioProgram high) =
      jetProgramValue (centralRatioInputs c e (fun n => thetaJet t n A) (fun n => thetaJet t n B)) (centralRatioProgram high) := by
  cases high <;> rfl

private theorem central_ratio_cell_sound {t a : ℝ} {z : ℂ} {high vertical : Bool} {edge l r : ℚ} (w : CentralRatioJetTrace)
    (tb : t∈Icc (rootTLower:ℝ) rootTUpper) (ab : a∈Icc (rootALower:ℝ) rootAUpper) (ht : 0<t)
    (regular : z+a∉(rhombicPeriodPair t ht).lattice) (inside : (centralBandEdgeBall vertical edge l r).Contains z)
    (check : w.Checks high vertical edge l r) :
    centralRatioJetMargin high<(iteratedDeriv (if high then 3 else 2) (centralPhaseThetaRatio t a) z).re := by
  let S := slopingFluxAnalyticSetup
  let c : ℂ := ((4*(1-a)/t:ℝ):ℂ)
  let K := (Real.pi/2:ℂ)
  let E := exp (K*c*z)
  let F := centralPhaseThetaRatio t a
  let A := (Real.pi:ℂ)*(z-a)/2
  let B := (Real.pi:ℂ)*(z+a)/2
  let n := if high then 3 else 2
  obtain ⟨box,ex,jm,jp,prog,pos⟩ := check
  have bz := coarsen_contains inside box
  obtain ⟨_,_,aval,_⟩ := sloping_flux_root_parameter_enclosures tb ab
  have sc := centralRatioSlopeTrace.sound S.config _ _ (threeDyadic_contains (central_trace_height_parameter tb) aval
    (DyadicBall.zero_contains _)) _ centralRatioSlopeTrace_valid
  have boundC : (centralRatioSlopeTrace.output.toBall S.config.prec).Contains c := by
    convert sc using 1
    simp [centralRatioSlopeExpression,BallExpression.value,BallExpression.value_div,BallExpression.value_sub,threeValues,c]
  have ee := w.exponential.sound S.config _ _ (threeDyadic_contains boundC bz (DyadicBall.zero_contains _)) _ ex
  have expo : (w.exponential.output.toBall S.config.prec).Contains E := by
    convert ee using 1
    simp only [centralRatioExpExpression,BallExpression.value,BallExpression.value_rational,threeValues,E,K]
    push_cast
    ring_nf
  have mm := centralShiftJets_sound high false w.minus tb ab bz jm
  have pp := centralShiftJets_sound high true w.plus tb ab bz jp
  have hv := jet_program_sound (centralRatioInputs_contains boundC expo mm pp) prog
  let out := (jetProgramOutput centralRatioSlopeTrace.output w.steps).toBall S.config.prec
  change out.Contains (jetProgramValue (centralRatioInputs c E (shiftJetValues high t A) (shiftJetValues high t B)) (centralRatioProgram high)) at hv
  rw [central_jet_program_ignores_unused] at hv
  have value : out.Contains (iteratedDeriv n F z/K^n) := by
    rw [← central_ratio_derivative_from_jets ht regular high]
    exact hv
  have fraction : (1/1024:ℝ)<(iteratedDeriv n F z/K^n).re := by
    have margin : (1/1024:ℝ)<((out.center.re-out.radius:ℚ):ℝ) := calc
      (1/1024:ℝ) = ((1/1024:ℚ):ℝ) := by norm_num
      _ < _ := Rat.cast_lt.mpr pos
    exact margin.trans_le (re_bounds value).1
  have kp : 0<(Real.pi/2)^n := pow_pos (by positivity) _
  have cast : K^n=(((Real.pi/2)^n:ℝ):ℂ) := by push_cast; rfl
  rw [cast,div_ofReal_re] at fraction
  change (Real.pi/2)^n/1024<(iteratedDeriv n F z).re
  linarith [(lt_div_iff₀ kp).mp fraction]

noncomputable def centralRatioEdgePoint (v : Bool) (edge x : ℝ) : ℂ := if v then (edge:ℂ)+I*x else (x:ℂ)+I*edge

theorem CheckedCentralRatioJets.sound {h v e l r} (c : CheckedCentralRatioJets h v e l r)
    {t a : ℝ} (tb : t∈Icc (rootTLower:ℝ) rootTUpper) (ab : a∈Icc (rootALower:ℝ) rootAUpper) (ht : 0<t) :
    ∀ x∈Icc (l:ℝ) r, let z := centralRatioEdgePoint v e x
      z+a∉(rhombicPeriodPair t ht).lattice →
        centralRatioJetMargin h<(iteratedDeriv (if h then 3 else 2) (centralPhaseThetaRatio t a) z).re := by
  induction c with
  | @leaf w h v e l r ok =>
    intro x hx z nz
    apply central_ratio_cell_sound w tb ab ht nz _ ok
    cases v
    · have hit := rectangle_center_disk_contains hx (show (e:ℝ)∈Icc (e:ℝ) e from ⟨le_rfl,le_rfl⟩)
      simpa [centralBandEdgeBall,centralRatioEdgePoint,z] using hit
    · have hit := rectangle_center_disk_contains (show (e:ℝ)∈Icc (e:ℝ) e from ⟨le_rfl,le_rfl⟩) hx
      simpa [centralBandEdgeBall,centralRatioEdgePoint,z] using hit
  | @join h v e l m r _ _ p q =>
    intro x hx
    rcases le_total x (m:ℝ) with a|a
    · exact p x ⟨hx.1,a⟩
    · exact q x ⟨a,hx.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedCentralRatioJets.sound
