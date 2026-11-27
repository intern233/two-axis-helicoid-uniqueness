import TwoAxisHelicoid.HighLevelThetaEdgeData
import TwoAxisHelicoid.CentralArcJetBounds
import TwoAxisHelicoid.CentralLevelThetaFactor
import TwoAxisHelicoid.CentralBandEdgeSound

namespace TwoAxisHelicoid
open Complex Set ComplexBall
attribute [local irreducible] thetaJet thetaScaledJet

theorem ShiftedThetaValueTrace.encloses {t a : ℝ} {z : ℂ} {box : DyadicBall}
    (plus : Bool) (w : ShiftedThetaValueTrace) (tb : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ab : a∈Icc (rootALower:ℝ) rootAUpper) (bz : (box.toBall slopingFluxAnalyticSetup.config.prec).Contains z)
    (checks : w.Checks box plus) :
    (w.value.output.toBall slopingFluxAnalyticSetup.config.prec).Contains
      (thetaScaledJet t 0 (if plus then z+a else z-a)) := by
  let S := slopingFluxAnalyticSetup
  let v := (Real.pi:ℂ)*(if plus then z+a else z-a)/2
  obtain ⟨arg,yi,sd,j⟩ := checks
  obtain ⟨lo,q,aval,_⟩ := sloping_flux_root_parameter_enclosures tb ab
  have av := w.argument.sound S.config _ _ (threeDyadic_contains bz aval (DyadicBall.zero_contains _)) _ arg
  have ev : (centralShiftExpression plus).value (threeValues z (a:ℂ) 0)=v := by
    cases plus <;> simp [centralShiftExpression,BallExpression.value,BallExpression.value_sub,v,threeValues] <;> ring
  rw [ev] at av
  have jet := central_trace_jet lo q (w.seed.sound _ av sd) (DyadicBall.im_le_one av yi) 0 (by decide) w.value j
  have eq : (Real.pi/2:ℂ)*(if plus then z+a else z-a)=v := by dsimp [v]; ring
  simpa [thetaScaledJet,eq] using jet


/-- The arithmetic trace for the meromorphic quotient, independent of
the linear functional that will be used to separate a horizontal level. -/
def HighLevelRatioTrace.Valid (w : HighLevelRatioTrace) : Prop :=
  let S := slopingFluxAnalyticSetup
  w.exponential.Valid S.config (threeDyadic centralRatioSlopeTrace.output w.box .zero) centralRatioExpExpression ∧
    w.minus.Checks w.box false ∧ w.plus.Checks w.box true ∧
    w.value.Valid S.config (threeDyadic w.exponential.output w.minus.value.output w.plus.value.output)
      (.div (.mul (.input 0) (.input 1)) (.input 2))

instance (w : HighLevelRatioTrace) : Decidable w.Valid := by
  unfold HighLevelRatioTrace.Valid
  infer_instance

theorem HighLevelRatioTrace.encloses {t a : ℝ} {z : ℂ} (w : HighLevelRatioTrace)
    (tb : t∈Icc (rootTLower:ℝ) rootTUpper) (ab : a∈Icc (rootALower:ℝ) rootAUpper)
    (bz : (w.box.toBall slopingFluxAnalyticSetup.config.prec).Contains z) (checks : w.Valid) :
    (w.value.output.toBall slopingFluxAnalyticSetup.config.prec).Contains (centralPhaseThetaRatio t a z) := by
  let S := slopingFluxAnalyticSetup
  let c : ℂ := ((4*(1-a)/t:ℝ):ℂ)
  let K := (Real.pi/2:ℂ)
  obtain ⟨ex,jm,jp,final⟩ := checks
  obtain ⟨_,_,aval,_⟩ := sloping_flux_root_parameter_enclosures tb ab
  have sc := centralRatioSlopeTrace.sound S.config _ _ (threeDyadic_contains (central_trace_height_parameter tb) aval
    (DyadicBall.zero_contains _)) _ centralRatioSlopeTrace_valid
  have bc : (centralRatioSlopeTrace.output.toBall S.config.prec).Contains c := by
    convert sc using 1
    simp [centralRatioSlopeExpression,BallExpression.value,BallExpression.value_div,BallExpression.value_sub,threeValues,c]
  have ee := w.exponential.sound S.config _ _ (threeDyadic_contains bc bz (DyadicBall.zero_contains _)) _ ex
  have ev : (w.exponential.output.toBall S.config.prec).Contains (exp (K*c*z)) := by
    convert ee using 1
    simp only [centralRatioExpExpression,BallExpression.value,BallExpression.value_rational,threeValues,K]
    push_cast
    ring_nf
  have minus := ShiftedThetaValueTrace.encloses false w.minus tb ab bz jm
  have plus := ShiftedThetaValueTrace.encloses true w.plus tb ab bz jp
  have b := w.value.sound S.config _ _ (threeDyadic_contains ev minus plus) _ final
  change (w.value.output.toBall S.config.prec).Contains
    ((exp (K*c*z)*thetaScaledJet t 0 (z-a))/thetaScaledJet t 0 (z+a)) at b
  have k : K*c=((2*(1-a)*Real.pi/t:ℝ):ℂ) := by dsimp [K,c]; push_cast; ring
  rw [k,mul_div_assoc] at b
  exact b

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HighLevelRatioTrace.encloses
