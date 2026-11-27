import TwoAxisHelicoid.TraceDataJacobiChordCell
import TwoAxisHelicoid.TraceDataJacobiCellBridge
import TwoAxisHelicoid.JacobiChordCell

namespace TwoAxisHelicoid.TraceData
set_option maxHeartbeats 1000000

theorem chord_expression_check_of_check (cfg : BallConfig) (bs : List DyadicBall)
    (e : BallExpression) (w : DyadicExpressionTrace)
    (hw : w.check cfg (dyadicInputList bs) e = true) :
    w.interpret.check cfg.interpret
      (TwoAxisHelicoid.dyadicInputList (bs.map DyadicBall.interpret)) e.interpret = true :=
  (TwoAxisHelicoid.DyadicExpressionTrace.check_eq_true _ _ _ _).mpr
    (jacobi_expression_valid_of_check cfg bs e w hw)

theorem interpret_jacobiChordQXExpression : jacobiChordQXExpression.interpret = TwoAxisHelicoid.jacobiChordQXExpression := rfl

theorem interpret_jacobiChordQInvXExpression : jacobiChordQInvXExpression.interpret = TwoAxisHelicoid.jacobiChordQInvXExpression := rfl

theorem interpret_jacobiChordQRXExpression : jacobiChordQRXExpression.interpret = TwoAxisHelicoid.jacobiChordQRXExpression := rfl

theorem interpret_jacobiChordQInvRXExpression : jacobiChordQInvRXExpression.interpret = TwoAxisHelicoid.jacobiChordQInvRXExpression := rfl

theorem interpret_jacobiChordRXExpression : jacobiChordRXExpression.interpret = TwoAxisHelicoid.jacobiChordRXExpression := rfl

theorem interpret_jacobiChordResultExpression : jacobiChordResultExpression.interpret = TwoAxisHelicoid.jacobiChordResultExpression := rfl

namespace DyadicJacobiChordParameters

def interpret (p : DyadicJacobiChordParameters) : TwoAxisHelicoid.DyadicJacobiChordParameters :=
  ⟨p.base.interpret,p.nomeHalf.interpret,p.chordH.interpret,p.chordK.interpret⟩

theorem valid_of_valid (cfg : BallConfig) (err : ℕ) (p : DyadicJacobiChordParameters)
    (hp : p.Valid cfg err) : p.interpret.Valid cfg.interpret err := by
  rcases hp with ⟨hb,hn,hh,hk⟩
  simp only [TwoAxisHelicoid.DyadicJacobiChordParameters.Valid, interpret,
    DyadicJacobiParameters.interpret, DyadicJacobiBaseParameters.interpret,
    DyadicExpressionTrace.interpret_output]
  refine ⟨p.base.valid_of_valid cfg err hb, ?_, ?_, ?_⟩
  · exact chord_expression_check_of_check cfg [p.base.base.height] jacobiChordNomeExpression p.nomeHalf hn
  · exact chord_expression_check_of_check cfg [p.nomeHalf.output] jacobiChordHExpression p.chordH hh
  · exact chord_expression_check_of_check cfg [p.nomeHalf.output] jacobiChordKExpression p.chordK hk

end DyadicJacobiChordParameters

namespace DyadicJacobiChordTrace

def interpret (w : DyadicJacobiChordTrace) : TwoAxisHelicoid.DyadicJacobiChordTrace :=
  ⟨w.u.interpret,w.uMinusI.interpret,w.uPlusI.interpret,w.x.interpret,w.invx.interpret,w.qx.interpret,w.qinvx.interpret,w.qrx.interpret,w.qinvrx.interpret,w.rx.interpret,w.pA.interpret,w.pB.interpret,w.pC.interpret,w.pD.interpret,w.eA.interpret,w.eB.interpret,w.result.interpret⟩

theorem interpret_output (w : DyadicJacobiChordTrace) :
    w.interpret.output = w.output.interpret := DyadicExpressionTrace.interpret_output _

theorem valid_of_valid (cfg : BallConfig) (productError eulerError : ℕ)
    (p : DyadicJacobiChordParameters) (z : DyadicBall) (w : DyadicJacobiChordTrace)
    (hw : w.Valid cfg productError eulerError p z) :
    w.interpret.Valid cfg.interpret productError eulerError p.interpret z.interpret := by
  rcases hw with ⟨hu,hum,hum0,hup,hup0,hx,hix,hqx,hqix,hqrx,hqirx,hrx,
    hpA,hpB,hpC,hpD,heA,heB,hresult⟩
  simp only [TwoAxisHelicoid.DyadicJacobiChordTrace.Valid, interpret, DyadicJacobiChordParameters.interpret,
    DyadicJacobiParameters.interpret, DyadicJacobiBaseParameters.interpret,
    DyadicExpressionTrace.interpret_output, BallConfig.interpret_prec]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact chord_expression_check_of_check cfg [p.chordH.output,p.chordK.output,z]
      jacobiChordUExpression w.u hu
  · exact chord_expression_check_of_check cfg [w.u.output] jacobiChordMinusIExpression w.uMinusI hum
  · simpa only [DyadicBall.interpret_lower] using hum0
  · exact chord_expression_check_of_check cfg [w.u.output] jacobiChordPlusIExpression w.uPlusI hup
  · simpa only [DyadicBall.interpret_lower] using hup0
  · exact chord_expression_check_of_check cfg [w.u.output] jacobiChordXExpression w.x hx
  · exact chord_expression_check_of_check cfg [w.u.output] jacobiChordInvXExpression w.invx hix
  · have h := chord_expression_check_of_check cfg (w.seedInputs p) jacobiChordQXExpression w.qx hqx
    rw [interpret_jacobiChordQXExpression] at h
    simpa only [TwoAxisHelicoid.DyadicJacobiChordTrace.seedInputs, seedInputs, List.map_cons, List.map_nil,
      DyadicExpressionTrace.interpret_output, DyadicJacobiChordParameters.interpret,
      DyadicJacobiParameters.interpret, DyadicJacobiBaseParameters.interpret] using h
  · have h := chord_expression_check_of_check cfg (w.seedInputs p) jacobiChordQInvXExpression w.qinvx hqix
    rw [interpret_jacobiChordQInvXExpression] at h
    simpa only [TwoAxisHelicoid.DyadicJacobiChordTrace.seedInputs, seedInputs, List.map_cons, List.map_nil,
      DyadicExpressionTrace.interpret_output, DyadicJacobiChordParameters.interpret,
      DyadicJacobiParameters.interpret, DyadicJacobiBaseParameters.interpret] using h
  · have h := chord_expression_check_of_check cfg (w.seedInputs p) jacobiChordQRXExpression w.qrx hqrx
    rw [interpret_jacobiChordQRXExpression] at h
    simpa only [TwoAxisHelicoid.DyadicJacobiChordTrace.seedInputs, seedInputs, List.map_cons, List.map_nil,
      DyadicExpressionTrace.interpret_output, DyadicJacobiChordParameters.interpret,
      DyadicJacobiParameters.interpret, DyadicJacobiBaseParameters.interpret] using h
  · have h := chord_expression_check_of_check cfg (w.seedInputs p) jacobiChordQInvRXExpression w.qinvrx hqirx
    rw [interpret_jacobiChordQInvRXExpression] at h
    simpa only [TwoAxisHelicoid.DyadicJacobiChordTrace.seedInputs, seedInputs, List.map_cons, List.map_nil,
      DyadicExpressionTrace.interpret_output, DyadicJacobiChordParameters.interpret,
      DyadicJacobiParameters.interpret, DyadicJacobiBaseParameters.interpret] using h
  · have h := chord_expression_check_of_check cfg (w.seedInputs p) jacobiChordRXExpression w.rx hrx
    rw [interpret_jacobiChordRXExpression] at h
    simpa only [TwoAxisHelicoid.DyadicJacobiChordTrace.seedInputs, seedInputs, List.map_cons, List.map_nil,
      DyadicExpressionTrace.interpret_output, DyadicJacobiChordParameters.interpret,
      DyadicJacobiParameters.interpret, DyadicJacobiBaseParameters.interpret] using h
  · exact (DyadicJacobiProductTrace.interpret_valid _ _ _ _ _).mpr hpA
  · exact (DyadicJacobiProductTrace.interpret_valid _ _ _ _ _).mpr hpB
  · exact (DyadicJacobiProductTrace.interpret_valid _ _ _ _ _).mpr hpC
  · exact (DyadicJacobiProductTrace.interpret_valid _ _ _ _ _).mpr hpD
  · exact (DyadicJacobiEulerTrace.interpret_valid _ _ _ _ _).mpr heA
  · exact (DyadicJacobiEulerTrace.interpret_valid _ _ _ _ _).mpr heB
  · have h := chord_expression_check_of_check cfg (w.inputs p) jacobiChordResultExpression w.result hresult
    rw [interpret_jacobiChordResultExpression] at h
    simpa only [TwoAxisHelicoid.DyadicJacobiChordTrace.inputs, inputs, List.map_cons, List.map_nil,
      DyadicJacobiProductTrace.interpret, DyadicJacobiEulerTrace.interpret,
      DyadicExpressionTrace.interpret_output, DyadicJacobiChordParameters.interpret,
      DyadicJacobiParameters.interpret, DyadicJacobiBaseParameters.interpret] using h

end DyadicJacobiChordTrace

namespace JacobiChordRangeNode

def interpret (w : JacobiChordRangeNode) : TwoAxisHelicoid.JacobiChordRangeNode :=
  ⟨w.point.interpret,w.function.interpret,w.weighted.interpret⟩

theorem valid_of_valid (cfg : BallConfig) (productError eulerError : ℕ)
    (p : DyadicJacobiChordParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : JacobiChordRangeNode) (hw : w.Valid cfg productError eulerError p center h node weight) :
    w.interpret.Valid cfg.interpret productError eulerError p.interpret center.interpret h node weight := by
  rcases hw with ⟨hz,hf,hw⟩
  refine ⟨?_, w.function.valid_of_valid cfg productError eulerError p w.point hf, ?_⟩
  · simpa only [interpret, TwoAxisHelicoid.ComplexBall.coarsens, TwoAxisHelicoid.QComplex.absUpper,
      TwoAxisHelicoid.QComplex.sub, TwoAxisHelicoid.QComplex.add, TwoAxisHelicoid.QComplex.neg, TwoAxisHelicoid.DyadicBall.toBall,
      DyadicBall.interpret, TwoAxisHelicoid.ComplexBall.add, TwoAxisHelicoid.ComplexBall.rational,
      TwoAxisHelicoid.ComplexBall.point, TwoAxisHelicoid.QComplex.ofRat, ComplexBall.coarsens,
      QComplex.absUpper, QComplex.sub, QComplex.add, QComplex.neg, DyadicBall.toBall,
      ComplexBall.add, ComplexBall.rational, ComplexBall.point, QComplex.ofRat,
      rat_abs_eq, BallConfig.interpret_prec, DyadicBall.denominator,
      TwoAxisHelicoid.DyadicBall.denominator] using hz
  · have he := chord_expression_check_of_check cfg [w.function.output]
      (.mul (.rational weight) (.input 0)) w.weighted hw
    have hexpr : (BallExpression.mul (.rational weight) (.input 0)).interpret =
        TwoAxisHelicoid.BallExpression.mul (.rational weight) (.input 0) := rfl
    rw [hexpr] at he
    simpa only [interpret, DyadicJacobiChordTrace.interpret_output, List.map_cons,
      List.map_nil] using he

end JacobiChordRangeNode

namespace JacobiChordRangeCell

def interpret {K : ℕ} (w : JacobiChordRangeCell K) : TwoAxisHelicoid.JacobiChordRangeCell K :=
  ⟨w.center.interpret,w.disk.interpret,w.diskFunction.interpret,
    fun i => (w.nodes i).interpret,w.output.interpret⟩

end JacobiChordRangeCell
end TwoAxisHelicoid.TraceData

#print axioms TwoAxisHelicoid.TraceData.JacobiChordRangeNode.valid_of_valid
