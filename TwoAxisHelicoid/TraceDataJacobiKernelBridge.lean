import TwoAxisHelicoid.TraceDataJacobiKernel
import TwoAxisHelicoid.TraceDataJacobiBridge
import TwoAxisHelicoid.TraceDataDerivativeBridge
import TwoAxisHelicoid.DyadicJacobiKernel

namespace TwoAxisHelicoid.TraceData
set_option maxHeartbeats 800000

theorem jacobi_expression_valid_of_check (cfg : BallConfig) (bs : List DyadicBall)
    (e : BallExpression) (w : DyadicExpressionTrace)
    (hw : w.check cfg (dyadicInputList bs) e = true) :
    w.interpret.Valid cfg.interpret
      (TwoAxisHelicoid.dyadicInputList (bs.map DyadicBall.interpret)) e.interpret := by
  apply (TwoAxisHelicoid.DyadicExpressionTrace.check_eq_true _ _ _ _).mp
  rw [← interpret_dyadicInputList, DyadicExpressionTrace.interpret_check]
  exact hw

theorem interpret_jacobiNormalizationExpression :
    jacobiNormalizationExpression.interpret = TwoAxisHelicoid.jacobiNormalizationExpression := rfl

theorem interpret_jacobiPhysicalXExpression (right : Bool) :
    (jacobiPhysicalXExpression right).interpret = TwoAxisHelicoid.jacobiPhysicalXExpression right := by
  cases right <;> rfl

theorem interpret_jacobiKernelResultExpression (right : Bool) :
    (jacobiKernelResultExpression right).interpret = TwoAxisHelicoid.jacobiKernelResultExpression right := by
  cases right <;> rfl

namespace DyadicJacobiBaseParameters
def interpret (p : DyadicJacobiBaseParameters) : TwoAxisHelicoid.DyadicJacobiBaseParameters :=
  ⟨p.height.interpret,p.abscissa.interpret,p.q.interpret,p.r.interpret,
    p.kappa.interpret,p.beta.interpret⟩

theorem valid_of_valid (cfg : BallConfig) (p : DyadicJacobiBaseParameters)
    (hp : p.Valid cfg) : p.interpret.Valid cfg.interpret := by
  rcases hp with ⟨hq,hr,hk,hb⟩
  refine ⟨?_,?_,?_,?_⟩
  · exact jacobi_expression_valid_of_check cfg p.inputs jacobiDualNomeExpression p.q hq
  · exact jacobi_expression_valid_of_check cfg p.inputs jacobiDualRExpression p.r hr
  · exact jacobi_expression_valid_of_check cfg p.inputs jacobiDualKappaExpression p.kappa hk
  · exact jacobi_expression_valid_of_check cfg p.inputs jacobiDualBetaExpression p.beta hb
end DyadicJacobiBaseParameters

namespace DyadicJacobiParameters
def interpret (p : DyadicJacobiParameters) : TwoAxisHelicoid.DyadicJacobiParameters :=
  ⟨p.base.interpret,p.qr.interpret,p.p0.interpret,p.pr.interpret,
    p.pinvr.interpret,p.normalization.interpret⟩

theorem valid_of_valid (cfg : BallConfig) (err : ℕ) (p : DyadicJacobiParameters)
    (hp : p.Valid cfg err) : p.interpret.Valid cfg.interpret err := by
  rcases hp with ⟨hb,hqr,h0,h1,h2,hn⟩
  simp only [TwoAxisHelicoid.DyadicJacobiParameters.Valid, interpret,
    DyadicJacobiBaseParameters.interpret, DyadicExpressionTrace.interpret_output,
    BallConfig.interpret_prec]
  refine ⟨p.base.valid_of_valid cfg hb, ?_, ?_, ?_, ?_, ?_⟩
  · exact (DyadicBall.interpret_ChecksMul _ _ _ _).mpr hqr
  · exact (DyadicJacobiProductTrace.interpret_valid _ _ _ _ _).mpr h0
  · exact (DyadicJacobiProductTrace.interpret_valid _ _ _ _ _).mpr h1
  · simpa only [DyadicBall.interpret_neg] using
      (DyadicJacobiProductTrace.interpret_valid cfg.prec err p.base.q.output p.base.beta.output.neg p.pinvr).mpr h2
  · have h := jacobi_expression_valid_of_check cfg p.inputs jacobiNormalizationExpression p.normalization hn
    rw [interpret_jacobiNormalizationExpression] at h
    simpa only [TwoAxisHelicoid.DyadicJacobiParameters.inputs, inputs, List.map_cons, List.map_nil,
      DyadicJacobiProductTrace.interpret, DyadicExpressionTrace.interpret_output,
      DyadicJacobiBaseParameters.interpret] using h
end DyadicJacobiParameters

namespace DyadicJacobiKernelTrace
def interpret (w : DyadicJacobiKernelTrace) : TwoAxisHelicoid.DyadicJacobiKernelTrace :=
  ⟨w.qx.interpret,w.qinvx.interpret,w.qrx.interpret,w.qinvrx.interpret,w.x.interpret,w.rx.interpret,w.pA.interpret,w.pB.interpret,w.pC.interpret,w.pD.interpret,w.eA.interpret,w.eB.interpret,w.result.interpret⟩

theorem interpret_output (w : DyadicJacobiKernelTrace) :
    w.interpret.output = w.output.interpret := DyadicExpressionTrace.interpret_output _

theorem valid_of_valid (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (z : DyadicBall) (w : DyadicJacobiKernelTrace)
    (hw : w.Valid cfg productError eulerError right p z) :
    w.interpret.Valid cfg.interpret productError eulerError right p.interpret z.interpret := by
  rcases hw with ⟨hA,hB,hC,hD,hX,hRX,hPA,hPB,hPC,hPD,hEA,hEB,hR⟩
  simp only [TwoAxisHelicoid.DyadicJacobiKernelTrace.Valid, interpret, DyadicJacobiParameters.interpret,
    DyadicJacobiBaseParameters.interpret, DyadicExpressionTrace.interpret_output,
    BallConfig.interpret_prec]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact jacobi_expression_valid_of_check cfg [p.base.height,p.base.abscissa,z] jacobiQXExpression w.qx hA
  · exact jacobi_expression_valid_of_check cfg [p.base.height,p.base.abscissa,z] jacobiQInvXExpression w.qinvx hB
  · exact jacobi_expression_valid_of_check cfg [p.base.height,p.base.abscissa,z] jacobiQRXExpression w.qrx hC
  · exact jacobi_expression_valid_of_check cfg [p.base.height,p.base.abscissa,z] jacobiQInvRXExpression w.qinvrx hD
  · have h := jacobi_expression_valid_of_check cfg [p.base.height,p.base.abscissa,z]
      (jacobiPhysicalXExpression right) w.x hX
    rw [interpret_jacobiPhysicalXExpression] at h
    exact h
  · exact jacobi_expression_valid_of_check cfg [p.base.height,p.base.abscissa,z]
      jacobiPhysicalRXExpression w.rx hRX
  · exact (DyadicJacobiProductTrace.interpret_valid _ _ _ _ _).mpr hPA
  · exact (DyadicJacobiProductTrace.interpret_valid _ _ _ _ _).mpr hPB
  · exact (DyadicJacobiProductTrace.interpret_valid _ _ _ _ _).mpr hPC
  · exact (DyadicJacobiProductTrace.interpret_valid _ _ _ _ _).mpr hPD
  · exact (DyadicJacobiEulerTrace.interpret_valid _ _ _ _ _).mpr hEA
  · exact (DyadicJacobiEulerTrace.interpret_valid _ _ _ _ _).mpr hEB
  · have h := jacobi_expression_valid_of_check cfg (w.inputs p)
      (jacobiKernelResultExpression right) w.result hR
    rw [interpret_jacobiKernelResultExpression] at h
    simpa only [TwoAxisHelicoid.DyadicJacobiKernelTrace.inputs, inputs, List.map_cons, List.map_nil,
      DyadicJacobiProductTrace.interpret, DyadicJacobiEulerTrace.interpret,
      DyadicExpressionTrace.interpret_output,
      DyadicJacobiBaseParameters.interpret] using h
end DyadicJacobiKernelTrace
end TwoAxisHelicoid.TraceData

#print axioms TwoAxisHelicoid.TraceData.DyadicJacobiKernelTrace.valid_of_valid

