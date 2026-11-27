import TwoAxisHelicoid.TraceDataJacobiFast
import TwoAxisHelicoid.TraceDataJacobiCellBridge
import TwoAxisHelicoid.JacobiFastRangeCell
namespace TwoAxisHelicoid.TraceData
set_option maxHeartbeats 800000
theorem interpret_jacobiFastQXExpression (right : Bool) : (jacobiFastQXExpression right).interpret = TwoAxisHelicoid.jacobiFastQXExpression right := by
  cases right <;> rfl

theorem interpret_jacobiFastQInvXExpression (right : Bool) : (jacobiFastQInvXExpression right).interpret = TwoAxisHelicoid.jacobiFastQInvXExpression right := by
  cases right <;> rfl

theorem interpret_jacobiFastQRXExpression (right : Bool) : (jacobiFastQRXExpression right).interpret = TwoAxisHelicoid.jacobiFastQRXExpression right := by
  cases right <;> rfl

theorem interpret_jacobiFastQInvRXExpression (right : Bool) : (jacobiFastQInvRXExpression right).interpret = TwoAxisHelicoid.jacobiFastQInvRXExpression right := by
  cases right <;> rfl

theorem interpret_jacobiFastRXExpression (right : Bool) : (jacobiFastRXExpression right).interpret = TwoAxisHelicoid.jacobiFastRXExpression right := by
  cases right <;> rfl

namespace DyadicJacobiKernelTrace
theorem fast_valid_of_valid (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (z : DyadicBall) (w : DyadicJacobiKernelTrace)
    (hw : w.FastValid cfg productError eulerError right p z) :
    w.interpret.FastValid cfg.interpret productError eulerError right p.interpret z.interpret := by
  rcases hw with ⟨hA,hB,hC,hD,hX,hRX,hPA,hPB,hPC,hPD,hEA,hEB,hR⟩
  simp only [TwoAxisHelicoid.DyadicJacobiKernelTrace.FastValid, interpret, DyadicJacobiParameters.interpret,
    DyadicJacobiBaseParameters.interpret, DyadicExpressionTrace.interpret_output,
    BallConfig.interpret_prec]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have h := jacobi_expression_valid_of_check cfg [p.base.q.output,p.base.r.output,p.base.beta.output,w.x.output]
      (jacobiFastQXExpression right) w.qx hA
    rw [interpret_jacobiFastQXExpression] at h
    exact h
  · have h := jacobi_expression_valid_of_check cfg [p.base.q.output,p.base.r.output,p.base.beta.output,w.x.output]
      (jacobiFastQInvXExpression right) w.qinvx hB
    rw [interpret_jacobiFastQInvXExpression] at h
    exact h
  · have h := jacobi_expression_valid_of_check cfg [p.base.q.output,p.base.r.output,p.base.beta.output,w.x.output]
      (jacobiFastQRXExpression right) w.qrx hC
    rw [interpret_jacobiFastQRXExpression] at h
    exact h
  · have h := jacobi_expression_valid_of_check cfg [p.base.q.output,p.base.r.output,p.base.beta.output,w.x.output]
      (jacobiFastQInvRXExpression right) w.qinvrx hD
    rw [interpret_jacobiFastQInvRXExpression] at h
    exact h
  · have h := jacobi_expression_valid_of_check cfg [p.base.height,p.base.abscissa,z]
      (jacobiPhysicalXExpression right) w.x hX
    rw [interpret_jacobiPhysicalXExpression] at h
    exact h
  · have h := jacobi_expression_valid_of_check cfg [p.base.q.output,p.base.r.output,p.base.beta.output,w.x.output]
      (jacobiFastRXExpression right) w.rx hRX
    rw [interpret_jacobiFastRXExpression] at h
    exact h
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
namespace JacobiRangeNode
theorem fast_valid_of_valid (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : JacobiRangeNode) (hw : w.FastValid cfg productError eulerError right p center h node weight) :
    w.interpret.FastValid cfg.interpret productError eulerError right p.interpret center.interpret h node weight := by
  rcases hw with ⟨hz,hf,hw⟩
  refine ⟨?_, w.function.fast_valid_of_valid cfg productError eulerError right p w.point hf, ?_⟩
  · simpa only [interpret, TwoAxisHelicoid.ComplexBall.coarsens, TwoAxisHelicoid.QComplex.absUpper,
      TwoAxisHelicoid.QComplex.sub, TwoAxisHelicoid.QComplex.add, TwoAxisHelicoid.QComplex.neg, TwoAxisHelicoid.DyadicBall.toBall,
      DyadicBall.interpret, TwoAxisHelicoid.ComplexBall.add, TwoAxisHelicoid.ComplexBall.rational,
      TwoAxisHelicoid.ComplexBall.point, TwoAxisHelicoid.QComplex.ofRat, ComplexBall.coarsens,
      QComplex.absUpper, QComplex.sub, QComplex.add, QComplex.neg, DyadicBall.toBall,
      ComplexBall.add, ComplexBall.rational, ComplexBall.point, QComplex.ofRat,
      rat_abs_eq, BallConfig.interpret_prec, DyadicBall.denominator,
      TwoAxisHelicoid.DyadicBall.denominator] using hz
  · have he := jacobi_expression_valid_of_check cfg [w.function.output]
      (.mul (.rational weight) (.input 0)) w.weighted hw
    have hexpr : (BallExpression.mul (.rational weight) (.input 0)).interpret =
        TwoAxisHelicoid.BallExpression.mul (.rational weight) (.input 0) := rfl
    rw [hexpr] at he
    simpa only [interpret, DyadicJacobiKernelTrace.interpret_output, List.map_cons,
      List.map_nil] using he

end JacobiRangeNode
end TwoAxisHelicoid.TraceData
#print axioms TwoAxisHelicoid.TraceData.JacobiRangeNode.fast_valid_of_valid
