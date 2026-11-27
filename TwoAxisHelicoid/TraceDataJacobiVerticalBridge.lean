import TwoAxisHelicoid.TraceDataJacobiVertical
import TwoAxisHelicoid.TraceDataJacobiKernelBridge
import TwoAxisHelicoid.JacobiVerticalCertificate

namespace TwoAxisHelicoid.TraceData

theorem interpret_jacobiSmallNomeExpression (u : ℚ) :
    (jacobiSmallNomeExpression u).interpret = TwoAxisHelicoid.jacobiSmallNomeExpression u := rfl

theorem jacobiSmallNome_valid_of_check (cfg : BallConfig) (u : ℚ) (w : DyadicExpressionTrace)
    (hw : w.check cfg (dyadicInputList []) (jacobiSmallNomeExpression u) = true) :
    w.interpret.Valid cfg.interpret (TwoAxisHelicoid.dyadicInputList []) (TwoAxisHelicoid.jacobiSmallNomeExpression u) := by
  have h := jacobi_expression_valid_of_check cfg [] (jacobiSmallNomeExpression u) w hw
  rw [interpret_jacobiSmallNomeExpression] at h
  exact h

namespace DyadicJacobiVerticalTrace

def interpret (w : DyadicJacobiVerticalTrace) : TwoAxisHelicoid.DyadicJacobiVerticalTrace :=
  ⟨w.first.interpret,w.second.interpret,w.output.interpret⟩

theorem valid_of_valid (cfg : BallConfig) (err : ℕ) (p : DyadicJacobiBaseParameters)
    (w : DyadicJacobiVerticalTrace) (hw : w.Valid cfg err p) :
    w.interpret.Valid cfg.interpret err p.interpret := by
  rcases hw with ⟨hf,hs,ha⟩
  simp only [interpret, TwoAxisHelicoid.DyadicJacobiVerticalTrace.Valid,
    DyadicJacobiBaseParameters.interpret, DyadicExpressionTrace.interpret_output]
  refine ⟨?_,?_,?_⟩
  · exact (DyadicJacobiSecondTrace.interpret_valid _ _ _ _ _).mpr hf
  · simpa only [DyadicBall.interpret_neg] using
      (DyadicJacobiSecondTrace.interpret_valid cfg err p.q.output p.beta.output.neg w.second).mpr hs
  · exact (DyadicBall.interpret_ChecksAdd _ _ _).mpr ha

end DyadicJacobiVerticalTrace
end TwoAxisHelicoid.TraceData

#print axioms TwoAxisHelicoid.TraceData.DyadicJacobiVerticalTrace.valid_of_valid
