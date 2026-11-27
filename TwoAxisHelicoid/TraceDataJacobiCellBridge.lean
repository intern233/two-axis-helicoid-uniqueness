import TwoAxisHelicoid.TraceDataJacobiCell
import TwoAxisHelicoid.TraceDataJacobiKernelBridge
import TwoAxisHelicoid.JacobiRangeCell
import TwoAxisHelicoid.RationalQuadrature32

namespace TwoAxisHelicoid.TraceData
set_option maxHeartbeats 800000

theorem jacobiQuadratureNodes_eq : ∀ i : Fin 32,
    jacobiQuadratureNodes i = TwoAxisHelicoid.rationalQuadrature32.node i := by decide +kernel

theorem jacobiQuadratureWeights_eq : ∀ i : Fin 32,
    jacobiQuadratureWeights i = TwoAxisHelicoid.rationalQuadrature32.weight i := by decide +kernel

namespace JacobiRangeNode

def interpret (w : JacobiRangeNode) : TwoAxisHelicoid.JacobiRangeNode :=
  ⟨w.point.interpret,w.function.interpret,w.weighted.interpret⟩

theorem valid_of_valid (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : JacobiRangeNode) (hw : w.Valid cfg productError eulerError right p center h node weight) :
    w.interpret.Valid cfg.interpret productError eulerError right p.interpret center.interpret h node weight := by
  rcases hw with ⟨hz,hf,hw⟩
  refine ⟨?_, w.function.valid_of_valid cfg productError eulerError right p w.point hf, ?_⟩
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

namespace JacobiRangeCell
def interpret {K : ℕ} (w : JacobiRangeCell K) : TwoAxisHelicoid.JacobiRangeCell K :=
  ⟨w.center.interpret,w.disk.interpret,w.diskFunction.interpret,
    fun i => (w.nodes i).interpret,w.output.interpret⟩
end JacobiRangeCell
end TwoAxisHelicoid.TraceData

#print axioms TwoAxisHelicoid.TraceData.JacobiRangeNode.valid_of_valid
