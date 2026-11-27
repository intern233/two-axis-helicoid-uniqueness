import TwoAxisHelicoid.TraceDataBridge

namespace TwoAxisHelicoid.TraceData
namespace DyadicThetaSeed
@[simp] theorem interpret_positive (w : DyadicThetaSeed) : w.interpret.positive = w.positive.interpret := rfl
@[simp] theorem interpret_negative (w : DyadicThetaSeed) : w.interpret.negative = w.negative.interpret := rfl
@[simp] theorem interpret_positiveSquare (w : DyadicThetaSeed) : w.interpret.positiveSquare = w.positiveSquare.interpret := rfl
@[simp] theorem interpret_negativeSquare (w : DyadicThetaSeed) : w.interpret.negativeSquare = w.negativeSquare.interpret := rfl
end DyadicThetaSeed

namespace DyadicThetaTrace
@[simp] theorem interpret_loop (w : DyadicThetaTrace) : w.interpret.loop = w.loop.interpret := rfl
@[simp] theorem interpret_output (w : DyadicThetaTrace) : w.interpret.output = w.output.interpret := rfl
end DyadicThetaTrace

namespace DyadicThetaATrace
@[simp] theorem interpret_argument (w : DyadicThetaATrace) : w.interpret.argument = w.argument.interpret := rfl
@[simp] theorem interpret_shiftedArgument (w : DyadicThetaATrace) : w.interpret.shiftedArgument = w.shiftedArgument.interpret := rfl
@[simp] theorem interpret_seed (w : DyadicThetaATrace) : w.interpret.seed = w.seed.interpret := rfl
@[simp] theorem interpret_shiftedSeed (w : DyadicThetaATrace) : w.interpret.shiftedSeed = w.shiftedSeed.interpret := rfl
@[simp] theorem interpret_theta0 (w : DyadicThetaATrace) : w.interpret.theta0 = w.theta0.interpret := rfl
@[simp] theorem interpret_theta1 (w : DyadicThetaATrace) : w.interpret.theta1 = w.theta1.interpret := rfl
@[simp] theorem interpret_thetaShifted (w : DyadicThetaATrace) : w.interpret.thetaShifted = w.thetaShifted.interpret := rfl
@[simp] theorem interpret_result (w : DyadicThetaATrace) : w.interpret.result = w.result.interpret := rfl
end DyadicThetaATrace

namespace DyadicCoefficientTrace
@[simp] theorem interpret_argument (w : DyadicCoefficientTrace) : w.interpret.argument = w.argument.interpret := rfl
@[simp] theorem interpret_seedZero (w : DyadicCoefficientTrace) : w.interpret.seedZero = w.seedZero.interpret := rfl
@[simp] theorem interpret_seedA (w : DyadicCoefficientTrace) : w.interpret.seedA = w.seedA.interpret := rfl
@[simp] theorem interpret_thetaZero (w : DyadicCoefficientTrace) : w.interpret.thetaZero = w.thetaZero.interpret := rfl
@[simp] theorem interpret_thetaA (w : DyadicCoefficientTrace) : w.interpret.thetaA = w.thetaA.interpret := rfl
@[simp] theorem interpret_result (w : DyadicCoefficientTrace) : w.interpret.result = w.result.interpret := rfl
end DyadicCoefficientTrace

namespace RangeDyadicParameters
@[simp] theorem interpret_height (w : RangeDyadicParameters) : w.interpret.height = w.height.interpret := rfl
@[simp] theorem interpret_abscissa (w : RangeDyadicParameters) : w.interpret.abscissa = w.abscissa.interpret := rfl
@[simp] theorem interpret_q (w : RangeDyadicParameters) : w.interpret.q = w.q.interpret := rfl
@[simp] theorem interpret_coefficient (w : RangeDyadicParameters) : w.interpret.coefficient = w.coefficient.interpret := rfl
end RangeDyadicParameters

namespace RangeDerivativeParameters
@[simp] theorem interpret_base (w : RangeDerivativeParameters) : w.interpret.base = w.base.interpret := rfl
@[simp] theorem interpret_thetaA1 (w : RangeDerivativeParameters) : w.interpret.thetaA1 = w.thetaA1.interpret := rfl
@[simp] theorem interpret_thetaA2 (w : RangeDerivativeParameters) : w.interpret.thetaA2 = w.thetaA2.interpret := rfl
@[simp] theorem interpret_thetaA3 (w : RangeDerivativeParameters) : w.interpret.thetaA3 = w.thetaA3.interpret := rfl
@[simp] theorem interpret_thetaA4 (w : RangeDerivativeParameters) : w.interpret.thetaA4 = w.thetaA4.interpret := rfl
@[simp] theorem interpret_thetaZero3 (w : RangeDerivativeParameters) : w.interpret.thetaZero3 = w.thetaZero3.interpret := rfl
@[simp] theorem interpret_ratioA (w : RangeDerivativeParameters) : w.interpret.ratioA = w.ratioA.interpret := rfl
@[simp] theorem interpret_ratioA2 (w : RangeDerivativeParameters) : w.interpret.ratioA2 = w.ratioA2.interpret := rfl
@[simp] theorem interpret_ratioZero (w : RangeDerivativeParameters) : w.interpret.ratioZero = w.ratioZero.interpret := rfl
@[simp] theorem interpret_gt (w : RangeDerivativeParameters) : w.interpret.gt = w.gt.interpret := rfl
end RangeDerivativeParameters

namespace RangeDerivativeTrace
@[simp] theorem interpret_base (w : RangeDerivativeTrace) : w.interpret.base = w.base.interpret := rfl
@[simp] theorem interpret_thetaZ2 (w : RangeDerivativeTrace) : w.interpret.thetaZ2 = w.thetaZ2.interpret := rfl
@[simp] theorem interpret_thetaZ3 (w : RangeDerivativeTrace) : w.interpret.thetaZ3 = w.thetaZ3.interpret := rfl
@[simp] theorem interpret_thetaM1 (w : RangeDerivativeTrace) : w.interpret.thetaM1 = w.thetaM1.interpret := rfl
@[simp] theorem interpret_thetaM2 (w : RangeDerivativeTrace) : w.interpret.thetaM2 = w.thetaM2.interpret := rfl
@[simp] theorem interpret_resultA (w : RangeDerivativeTrace) : w.interpret.resultA = w.resultA.interpret := rfl
@[simp] theorem interpret_resultT (w : RangeDerivativeTrace) : w.interpret.resultT = w.resultT.interpret := rfl
end RangeDerivativeTrace

namespace RangeDerivativeNode
@[simp] theorem interpret_point (w : RangeDerivativeNode) : w.interpret.point = w.point.interpret := rfl
@[simp] theorem interpret_function (w : RangeDerivativeNode) : w.interpret.function = w.function.interpret := rfl
@[simp] theorem interpret_weightedA (w : RangeDerivativeNode) : w.interpret.weightedA = w.weightedA.interpret := rfl
@[simp] theorem interpret_weightedT (w : RangeDerivativeNode) : w.interpret.weightedT = w.weightedT.interpret := rfl
end RangeDerivativeNode

end TwoAxisHelicoid.TraceData
