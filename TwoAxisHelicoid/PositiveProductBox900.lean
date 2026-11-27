import TwoAxisHelicoid.TraceDataPositiveProductBox900
import TwoAxisHelicoid.TraceDataJacobiFastBridge
import TwoAxisHelicoid.TraceDataJacobiVerticalBridge
import TwoAxisHelicoid.JacobiRangeComposite
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def positiveProductBox900Parameters : DyadicJacobiParameters := TraceData.positiveProductBox900Parameters.interpret
theorem positiveProductBox900Parameters_valid : positiveProductBox900Parameters.Valid ⟨64,12,6⟩ 18446744074 :=
  TraceData.DyadicJacobiParameters.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Parameters_valid
noncomputable def positiveProductBox900Cell000 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell000.interpret
theorem positiveProductBox900Cell000_valid : positiveProductBox900Cell000.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-7/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.disk TraceData.positiveProductBox900Cell000.diskFunction TraceData.positiveProductBox900Cell000Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell000Node00 TraceData.positiveProductBox900Cell000Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell000Node01 TraceData.positiveProductBox900Cell000Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell000Node02 TraceData.positiveProductBox900Cell000Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell000Node03 TraceData.positiveProductBox900Cell000Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell000Node04 TraceData.positiveProductBox900Cell000Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell000Node05 TraceData.positiveProductBox900Cell000Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell000Node06 TraceData.positiveProductBox900Cell000Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell000Node07 TraceData.positiveProductBox900Cell000Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell000Node08 TraceData.positiveProductBox900Cell000Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell000Node09 TraceData.positiveProductBox900Cell000Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell000Node10 TraceData.positiveProductBox900Cell000Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell000Node11 TraceData.positiveProductBox900Cell000Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell000Node12 TraceData.positiveProductBox900Cell000Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell000Node13 TraceData.positiveProductBox900Cell000Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell000Node14 TraceData.positiveProductBox900Cell000Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell000Node15 TraceData.positiveProductBox900Cell000Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell000Node16 TraceData.positiveProductBox900Cell000Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell000Node17 TraceData.positiveProductBox900Cell000Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell000Node18 TraceData.positiveProductBox900Cell000Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell000Node19 TraceData.positiveProductBox900Cell000Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell000Node20 TraceData.positiveProductBox900Cell000Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell000Node21 TraceData.positiveProductBox900Cell000Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell000Node22 TraceData.positiveProductBox900Cell000Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell000Node23 TraceData.positiveProductBox900Cell000Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell000Node24 TraceData.positiveProductBox900Cell000Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell000Node25 TraceData.positiveProductBox900Cell000Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell000Node26 TraceData.positiveProductBox900Cell000Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell000Node27 TraceData.positiveProductBox900Cell000Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell000Node28 TraceData.positiveProductBox900Cell000Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell000Node29 TraceData.positiveProductBox900Cell000Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell000Node30 TraceData.positiveProductBox900Cell000Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell000.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell000Node31 TraceData.positiveProductBox900Cell000Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell001 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell001.interpret
theorem positiveProductBox900Cell001_valid : positiveProductBox900Cell001.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-5/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.disk TraceData.positiveProductBox900Cell001.diskFunction TraceData.positiveProductBox900Cell001Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell001Node00 TraceData.positiveProductBox900Cell001Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell001Node01 TraceData.positiveProductBox900Cell001Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell001Node02 TraceData.positiveProductBox900Cell001Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell001Node03 TraceData.positiveProductBox900Cell001Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell001Node04 TraceData.positiveProductBox900Cell001Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell001Node05 TraceData.positiveProductBox900Cell001Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell001Node06 TraceData.positiveProductBox900Cell001Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell001Node07 TraceData.positiveProductBox900Cell001Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell001Node08 TraceData.positiveProductBox900Cell001Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell001Node09 TraceData.positiveProductBox900Cell001Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell001Node10 TraceData.positiveProductBox900Cell001Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell001Node11 TraceData.positiveProductBox900Cell001Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell001Node12 TraceData.positiveProductBox900Cell001Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell001Node13 TraceData.positiveProductBox900Cell001Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell001Node14 TraceData.positiveProductBox900Cell001Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell001Node15 TraceData.positiveProductBox900Cell001Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell001Node16 TraceData.positiveProductBox900Cell001Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell001Node17 TraceData.positiveProductBox900Cell001Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell001Node18 TraceData.positiveProductBox900Cell001Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell001Node19 TraceData.positiveProductBox900Cell001Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell001Node20 TraceData.positiveProductBox900Cell001Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell001Node21 TraceData.positiveProductBox900Cell001Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell001Node22 TraceData.positiveProductBox900Cell001Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell001Node23 TraceData.positiveProductBox900Cell001Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell001Node24 TraceData.positiveProductBox900Cell001Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell001Node25 TraceData.positiveProductBox900Cell001Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell001Node26 TraceData.positiveProductBox900Cell001Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell001Node27 TraceData.positiveProductBox900Cell001Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell001Node28 TraceData.positiveProductBox900Cell001Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell001Node29 TraceData.positiveProductBox900Cell001Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell001Node30 TraceData.positiveProductBox900Cell001Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell001.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell001Node31 TraceData.positiveProductBox900Cell001Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell002 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell002.interpret
theorem positiveProductBox900Cell002_valid : positiveProductBox900Cell002.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-7/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.disk TraceData.positiveProductBox900Cell002.diskFunction TraceData.positiveProductBox900Cell002Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell002Node00 TraceData.positiveProductBox900Cell002Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell002Node01 TraceData.positiveProductBox900Cell002Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell002Node02 TraceData.positiveProductBox900Cell002Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell002Node03 TraceData.positiveProductBox900Cell002Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell002Node04 TraceData.positiveProductBox900Cell002Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell002Node05 TraceData.positiveProductBox900Cell002Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell002Node06 TraceData.positiveProductBox900Cell002Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell002Node07 TraceData.positiveProductBox900Cell002Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell002Node08 TraceData.positiveProductBox900Cell002Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell002Node09 TraceData.positiveProductBox900Cell002Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell002Node10 TraceData.positiveProductBox900Cell002Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell002Node11 TraceData.positiveProductBox900Cell002Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell002Node12 TraceData.positiveProductBox900Cell002Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell002Node13 TraceData.positiveProductBox900Cell002Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell002Node14 TraceData.positiveProductBox900Cell002Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell002Node15 TraceData.positiveProductBox900Cell002Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell002Node16 TraceData.positiveProductBox900Cell002Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell002Node17 TraceData.positiveProductBox900Cell002Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell002Node18 TraceData.positiveProductBox900Cell002Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell002Node19 TraceData.positiveProductBox900Cell002Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell002Node20 TraceData.positiveProductBox900Cell002Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell002Node21 TraceData.positiveProductBox900Cell002Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell002Node22 TraceData.positiveProductBox900Cell002Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell002Node23 TraceData.positiveProductBox900Cell002Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell002Node24 TraceData.positiveProductBox900Cell002Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell002Node25 TraceData.positiveProductBox900Cell002Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell002Node26 TraceData.positiveProductBox900Cell002Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell002Node27 TraceData.positiveProductBox900Cell002Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell002Node28 TraceData.positiveProductBox900Cell002Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell002Node29 TraceData.positiveProductBox900Cell002Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell002Node30 TraceData.positiveProductBox900Cell002Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell002Node31 TraceData.positiveProductBox900Cell002Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell003 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell003.interpret
theorem positiveProductBox900Cell003_valid : positiveProductBox900Cell003.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-5/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.disk TraceData.positiveProductBox900Cell003.diskFunction TraceData.positiveProductBox900Cell003Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell003Node00 TraceData.positiveProductBox900Cell003Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell003Node01 TraceData.positiveProductBox900Cell003Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell003Node02 TraceData.positiveProductBox900Cell003Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell003Node03 TraceData.positiveProductBox900Cell003Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell003Node04 TraceData.positiveProductBox900Cell003Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell003Node05 TraceData.positiveProductBox900Cell003Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell003Node06 TraceData.positiveProductBox900Cell003Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell003Node07 TraceData.positiveProductBox900Cell003Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell003Node08 TraceData.positiveProductBox900Cell003Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell003Node09 TraceData.positiveProductBox900Cell003Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell003Node10 TraceData.positiveProductBox900Cell003Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell003Node11 TraceData.positiveProductBox900Cell003Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell003Node12 TraceData.positiveProductBox900Cell003Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell003Node13 TraceData.positiveProductBox900Cell003Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell003Node14 TraceData.positiveProductBox900Cell003Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell003Node15 TraceData.positiveProductBox900Cell003Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell003Node16 TraceData.positiveProductBox900Cell003Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell003Node17 TraceData.positiveProductBox900Cell003Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell003Node18 TraceData.positiveProductBox900Cell003Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell003Node19 TraceData.positiveProductBox900Cell003Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell003Node20 TraceData.positiveProductBox900Cell003Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell003Node21 TraceData.positiveProductBox900Cell003Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell003Node22 TraceData.positiveProductBox900Cell003Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell003Node23 TraceData.positiveProductBox900Cell003Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell003Node24 TraceData.positiveProductBox900Cell003Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell003Node25 TraceData.positiveProductBox900Cell003Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell003Node26 TraceData.positiveProductBox900Cell003Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell003Node27 TraceData.positiveProductBox900Cell003Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell003Node28 TraceData.positiveProductBox900Cell003Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell003Node29 TraceData.positiveProductBox900Cell003Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell003Node30 TraceData.positiveProductBox900Cell003Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell003.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell003Node31 TraceData.positiveProductBox900Cell003Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell004 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell004.interpret
theorem positiveProductBox900Cell004_valid : positiveProductBox900Cell004.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-7/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.disk TraceData.positiveProductBox900Cell004.diskFunction TraceData.positiveProductBox900Cell004Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell004Node00 TraceData.positiveProductBox900Cell004Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell004Node01 TraceData.positiveProductBox900Cell004Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell004Node02 TraceData.positiveProductBox900Cell004Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell004Node03 TraceData.positiveProductBox900Cell004Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell004Node04 TraceData.positiveProductBox900Cell004Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell004Node05 TraceData.positiveProductBox900Cell004Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell004Node06 TraceData.positiveProductBox900Cell004Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell004Node07 TraceData.positiveProductBox900Cell004Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell004Node08 TraceData.positiveProductBox900Cell004Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell004Node09 TraceData.positiveProductBox900Cell004Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell004Node10 TraceData.positiveProductBox900Cell004Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell004Node11 TraceData.positiveProductBox900Cell004Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell004Node12 TraceData.positiveProductBox900Cell004Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell004Node13 TraceData.positiveProductBox900Cell004Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell004Node14 TraceData.positiveProductBox900Cell004Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell004Node15 TraceData.positiveProductBox900Cell004Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell004Node16 TraceData.positiveProductBox900Cell004Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell004Node17 TraceData.positiveProductBox900Cell004Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell004Node18 TraceData.positiveProductBox900Cell004Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell004Node19 TraceData.positiveProductBox900Cell004Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell004Node20 TraceData.positiveProductBox900Cell004Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell004Node21 TraceData.positiveProductBox900Cell004Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell004Node22 TraceData.positiveProductBox900Cell004Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell004Node23 TraceData.positiveProductBox900Cell004Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell004Node24 TraceData.positiveProductBox900Cell004Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell004Node25 TraceData.positiveProductBox900Cell004Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell004Node26 TraceData.positiveProductBox900Cell004Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell004Node27 TraceData.positiveProductBox900Cell004Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell004Node28 TraceData.positiveProductBox900Cell004Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell004Node29 TraceData.positiveProductBox900Cell004Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell004Node30 TraceData.positiveProductBox900Cell004Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell004Node31 TraceData.positiveProductBox900Cell004Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell005 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell005.interpret
theorem positiveProductBox900Cell005_valid : positiveProductBox900Cell005.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-11/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.disk TraceData.positiveProductBox900Cell005.diskFunction TraceData.positiveProductBox900Cell005Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell005Node00 TraceData.positiveProductBox900Cell005Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell005Node01 TraceData.positiveProductBox900Cell005Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell005Node02 TraceData.positiveProductBox900Cell005Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell005Node03 TraceData.positiveProductBox900Cell005Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell005Node04 TraceData.positiveProductBox900Cell005Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell005Node05 TraceData.positiveProductBox900Cell005Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell005Node06 TraceData.positiveProductBox900Cell005Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell005Node07 TraceData.positiveProductBox900Cell005Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell005Node08 TraceData.positiveProductBox900Cell005Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell005Node09 TraceData.positiveProductBox900Cell005Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell005Node10 TraceData.positiveProductBox900Cell005Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell005Node11 TraceData.positiveProductBox900Cell005Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell005Node12 TraceData.positiveProductBox900Cell005Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell005Node13 TraceData.positiveProductBox900Cell005Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell005Node14 TraceData.positiveProductBox900Cell005Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell005Node15 TraceData.positiveProductBox900Cell005Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell005Node16 TraceData.positiveProductBox900Cell005Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell005Node17 TraceData.positiveProductBox900Cell005Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell005Node18 TraceData.positiveProductBox900Cell005Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell005Node19 TraceData.positiveProductBox900Cell005Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell005Node20 TraceData.positiveProductBox900Cell005Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell005Node21 TraceData.positiveProductBox900Cell005Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell005Node22 TraceData.positiveProductBox900Cell005Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell005Node23 TraceData.positiveProductBox900Cell005Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell005Node24 TraceData.positiveProductBox900Cell005Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell005Node25 TraceData.positiveProductBox900Cell005Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell005Node26 TraceData.positiveProductBox900Cell005Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell005Node27 TraceData.positiveProductBox900Cell005Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell005Node28 TraceData.positiveProductBox900Cell005Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell005Node29 TraceData.positiveProductBox900Cell005Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell005Node30 TraceData.positiveProductBox900Cell005Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell005.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell005Node31 TraceData.positiveProductBox900Cell005Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell006 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell006.interpret
theorem positiveProductBox900Cell006_valid : positiveProductBox900Cell006.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-9/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.disk TraceData.positiveProductBox900Cell006.diskFunction TraceData.positiveProductBox900Cell006Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell006Node00 TraceData.positiveProductBox900Cell006Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell006Node01 TraceData.positiveProductBox900Cell006Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell006Node02 TraceData.positiveProductBox900Cell006Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell006Node03 TraceData.positiveProductBox900Cell006Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell006Node04 TraceData.positiveProductBox900Cell006Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell006Node05 TraceData.positiveProductBox900Cell006Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell006Node06 TraceData.positiveProductBox900Cell006Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell006Node07 TraceData.positiveProductBox900Cell006Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell006Node08 TraceData.positiveProductBox900Cell006Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell006Node09 TraceData.positiveProductBox900Cell006Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell006Node10 TraceData.positiveProductBox900Cell006Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell006Node11 TraceData.positiveProductBox900Cell006Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell006Node12 TraceData.positiveProductBox900Cell006Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell006Node13 TraceData.positiveProductBox900Cell006Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell006Node14 TraceData.positiveProductBox900Cell006Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell006Node15 TraceData.positiveProductBox900Cell006Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell006Node16 TraceData.positiveProductBox900Cell006Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell006Node17 TraceData.positiveProductBox900Cell006Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell006Node18 TraceData.positiveProductBox900Cell006Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell006Node19 TraceData.positiveProductBox900Cell006Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell006Node20 TraceData.positiveProductBox900Cell006Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell006Node21 TraceData.positiveProductBox900Cell006Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell006Node22 TraceData.positiveProductBox900Cell006Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell006Node23 TraceData.positiveProductBox900Cell006Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell006Node24 TraceData.positiveProductBox900Cell006Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell006Node25 TraceData.positiveProductBox900Cell006Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell006Node26 TraceData.positiveProductBox900Cell006Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell006Node27 TraceData.positiveProductBox900Cell006Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell006Node28 TraceData.positiveProductBox900Cell006Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell006Node29 TraceData.positiveProductBox900Cell006Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell006Node30 TraceData.positiveProductBox900Cell006Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell006.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell006Node31 TraceData.positiveProductBox900Cell006Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell007 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell007.interpret
theorem positiveProductBox900Cell007_valid : positiveProductBox900Cell007.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-7/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.disk TraceData.positiveProductBox900Cell007.diskFunction TraceData.positiveProductBox900Cell007Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell007Node00 TraceData.positiveProductBox900Cell007Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell007Node01 TraceData.positiveProductBox900Cell007Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell007Node02 TraceData.positiveProductBox900Cell007Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell007Node03 TraceData.positiveProductBox900Cell007Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell007Node04 TraceData.positiveProductBox900Cell007Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell007Node05 TraceData.positiveProductBox900Cell007Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell007Node06 TraceData.positiveProductBox900Cell007Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell007Node07 TraceData.positiveProductBox900Cell007Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell007Node08 TraceData.positiveProductBox900Cell007Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell007Node09 TraceData.positiveProductBox900Cell007Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell007Node10 TraceData.positiveProductBox900Cell007Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell007Node11 TraceData.positiveProductBox900Cell007Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell007Node12 TraceData.positiveProductBox900Cell007Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell007Node13 TraceData.positiveProductBox900Cell007Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell007Node14 TraceData.positiveProductBox900Cell007Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell007Node15 TraceData.positiveProductBox900Cell007Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell007Node16 TraceData.positiveProductBox900Cell007Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell007Node17 TraceData.positiveProductBox900Cell007Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell007Node18 TraceData.positiveProductBox900Cell007Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell007Node19 TraceData.positiveProductBox900Cell007Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell007Node20 TraceData.positiveProductBox900Cell007Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell007Node21 TraceData.positiveProductBox900Cell007Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell007Node22 TraceData.positiveProductBox900Cell007Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell007Node23 TraceData.positiveProductBox900Cell007Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell007Node24 TraceData.positiveProductBox900Cell007Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell007Node25 TraceData.positiveProductBox900Cell007Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell007Node26 TraceData.positiveProductBox900Cell007Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell007Node27 TraceData.positiveProductBox900Cell007Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell007Node28 TraceData.positiveProductBox900Cell007Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell007Node29 TraceData.positiveProductBox900Cell007Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell007Node30 TraceData.positiveProductBox900Cell007Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell007.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell007Node31 TraceData.positiveProductBox900Cell007Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell008 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell008.interpret
theorem positiveProductBox900Cell008_valid : positiveProductBox900Cell008.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-11/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.disk TraceData.positiveProductBox900Cell008.diskFunction TraceData.positiveProductBox900Cell008Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell008Node00 TraceData.positiveProductBox900Cell008Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell008Node01 TraceData.positiveProductBox900Cell008Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell008Node02 TraceData.positiveProductBox900Cell008Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell008Node03 TraceData.positiveProductBox900Cell008Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell008Node04 TraceData.positiveProductBox900Cell008Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell008Node05 TraceData.positiveProductBox900Cell008Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell008Node06 TraceData.positiveProductBox900Cell008Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell008Node07 TraceData.positiveProductBox900Cell008Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell008Node08 TraceData.positiveProductBox900Cell008Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell008Node09 TraceData.positiveProductBox900Cell008Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell008Node10 TraceData.positiveProductBox900Cell008Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell008Node11 TraceData.positiveProductBox900Cell008Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell008Node12 TraceData.positiveProductBox900Cell008Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell008Node13 TraceData.positiveProductBox900Cell008Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell008Node14 TraceData.positiveProductBox900Cell008Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell008Node15 TraceData.positiveProductBox900Cell008Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell008Node16 TraceData.positiveProductBox900Cell008Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell008Node17 TraceData.positiveProductBox900Cell008Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell008Node18 TraceData.positiveProductBox900Cell008Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell008Node19 TraceData.positiveProductBox900Cell008Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell008Node20 TraceData.positiveProductBox900Cell008Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell008Node21 TraceData.positiveProductBox900Cell008Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell008Node22 TraceData.positiveProductBox900Cell008Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell008Node23 TraceData.positiveProductBox900Cell008Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell008Node24 TraceData.positiveProductBox900Cell008Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell008Node25 TraceData.positiveProductBox900Cell008Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell008Node26 TraceData.positiveProductBox900Cell008Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell008Node27 TraceData.positiveProductBox900Cell008Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell008Node28 TraceData.positiveProductBox900Cell008Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell008Node29 TraceData.positiveProductBox900Cell008Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell008Node30 TraceData.positiveProductBox900Cell008Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell008.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell008Node31 TraceData.positiveProductBox900Cell008Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell009 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell009.interpret
theorem positiveProductBox900Cell009_valid : positiveProductBox900Cell009.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-9/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.disk TraceData.positiveProductBox900Cell009.diskFunction TraceData.positiveProductBox900Cell009Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell009Node00 TraceData.positiveProductBox900Cell009Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell009Node01 TraceData.positiveProductBox900Cell009Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell009Node02 TraceData.positiveProductBox900Cell009Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell009Node03 TraceData.positiveProductBox900Cell009Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell009Node04 TraceData.positiveProductBox900Cell009Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell009Node05 TraceData.positiveProductBox900Cell009Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell009Node06 TraceData.positiveProductBox900Cell009Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell009Node07 TraceData.positiveProductBox900Cell009Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell009Node08 TraceData.positiveProductBox900Cell009Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell009Node09 TraceData.positiveProductBox900Cell009Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell009Node10 TraceData.positiveProductBox900Cell009Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell009Node11 TraceData.positiveProductBox900Cell009Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell009Node12 TraceData.positiveProductBox900Cell009Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell009Node13 TraceData.positiveProductBox900Cell009Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell009Node14 TraceData.positiveProductBox900Cell009Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell009Node15 TraceData.positiveProductBox900Cell009Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell009Node16 TraceData.positiveProductBox900Cell009Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell009Node17 TraceData.positiveProductBox900Cell009Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell009Node18 TraceData.positiveProductBox900Cell009Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell009Node19 TraceData.positiveProductBox900Cell009Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell009Node20 TraceData.positiveProductBox900Cell009Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell009Node21 TraceData.positiveProductBox900Cell009Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell009Node22 TraceData.positiveProductBox900Cell009Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell009Node23 TraceData.positiveProductBox900Cell009Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell009Node24 TraceData.positiveProductBox900Cell009Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell009Node25 TraceData.positiveProductBox900Cell009Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell009Node26 TraceData.positiveProductBox900Cell009Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell009Node27 TraceData.positiveProductBox900Cell009Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell009Node28 TraceData.positiveProductBox900Cell009Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell009Node29 TraceData.positiveProductBox900Cell009Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell009Node30 TraceData.positiveProductBox900Cell009Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell009Node31 TraceData.positiveProductBox900Cell009Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell010 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell010.interpret
theorem positiveProductBox900Cell010_valid : positiveProductBox900Cell010.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-7/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.disk TraceData.positiveProductBox900Cell010.diskFunction TraceData.positiveProductBox900Cell010Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell010Node00 TraceData.positiveProductBox900Cell010Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell010Node01 TraceData.positiveProductBox900Cell010Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell010Node02 TraceData.positiveProductBox900Cell010Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell010Node03 TraceData.positiveProductBox900Cell010Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell010Node04 TraceData.positiveProductBox900Cell010Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell010Node05 TraceData.positiveProductBox900Cell010Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell010Node06 TraceData.positiveProductBox900Cell010Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell010Node07 TraceData.positiveProductBox900Cell010Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell010Node08 TraceData.positiveProductBox900Cell010Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell010Node09 TraceData.positiveProductBox900Cell010Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell010Node10 TraceData.positiveProductBox900Cell010Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell010Node11 TraceData.positiveProductBox900Cell010Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell010Node12 TraceData.positiveProductBox900Cell010Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell010Node13 TraceData.positiveProductBox900Cell010Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell010Node14 TraceData.positiveProductBox900Cell010Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell010Node15 TraceData.positiveProductBox900Cell010Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell010Node16 TraceData.positiveProductBox900Cell010Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell010Node17 TraceData.positiveProductBox900Cell010Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell010Node18 TraceData.positiveProductBox900Cell010Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell010Node19 TraceData.positiveProductBox900Cell010Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell010Node20 TraceData.positiveProductBox900Cell010Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell010Node21 TraceData.positiveProductBox900Cell010Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell010Node22 TraceData.positiveProductBox900Cell010Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell010Node23 TraceData.positiveProductBox900Cell010Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell010Node24 TraceData.positiveProductBox900Cell010Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell010Node25 TraceData.positiveProductBox900Cell010Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell010Node26 TraceData.positiveProductBox900Cell010Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell010Node27 TraceData.positiveProductBox900Cell010Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell010Node28 TraceData.positiveProductBox900Cell010Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell010Node29 TraceData.positiveProductBox900Cell010Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell010Node30 TraceData.positiveProductBox900Cell010Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell010.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell010Node31 TraceData.positiveProductBox900Cell010Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell011 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell011.interpret
theorem positiveProductBox900Cell011_valid : positiveProductBox900Cell011.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-5/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.disk TraceData.positiveProductBox900Cell011.diskFunction TraceData.positiveProductBox900Cell011Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell011Node00 TraceData.positiveProductBox900Cell011Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell011Node01 TraceData.positiveProductBox900Cell011Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell011Node02 TraceData.positiveProductBox900Cell011Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell011Node03 TraceData.positiveProductBox900Cell011Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell011Node04 TraceData.positiveProductBox900Cell011Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell011Node05 TraceData.positiveProductBox900Cell011Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell011Node06 TraceData.positiveProductBox900Cell011Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell011Node07 TraceData.positiveProductBox900Cell011Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell011Node08 TraceData.positiveProductBox900Cell011Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell011Node09 TraceData.positiveProductBox900Cell011Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell011Node10 TraceData.positiveProductBox900Cell011Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell011Node11 TraceData.positiveProductBox900Cell011Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell011Node12 TraceData.positiveProductBox900Cell011Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell011Node13 TraceData.positiveProductBox900Cell011Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell011Node14 TraceData.positiveProductBox900Cell011Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell011Node15 TraceData.positiveProductBox900Cell011Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell011Node16 TraceData.positiveProductBox900Cell011Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell011Node17 TraceData.positiveProductBox900Cell011Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell011Node18 TraceData.positiveProductBox900Cell011Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell011Node19 TraceData.positiveProductBox900Cell011Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell011Node20 TraceData.positiveProductBox900Cell011Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell011Node21 TraceData.positiveProductBox900Cell011Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell011Node22 TraceData.positiveProductBox900Cell011Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell011Node23 TraceData.positiveProductBox900Cell011Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell011Node24 TraceData.positiveProductBox900Cell011Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell011Node25 TraceData.positiveProductBox900Cell011Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell011Node26 TraceData.positiveProductBox900Cell011Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell011Node27 TraceData.positiveProductBox900Cell011Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell011Node28 TraceData.positiveProductBox900Cell011Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell011Node29 TraceData.positiveProductBox900Cell011Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell011Node30 TraceData.positiveProductBox900Cell011Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell011.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell011Node31 TraceData.positiveProductBox900Cell011Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell012 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell012.interpret
theorem positiveProductBox900Cell012_valid : positiveProductBox900Cell012.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-3/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.disk TraceData.positiveProductBox900Cell012.diskFunction TraceData.positiveProductBox900Cell012Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell012Node00 TraceData.positiveProductBox900Cell012Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell012Node01 TraceData.positiveProductBox900Cell012Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell012Node02 TraceData.positiveProductBox900Cell012Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell012Node03 TraceData.positiveProductBox900Cell012Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell012Node04 TraceData.positiveProductBox900Cell012Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell012Node05 TraceData.positiveProductBox900Cell012Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell012Node06 TraceData.positiveProductBox900Cell012Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell012Node07 TraceData.positiveProductBox900Cell012Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell012Node08 TraceData.positiveProductBox900Cell012Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell012Node09 TraceData.positiveProductBox900Cell012Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell012Node10 TraceData.positiveProductBox900Cell012Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell012Node11 TraceData.positiveProductBox900Cell012Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell012Node12 TraceData.positiveProductBox900Cell012Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell012Node13 TraceData.positiveProductBox900Cell012Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell012Node14 TraceData.positiveProductBox900Cell012Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell012Node15 TraceData.positiveProductBox900Cell012Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell012Node16 TraceData.positiveProductBox900Cell012Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell012Node17 TraceData.positiveProductBox900Cell012Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell012Node18 TraceData.positiveProductBox900Cell012Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell012Node19 TraceData.positiveProductBox900Cell012Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell012Node20 TraceData.positiveProductBox900Cell012Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell012Node21 TraceData.positiveProductBox900Cell012Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell012Node22 TraceData.positiveProductBox900Cell012Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell012Node23 TraceData.positiveProductBox900Cell012Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell012Node24 TraceData.positiveProductBox900Cell012Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell012Node25 TraceData.positiveProductBox900Cell012Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell012Node26 TraceData.positiveProductBox900Cell012Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell012Node27 TraceData.positiveProductBox900Cell012Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell012Node28 TraceData.positiveProductBox900Cell012Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell012Node29 TraceData.positiveProductBox900Cell012Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell012Node30 TraceData.positiveProductBox900Cell012Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell012.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell012Node31 TraceData.positiveProductBox900Cell012Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell013 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell013.interpret
theorem positiveProductBox900Cell013_valid : positiveProductBox900Cell013.FastValid ⟨64,12,6⟩ 18446744074 9223372037 false rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (-1/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.disk TraceData.positiveProductBox900Cell013.diskFunction TraceData.positiveProductBox900Cell013Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell013Node00 TraceData.positiveProductBox900Cell013Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell013Node01 TraceData.positiveProductBox900Cell013Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell013Node02 TraceData.positiveProductBox900Cell013Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell013Node03 TraceData.positiveProductBox900Cell013Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell013Node04 TraceData.positiveProductBox900Cell013Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell013Node05 TraceData.positiveProductBox900Cell013Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell013Node06 TraceData.positiveProductBox900Cell013Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell013Node07 TraceData.positiveProductBox900Cell013Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell013Node08 TraceData.positiveProductBox900Cell013Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell013Node09 TraceData.positiveProductBox900Cell013Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell013Node10 TraceData.positiveProductBox900Cell013Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell013Node11 TraceData.positiveProductBox900Cell013Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell013Node12 TraceData.positiveProductBox900Cell013Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell013Node13 TraceData.positiveProductBox900Cell013Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell013Node14 TraceData.positiveProductBox900Cell013Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell013Node15 TraceData.positiveProductBox900Cell013Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell013Node16 TraceData.positiveProductBox900Cell013Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell013Node17 TraceData.positiveProductBox900Cell013Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell013Node18 TraceData.positiveProductBox900Cell013Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell013Node19 TraceData.positiveProductBox900Cell013Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell013Node20 TraceData.positiveProductBox900Cell013Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell013Node21 TraceData.positiveProductBox900Cell013Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell013Node22 TraceData.positiveProductBox900Cell013Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell013Node23 TraceData.positiveProductBox900Cell013Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell013Node24 TraceData.positiveProductBox900Cell013Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell013Node25 TraceData.positiveProductBox900Cell013Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell013Node26 TraceData.positiveProductBox900Cell013Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell013Node27 TraceData.positiveProductBox900Cell013Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell013Node28 TraceData.positiveProductBox900Cell013Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell013Node29 TraceData.positiveProductBox900Cell013Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell013Node30 TraceData.positiveProductBox900Cell013Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 false TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell013.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell013Node31 TraceData.positiveProductBox900Cell013Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell014 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell014.interpret
theorem positiveProductBox900Cell014_valid : positiveProductBox900Cell014.FastValid ⟨64,12,6⟩ 18446744074 9223372037 true rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (1/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.disk TraceData.positiveProductBox900Cell014.diskFunction TraceData.positiveProductBox900Cell014Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell014Node00 TraceData.positiveProductBox900Cell014Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell014Node01 TraceData.positiveProductBox900Cell014Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell014Node02 TraceData.positiveProductBox900Cell014Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell014Node03 TraceData.positiveProductBox900Cell014Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell014Node04 TraceData.positiveProductBox900Cell014Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell014Node05 TraceData.positiveProductBox900Cell014Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell014Node06 TraceData.positiveProductBox900Cell014Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell014Node07 TraceData.positiveProductBox900Cell014Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell014Node08 TraceData.positiveProductBox900Cell014Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell014Node09 TraceData.positiveProductBox900Cell014Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell014Node10 TraceData.positiveProductBox900Cell014Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell014Node11 TraceData.positiveProductBox900Cell014Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell014Node12 TraceData.positiveProductBox900Cell014Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell014Node13 TraceData.positiveProductBox900Cell014Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell014Node14 TraceData.positiveProductBox900Cell014Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell014Node15 TraceData.positiveProductBox900Cell014Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell014Node16 TraceData.positiveProductBox900Cell014Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell014Node17 TraceData.positiveProductBox900Cell014Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell014Node18 TraceData.positiveProductBox900Cell014Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell014Node19 TraceData.positiveProductBox900Cell014Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell014Node20 TraceData.positiveProductBox900Cell014Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell014Node21 TraceData.positiveProductBox900Cell014Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell014Node22 TraceData.positiveProductBox900Cell014Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell014Node23 TraceData.positiveProductBox900Cell014Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell014Node24 TraceData.positiveProductBox900Cell014Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell014Node25 TraceData.positiveProductBox900Cell014Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell014Node26 TraceData.positiveProductBox900Cell014Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell014Node27 TraceData.positiveProductBox900Cell014Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell014Node28 TraceData.positiveProductBox900Cell014Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell014Node29 TraceData.positiveProductBox900Cell014Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell014Node30 TraceData.positiveProductBox900Cell014Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell014.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell014Node31 TraceData.positiveProductBox900Cell014Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell015 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell015.interpret
theorem positiveProductBox900Cell015_valid : positiveProductBox900Cell015.FastValid ⟨64,12,6⟩ 18446744074 9223372037 true rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (3/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.disk TraceData.positiveProductBox900Cell015.diskFunction TraceData.positiveProductBox900Cell015Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell015Node00 TraceData.positiveProductBox900Cell015Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell015Node01 TraceData.positiveProductBox900Cell015Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell015Node02 TraceData.positiveProductBox900Cell015Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell015Node03 TraceData.positiveProductBox900Cell015Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell015Node04 TraceData.positiveProductBox900Cell015Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell015Node05 TraceData.positiveProductBox900Cell015Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell015Node06 TraceData.positiveProductBox900Cell015Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell015Node07 TraceData.positiveProductBox900Cell015Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell015Node08 TraceData.positiveProductBox900Cell015Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell015Node09 TraceData.positiveProductBox900Cell015Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell015Node10 TraceData.positiveProductBox900Cell015Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell015Node11 TraceData.positiveProductBox900Cell015Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell015Node12 TraceData.positiveProductBox900Cell015Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell015Node13 TraceData.positiveProductBox900Cell015Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell015Node14 TraceData.positiveProductBox900Cell015Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell015Node15 TraceData.positiveProductBox900Cell015Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell015Node16 TraceData.positiveProductBox900Cell015Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell015Node17 TraceData.positiveProductBox900Cell015Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell015Node18 TraceData.positiveProductBox900Cell015Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell015Node19 TraceData.positiveProductBox900Cell015Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell015Node20 TraceData.positiveProductBox900Cell015Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell015Node21 TraceData.positiveProductBox900Cell015Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell015Node22 TraceData.positiveProductBox900Cell015Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell015Node23 TraceData.positiveProductBox900Cell015Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell015Node24 TraceData.positiveProductBox900Cell015Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell015Node25 TraceData.positiveProductBox900Cell015Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell015Node26 TraceData.positiveProductBox900Cell015Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell015Node27 TraceData.positiveProductBox900Cell015Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell015Node28 TraceData.positiveProductBox900Cell015Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell015Node29 TraceData.positiveProductBox900Cell015Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell015Node30 TraceData.positiveProductBox900Cell015Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell015Node31 TraceData.positiveProductBox900Cell015Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell016 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell016.interpret
theorem positiveProductBox900Cell016_valid : positiveProductBox900Cell016.FastValid ⟨64,12,6⟩ 18446744074 9223372037 true rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (3/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.disk TraceData.positiveProductBox900Cell016.diskFunction TraceData.positiveProductBox900Cell016Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell016Node00 TraceData.positiveProductBox900Cell016Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell016Node01 TraceData.positiveProductBox900Cell016Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell016Node02 TraceData.positiveProductBox900Cell016Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell016Node03 TraceData.positiveProductBox900Cell016Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell016Node04 TraceData.positiveProductBox900Cell016Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell016Node05 TraceData.positiveProductBox900Cell016Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell016Node06 TraceData.positiveProductBox900Cell016Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell016Node07 TraceData.positiveProductBox900Cell016Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell016Node08 TraceData.positiveProductBox900Cell016Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell016Node09 TraceData.positiveProductBox900Cell016Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell016Node10 TraceData.positiveProductBox900Cell016Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell016Node11 TraceData.positiveProductBox900Cell016Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell016Node12 TraceData.positiveProductBox900Cell016Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell016Node13 TraceData.positiveProductBox900Cell016Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell016Node14 TraceData.positiveProductBox900Cell016Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell016Node15 TraceData.positiveProductBox900Cell016Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell016Node16 TraceData.positiveProductBox900Cell016Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell016Node17 TraceData.positiveProductBox900Cell016Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell016Node18 TraceData.positiveProductBox900Cell016Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell016Node19 TraceData.positiveProductBox900Cell016Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell016Node20 TraceData.positiveProductBox900Cell016Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell016Node21 TraceData.positiveProductBox900Cell016Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell016Node22 TraceData.positiveProductBox900Cell016Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell016Node23 TraceData.positiveProductBox900Cell016Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell016Node24 TraceData.positiveProductBox900Cell016Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell016Node25 TraceData.positiveProductBox900Cell016Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell016Node26 TraceData.positiveProductBox900Cell016Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell016Node27 TraceData.positiveProductBox900Cell016Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell016Node28 TraceData.positiveProductBox900Cell016Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell016Node29 TraceData.positiveProductBox900Cell016Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell016Node30 TraceData.positiveProductBox900Cell016Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell016Node31 TraceData.positiveProductBox900Cell016Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell017 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell017.interpret
theorem positiveProductBox900Cell017_valid : positiveProductBox900Cell017.FastValid ⟨64,12,6⟩ 18446744074 9223372037 true rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (5/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.disk TraceData.positiveProductBox900Cell017.diskFunction TraceData.positiveProductBox900Cell017Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell017Node00 TraceData.positiveProductBox900Cell017Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell017Node01 TraceData.positiveProductBox900Cell017Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell017Node02 TraceData.positiveProductBox900Cell017Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell017Node03 TraceData.positiveProductBox900Cell017Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell017Node04 TraceData.positiveProductBox900Cell017Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell017Node05 TraceData.positiveProductBox900Cell017Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell017Node06 TraceData.positiveProductBox900Cell017Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell017Node07 TraceData.positiveProductBox900Cell017Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell017Node08 TraceData.positiveProductBox900Cell017Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell017Node09 TraceData.positiveProductBox900Cell017Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell017Node10 TraceData.positiveProductBox900Cell017Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell017Node11 TraceData.positiveProductBox900Cell017Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell017Node12 TraceData.positiveProductBox900Cell017Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell017Node13 TraceData.positiveProductBox900Cell017Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell017Node14 TraceData.positiveProductBox900Cell017Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell017Node15 TraceData.positiveProductBox900Cell017Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell017Node16 TraceData.positiveProductBox900Cell017Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell017Node17 TraceData.positiveProductBox900Cell017Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell017Node18 TraceData.positiveProductBox900Cell017Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell017Node19 TraceData.positiveProductBox900Cell017Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell017Node20 TraceData.positiveProductBox900Cell017Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell017Node21 TraceData.positiveProductBox900Cell017Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell017Node22 TraceData.positiveProductBox900Cell017Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell017Node23 TraceData.positiveProductBox900Cell017Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell017Node24 TraceData.positiveProductBox900Cell017Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell017Node25 TraceData.positiveProductBox900Cell017Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell017Node26 TraceData.positiveProductBox900Cell017Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell017Node27 TraceData.positiveProductBox900Cell017Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell017Node28 TraceData.positiveProductBox900Cell017Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell017Node29 TraceData.positiveProductBox900Cell017Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell017Node30 TraceData.positiveProductBox900Cell017Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell017.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell017Node31 TraceData.positiveProductBox900Cell017Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell018 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell018.interpret
theorem positiveProductBox900Cell018_valid : positiveProductBox900Cell018.FastValid ⟨64,12,6⟩ 18446744074 9223372037 true rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (7/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.disk TraceData.positiveProductBox900Cell018.diskFunction TraceData.positiveProductBox900Cell018Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell018Node00 TraceData.positiveProductBox900Cell018Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell018Node01 TraceData.positiveProductBox900Cell018Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell018Node02 TraceData.positiveProductBox900Cell018Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell018Node03 TraceData.positiveProductBox900Cell018Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell018Node04 TraceData.positiveProductBox900Cell018Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell018Node05 TraceData.positiveProductBox900Cell018Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell018Node06 TraceData.positiveProductBox900Cell018Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell018Node07 TraceData.positiveProductBox900Cell018Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell018Node08 TraceData.positiveProductBox900Cell018Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell018Node09 TraceData.positiveProductBox900Cell018Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell018Node10 TraceData.positiveProductBox900Cell018Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell018Node11 TraceData.positiveProductBox900Cell018Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell018Node12 TraceData.positiveProductBox900Cell018Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell018Node13 TraceData.positiveProductBox900Cell018Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell018Node14 TraceData.positiveProductBox900Cell018Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell018Node15 TraceData.positiveProductBox900Cell018Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell018Node16 TraceData.positiveProductBox900Cell018Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell018Node17 TraceData.positiveProductBox900Cell018Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell018Node18 TraceData.positiveProductBox900Cell018Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell018Node19 TraceData.positiveProductBox900Cell018Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell018Node20 TraceData.positiveProductBox900Cell018Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell018Node21 TraceData.positiveProductBox900Cell018Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell018Node22 TraceData.positiveProductBox900Cell018Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell018Node23 TraceData.positiveProductBox900Cell018Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell018Node24 TraceData.positiveProductBox900Cell018Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell018Node25 TraceData.positiveProductBox900Cell018Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell018Node26 TraceData.positiveProductBox900Cell018Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell018Node27 TraceData.positiveProductBox900Cell018Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell018Node28 TraceData.positiveProductBox900Cell018Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell018Node29 TraceData.positiveProductBox900Cell018Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell018Node30 TraceData.positiveProductBox900Cell018Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell018.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell018Node31 TraceData.positiveProductBox900Cell018Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell019 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell019.interpret
theorem positiveProductBox900Cell019_valid : positiveProductBox900Cell019.FastValid ⟨64,12,6⟩ 18446744074 9223372037 true rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (5/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.disk TraceData.positiveProductBox900Cell019.diskFunction TraceData.positiveProductBox900Cell019Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell019Node00 TraceData.positiveProductBox900Cell019Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell019Node01 TraceData.positiveProductBox900Cell019Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell019Node02 TraceData.positiveProductBox900Cell019Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell019Node03 TraceData.positiveProductBox900Cell019Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell019Node04 TraceData.positiveProductBox900Cell019Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell019Node05 TraceData.positiveProductBox900Cell019Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell019Node06 TraceData.positiveProductBox900Cell019Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell019Node07 TraceData.positiveProductBox900Cell019Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell019Node08 TraceData.positiveProductBox900Cell019Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell019Node09 TraceData.positiveProductBox900Cell019Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell019Node10 TraceData.positiveProductBox900Cell019Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell019Node11 TraceData.positiveProductBox900Cell019Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell019Node12 TraceData.positiveProductBox900Cell019Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell019Node13 TraceData.positiveProductBox900Cell019Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell019Node14 TraceData.positiveProductBox900Cell019Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell019Node15 TraceData.positiveProductBox900Cell019Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell019Node16 TraceData.positiveProductBox900Cell019Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell019Node17 TraceData.positiveProductBox900Cell019Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell019Node18 TraceData.positiveProductBox900Cell019Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell019Node19 TraceData.positiveProductBox900Cell019Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell019Node20 TraceData.positiveProductBox900Cell019Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell019Node21 TraceData.positiveProductBox900Cell019Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell019Node22 TraceData.positiveProductBox900Cell019Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell019Node23 TraceData.positiveProductBox900Cell019Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell019Node24 TraceData.positiveProductBox900Cell019Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell019Node25 TraceData.positiveProductBox900Cell019Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell019Node26 TraceData.positiveProductBox900Cell019Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell019Node27 TraceData.positiveProductBox900Cell019Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell019Node28 TraceData.positiveProductBox900Cell019Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell019Node29 TraceData.positiveProductBox900Cell019Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell019Node30 TraceData.positiveProductBox900Cell019Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell019.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell019Node31 TraceData.positiveProductBox900Cell019Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell020 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell020.interpret
theorem positiveProductBox900Cell020_valid : positiveProductBox900Cell020.FastValid ⟨64,12,6⟩ 18446744074 9223372037 true rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (7/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.disk TraceData.positiveProductBox900Cell020.diskFunction TraceData.positiveProductBox900Cell020Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell020Node00 TraceData.positiveProductBox900Cell020Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell020Node01 TraceData.positiveProductBox900Cell020Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell020Node02 TraceData.positiveProductBox900Cell020Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell020Node03 TraceData.positiveProductBox900Cell020Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell020Node04 TraceData.positiveProductBox900Cell020Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell020Node05 TraceData.positiveProductBox900Cell020Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell020Node06 TraceData.positiveProductBox900Cell020Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell020Node07 TraceData.positiveProductBox900Cell020Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell020Node08 TraceData.positiveProductBox900Cell020Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell020Node09 TraceData.positiveProductBox900Cell020Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell020Node10 TraceData.positiveProductBox900Cell020Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell020Node11 TraceData.positiveProductBox900Cell020Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell020Node12 TraceData.positiveProductBox900Cell020Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell020Node13 TraceData.positiveProductBox900Cell020Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell020Node14 TraceData.positiveProductBox900Cell020Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell020Node15 TraceData.positiveProductBox900Cell020Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell020Node16 TraceData.positiveProductBox900Cell020Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell020Node17 TraceData.positiveProductBox900Cell020Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell020Node18 TraceData.positiveProductBox900Cell020Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell020Node19 TraceData.positiveProductBox900Cell020Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell020Node20 TraceData.positiveProductBox900Cell020Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell020Node21 TraceData.positiveProductBox900Cell020Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell020Node22 TraceData.positiveProductBox900Cell020Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell020Node23 TraceData.positiveProductBox900Cell020Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell020Node24 TraceData.positiveProductBox900Cell020Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell020Node25 TraceData.positiveProductBox900Cell020Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell020Node26 TraceData.positiveProductBox900Cell020Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell020Node27 TraceData.positiveProductBox900Cell020Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell020Node28 TraceData.positiveProductBox900Cell020Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell020Node29 TraceData.positiveProductBox900Cell020Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell020Node30 TraceData.positiveProductBox900Cell020Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell020Node31 TraceData.positiveProductBox900Cell020Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell021 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell021.interpret
theorem positiveProductBox900Cell021_valid : positiveProductBox900Cell021.FastValid ⟨64,12,6⟩ 18446744074 9223372037 true rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (3/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.disk TraceData.positiveProductBox900Cell021.diskFunction TraceData.positiveProductBox900Cell021Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell021Node00 TraceData.positiveProductBox900Cell021Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell021Node01 TraceData.positiveProductBox900Cell021Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell021Node02 TraceData.positiveProductBox900Cell021Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell021Node03 TraceData.positiveProductBox900Cell021Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell021Node04 TraceData.positiveProductBox900Cell021Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell021Node05 TraceData.positiveProductBox900Cell021Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell021Node06 TraceData.positiveProductBox900Cell021Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell021Node07 TraceData.positiveProductBox900Cell021Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell021Node08 TraceData.positiveProductBox900Cell021Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell021Node09 TraceData.positiveProductBox900Cell021Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell021Node10 TraceData.positiveProductBox900Cell021Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell021Node11 TraceData.positiveProductBox900Cell021Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell021Node12 TraceData.positiveProductBox900Cell021Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell021Node13 TraceData.positiveProductBox900Cell021Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell021Node14 TraceData.positiveProductBox900Cell021Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell021Node15 TraceData.positiveProductBox900Cell021Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell021Node16 TraceData.positiveProductBox900Cell021Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell021Node17 TraceData.positiveProductBox900Cell021Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell021Node18 TraceData.positiveProductBox900Cell021Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell021Node19 TraceData.positiveProductBox900Cell021Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell021Node20 TraceData.positiveProductBox900Cell021Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell021Node21 TraceData.positiveProductBox900Cell021Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell021Node22 TraceData.positiveProductBox900Cell021Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell021Node23 TraceData.positiveProductBox900Cell021Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell021Node24 TraceData.positiveProductBox900Cell021Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell021Node25 TraceData.positiveProductBox900Cell021Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell021Node26 TraceData.positiveProductBox900Cell021Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell021Node27 TraceData.positiveProductBox900Cell021Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell021Node28 TraceData.positiveProductBox900Cell021Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell021Node29 TraceData.positiveProductBox900Cell021Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell021Node30 TraceData.positiveProductBox900Cell021Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell021.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell021Node31 TraceData.positiveProductBox900Cell021Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell022 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell022.interpret
theorem positiveProductBox900Cell022_valid : positiveProductBox900Cell022.FastValid ⟨64,12,6⟩ 18446744074 9223372037 true rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (5/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.disk TraceData.positiveProductBox900Cell022.diskFunction TraceData.positiveProductBox900Cell022Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell022Node00 TraceData.positiveProductBox900Cell022Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell022Node01 TraceData.positiveProductBox900Cell022Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell022Node02 TraceData.positiveProductBox900Cell022Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell022Node03 TraceData.positiveProductBox900Cell022Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell022Node04 TraceData.positiveProductBox900Cell022Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell022Node05 TraceData.positiveProductBox900Cell022Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell022Node06 TraceData.positiveProductBox900Cell022Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell022Node07 TraceData.positiveProductBox900Cell022Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell022Node08 TraceData.positiveProductBox900Cell022Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell022Node09 TraceData.positiveProductBox900Cell022Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell022Node10 TraceData.positiveProductBox900Cell022Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell022Node11 TraceData.positiveProductBox900Cell022Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell022Node12 TraceData.positiveProductBox900Cell022Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell022Node13 TraceData.positiveProductBox900Cell022Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell022Node14 TraceData.positiveProductBox900Cell022Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell022Node15 TraceData.positiveProductBox900Cell022Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell022Node16 TraceData.positiveProductBox900Cell022Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell022Node17 TraceData.positiveProductBox900Cell022Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell022Node18 TraceData.positiveProductBox900Cell022Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell022Node19 TraceData.positiveProductBox900Cell022Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell022Node20 TraceData.positiveProductBox900Cell022Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell022Node21 TraceData.positiveProductBox900Cell022Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell022Node22 TraceData.positiveProductBox900Cell022Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell022Node23 TraceData.positiveProductBox900Cell022Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell022Node24 TraceData.positiveProductBox900Cell022Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell022Node25 TraceData.positiveProductBox900Cell022Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell022Node26 TraceData.positiveProductBox900Cell022Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell022Node27 TraceData.positiveProductBox900Cell022Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell022Node28 TraceData.positiveProductBox900Cell022Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell022Node29 TraceData.positiveProductBox900Cell022Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell022Node30 TraceData.positiveProductBox900Cell022Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell022.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell022Node31 TraceData.positiveProductBox900Cell022Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveProductBox900Cell023 : JacobiRangeCell 32 := TraceData.positiveProductBox900Cell023.interpret
theorem positiveProductBox900Cell023_valid : positiveProductBox900Cell023.FastValid ⟨64,12,6⟩ 18446744074 9223372037 true rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (7/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiKernelTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.disk TraceData.positiveProductBox900Cell023.diskFunction TraceData.positiveProductBox900Cell023Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveProductBox900Cell023Node00 TraceData.positiveProductBox900Cell023Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveProductBox900Cell023Node01 TraceData.positiveProductBox900Cell023Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveProductBox900Cell023Node02 TraceData.positiveProductBox900Cell023Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveProductBox900Cell023Node03 TraceData.positiveProductBox900Cell023Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveProductBox900Cell023Node04 TraceData.positiveProductBox900Cell023Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveProductBox900Cell023Node05 TraceData.positiveProductBox900Cell023Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveProductBox900Cell023Node06 TraceData.positiveProductBox900Cell023Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveProductBox900Cell023Node07 TraceData.positiveProductBox900Cell023Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveProductBox900Cell023Node08 TraceData.positiveProductBox900Cell023Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveProductBox900Cell023Node09 TraceData.positiveProductBox900Cell023Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveProductBox900Cell023Node10 TraceData.positiveProductBox900Cell023Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveProductBox900Cell023Node11 TraceData.positiveProductBox900Cell023Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveProductBox900Cell023Node12 TraceData.positiveProductBox900Cell023Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveProductBox900Cell023Node13 TraceData.positiveProductBox900Cell023Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveProductBox900Cell023Node14 TraceData.positiveProductBox900Cell023Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveProductBox900Cell023Node15 TraceData.positiveProductBox900Cell023Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveProductBox900Cell023Node16 TraceData.positiveProductBox900Cell023Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveProductBox900Cell023Node17 TraceData.positiveProductBox900Cell023Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveProductBox900Cell023Node18 TraceData.positiveProductBox900Cell023Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveProductBox900Cell023Node19 TraceData.positiveProductBox900Cell023Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveProductBox900Cell023Node20 TraceData.positiveProductBox900Cell023Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveProductBox900Cell023Node21 TraceData.positiveProductBox900Cell023Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveProductBox900Cell023Node22 TraceData.positiveProductBox900Cell023Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveProductBox900Cell023Node23 TraceData.positiveProductBox900Cell023Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveProductBox900Cell023Node24 TraceData.positiveProductBox900Cell023Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveProductBox900Cell023Node25 TraceData.positiveProductBox900Cell023Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveProductBox900Cell023Node26 TraceData.positiveProductBox900Cell023Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveProductBox900Cell023Node27 TraceData.positiveProductBox900Cell023Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveProductBox900Cell023Node28 TraceData.positiveProductBox900Cell023Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveProductBox900Cell023Node29 TraceData.positiveProductBox900Cell023Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveProductBox900Cell023Node30 TraceData.positiveProductBox900Cell023Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiRangeNode.fast_valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 true TraceData.positiveProductBox900Parameters TraceData.positiveProductBox900Cell023.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveProductBox900Cell023Node31 TraceData.positiveProductBox900Cell023Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
def positiveProductBox900Boundary : ℕ → ℚ := fun i => match i with
  | 0 => (-1/2)
  | 1 => (-3/8)
  | 2 => (-1/4)
  | 3 => (-3/16)
  | 4 => (-1/8)
  | 5 => (-3/32)
  | 6 => (-5/64)
  | 7 => (-1/16)
  | 8 => (-3/64)
  | 9 => (-5/128)
  | 10 => (-1/32)
  | 11 => (-3/128)
  | 12 => (-1/64)
  | 13 => (-1/128)
  | 14 => (0/1)
  | 15 => (1/128)
  | 16 => (1/64)
  | 17 => (1/32)
  | 18 => (3/64)
  | 19 => (1/16)
  | 20 => (3/32)
  | 21 => (1/8)
  | 22 => (1/4)
  | 23 => (3/8)
  | _ => (1/2)
def positiveProductBox900Radius : Fin 24 → ℚ := ![(1/8),(1/8),(1/16),(1/16),(1/32),(1/64),(1/64),(1/64),(1/128),(1/128),(1/128),(1/128),(1/128),(1/128),(1/128),(1/128),(1/64),(1/64),(1/64),(1/32),(1/32),(1/8),(1/8),(1/8)]
def positiveProductBox900Right : Fin 24 → Bool := ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true]
noncomputable def positiveProductBox900Cells : Fin 24 → JacobiRangeCell 32 := ![positiveProductBox900Cell000,positiveProductBox900Cell001,positiveProductBox900Cell002,positiveProductBox900Cell003,positiveProductBox900Cell004,positiveProductBox900Cell005,positiveProductBox900Cell006,positiveProductBox900Cell007,positiveProductBox900Cell008,positiveProductBox900Cell009,positiveProductBox900Cell010,positiveProductBox900Cell011,positiveProductBox900Cell012,positiveProductBox900Cell013,positiveProductBox900Cell014,positiveProductBox900Cell015,positiveProductBox900Cell016,positiveProductBox900Cell017,positiveProductBox900Cell018,positiveProductBox900Cell019,positiveProductBox900Cell020,positiveProductBox900Cell021,positiveProductBox900Cell022,positiveProductBox900Cell023]
theorem positiveProductBox900Cells_valid : ∀ i : Fin 24, (positiveProductBox900Cells i).FastValid ⟨64,12,6⟩ 18446744074 9223372037 (positiveProductBox900Right i) rationalQuadrature32 32 positiveProductBox900Parameters (1/8) (jacobiCellCenter positiveProductBox900Boundary i) (jacobiCellRadius positiveProductBox900Boundary i) (positiveProductBox900Radius i) := by
  intro i
  fin_cases i
  · convert positiveProductBox900Cell000_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell001_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell002_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell003_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell004_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell005_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell006_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell007_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell008_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell009_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell010_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell011_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell012_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell013_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell014_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell015_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell016_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell017_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell018_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell019_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell020_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell021_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell022_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
  · convert positiveProductBox900Cell023_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveProductBox900Boundary]
theorem positiveProductBox900_lower : (3/10000 : ℚ) < (combineJacobiCells ⟨64,12,6⟩ positiveProductBox900Boundary positiveProductBox900Cells).center.re-(combineJacobiCells ⟨64,12,6⟩ positiveProductBox900Boundary positiveProductBox900Cells).radius := by decide +kernel
theorem positiveProductBox900_rectangle_positive {t a : ℝ}
    (htl : (((1/8) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((801/6400) : ℚ) : ℝ))
    (hal : (((1/2) : ℚ) : ℝ) ≤ a) (hau : a ≤ (((14757421430562734652347/29514790517935282585600) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < thetaHorizontalPeriod t a := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveProductBox900Parameters.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveProductBox900Parameters.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobi_fast_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ha0 ha1 htl positiveProductBox900Parameters positiveProductBox900Parameters_valid hbt hba
    positiveProductBox900Boundary (by decide +kernel) (by decide +kernel)
    positiveProductBox900Radius positiveProductBox900Right positiveProductBox900Cells positiveProductBox900Cells_valid
  have hl := (ComplexBall.re_bounds hb).1
  rw [← horizontal_period_centered ht0 a] at hl
  have hc : (((3/10000 : ℚ) : ℝ)) <
      (((combineJacobiCells ⟨64,12,6⟩ positiveProductBox900Boundary positiveProductBox900Cells).center.re-(combineJacobiCells ⟨64,12,6⟩ positiveProductBox900Boundary positiveProductBox900Cells).radius : ℚ) : ℝ) :=
    (Rat.cast_lt (K := ℝ)).mpr positiveProductBox900_lower
  rw [show (((3/10000 : ℚ) : ℝ)) = (3/10000 : ℝ) by norm_num] at hc
  exact hc.trans_le hl

theorem positiveProductBox900_vertical_enclosure {t : ℝ}
    (htl : (((1/8) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((801/6400) : ℚ) : ℝ)) :
    verticalA t ∈ Set.Icc (((1/2) : ℚ) : ℝ) (((14757421430562734652347/29514790517935282585600) : ℚ) : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have hdomain : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper :=
    ⟨ht0, htu.trans_lt ((by norm_num : (((801/6400) : ℚ) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  have hq := jacobiSmallNome_upper ⟨64,12,6⟩ (801/6400) (32673651801947/9223372036854775808) TraceData.positiveProductBox900Nome.interpret
    (TraceData.jacobiSmallNome_valid_of_check ⟨64,12,6⟩ (801/6400) TraceData.positiveProductBox900Nome TraceData.positiveProductBox900Nome_valid)
    (by decide +kernel)
  have hu := verticalA_small_rectangle_upper ht0 htu (by norm_num) hq
  have he : (1/2 : ℝ)+2*(((801/6400) : ℚ) : ℝ)*(((32673651801947/9223372036854775808) : ℚ) : ℝ) = (((14757421430562734652347/29514790517935282585600) : ℚ) : ℝ) := by norm_num
  rw [he] at hu
  exact ⟨by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (verticalA_gt_half hdomain).le, hu⟩
theorem positiveProductBox900_positive {t : ℝ}
    (htl : (((1/8) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((801/6400) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < actualPeriodAlong t := by
  have ha := positiveProductBox900_vertical_enclosure htl htu
  exact positiveProductBox900_rectangle_positive htl htu ha.1 ha.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positiveProductBox900_positive
