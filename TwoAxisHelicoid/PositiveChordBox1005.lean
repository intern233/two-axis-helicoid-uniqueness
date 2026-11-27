import TwoAxisHelicoid.TraceDataPositiveChordBox1005
import TwoAxisHelicoid.TraceDataJacobiChordBridge
import TwoAxisHelicoid.TraceDataJacobiVerticalBridge
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def positiveChordBox1005Parameters : DyadicJacobiChordParameters := TraceData.positiveChordBox1005Parameters.interpret
theorem positiveChordBox1005Parameters_valid : positiveChordBox1005Parameters.Valid ⟨64,12,6⟩ 18446744074 :=
  TraceData.DyadicJacobiChordParameters.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Parameters_valid
noncomputable def positiveChordBox1005Cell000 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell000.interpret
theorem positiveChordBox1005Cell000_valid : positiveChordBox1005Cell000.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-32767/32768) (1/32768) (1/16384) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.disk TraceData.positiveChordBox1005Cell000.diskFunction TraceData.positiveChordBox1005Cell000Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell000Node00 TraceData.positiveChordBox1005Cell000Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell000Node01 TraceData.positiveChordBox1005Cell000Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell000Node02 TraceData.positiveChordBox1005Cell000Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell000Node03 TraceData.positiveChordBox1005Cell000Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell000Node04 TraceData.positiveChordBox1005Cell000Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell000Node05 TraceData.positiveChordBox1005Cell000Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell000Node06 TraceData.positiveChordBox1005Cell000Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell000Node07 TraceData.positiveChordBox1005Cell000Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell000Node08 TraceData.positiveChordBox1005Cell000Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell000Node09 TraceData.positiveChordBox1005Cell000Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell000Node10 TraceData.positiveChordBox1005Cell000Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell000Node11 TraceData.positiveChordBox1005Cell000Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell000Node12 TraceData.positiveChordBox1005Cell000Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell000Node13 TraceData.positiveChordBox1005Cell000Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell000Node14 TraceData.positiveChordBox1005Cell000Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell000Node15 TraceData.positiveChordBox1005Cell000Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell000Node16 TraceData.positiveChordBox1005Cell000Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell000Node17 TraceData.positiveChordBox1005Cell000Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell000Node18 TraceData.positiveChordBox1005Cell000Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell000Node19 TraceData.positiveChordBox1005Cell000Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell000Node20 TraceData.positiveChordBox1005Cell000Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell000Node21 TraceData.positiveChordBox1005Cell000Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell000Node22 TraceData.positiveChordBox1005Cell000Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell000Node23 TraceData.positiveChordBox1005Cell000Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell000Node24 TraceData.positiveChordBox1005Cell000Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell000Node25 TraceData.positiveChordBox1005Cell000Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell000Node26 TraceData.positiveChordBox1005Cell000Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell000Node27 TraceData.positiveChordBox1005Cell000Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell000Node28 TraceData.positiveChordBox1005Cell000Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell000Node29 TraceData.positiveChordBox1005Cell000Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell000Node30 TraceData.positiveChordBox1005Cell000Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell000.center (1/32768) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell000Node31 TraceData.positiveChordBox1005Cell000Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell001 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell001.interpret
theorem positiveChordBox1005Cell001_valid : positiveChordBox1005Cell001.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-32765/32768) (1/32768) (1/16384) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.disk TraceData.positiveChordBox1005Cell001.diskFunction TraceData.positiveChordBox1005Cell001Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell001Node00 TraceData.positiveChordBox1005Cell001Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell001Node01 TraceData.positiveChordBox1005Cell001Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell001Node02 TraceData.positiveChordBox1005Cell001Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell001Node03 TraceData.positiveChordBox1005Cell001Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell001Node04 TraceData.positiveChordBox1005Cell001Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell001Node05 TraceData.positiveChordBox1005Cell001Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell001Node06 TraceData.positiveChordBox1005Cell001Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell001Node07 TraceData.positiveChordBox1005Cell001Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell001Node08 TraceData.positiveChordBox1005Cell001Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell001Node09 TraceData.positiveChordBox1005Cell001Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell001Node10 TraceData.positiveChordBox1005Cell001Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell001Node11 TraceData.positiveChordBox1005Cell001Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell001Node12 TraceData.positiveChordBox1005Cell001Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell001Node13 TraceData.positiveChordBox1005Cell001Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell001Node14 TraceData.positiveChordBox1005Cell001Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell001Node15 TraceData.positiveChordBox1005Cell001Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell001Node16 TraceData.positiveChordBox1005Cell001Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell001Node17 TraceData.positiveChordBox1005Cell001Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell001Node18 TraceData.positiveChordBox1005Cell001Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell001Node19 TraceData.positiveChordBox1005Cell001Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell001Node20 TraceData.positiveChordBox1005Cell001Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell001Node21 TraceData.positiveChordBox1005Cell001Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell001Node22 TraceData.positiveChordBox1005Cell001Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell001Node23 TraceData.positiveChordBox1005Cell001Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell001Node24 TraceData.positiveChordBox1005Cell001Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell001Node25 TraceData.positiveChordBox1005Cell001Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell001Node26 TraceData.positiveChordBox1005Cell001Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell001Node27 TraceData.positiveChordBox1005Cell001Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell001Node28 TraceData.positiveChordBox1005Cell001Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell001Node29 TraceData.positiveChordBox1005Cell001Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell001Node30 TraceData.positiveChordBox1005Cell001Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell001.center (1/32768) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell001Node31 TraceData.positiveChordBox1005Cell001Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell002 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell002.interpret
theorem positiveChordBox1005Cell002_valid : positiveChordBox1005Cell002.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-32763/32768) (1/32768) (1/16384) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.disk TraceData.positiveChordBox1005Cell002.diskFunction TraceData.positiveChordBox1005Cell002Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell002Node00 TraceData.positiveChordBox1005Cell002Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell002Node01 TraceData.positiveChordBox1005Cell002Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell002Node02 TraceData.positiveChordBox1005Cell002Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell002Node03 TraceData.positiveChordBox1005Cell002Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell002Node04 TraceData.positiveChordBox1005Cell002Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell002Node05 TraceData.positiveChordBox1005Cell002Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell002Node06 TraceData.positiveChordBox1005Cell002Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell002Node07 TraceData.positiveChordBox1005Cell002Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell002Node08 TraceData.positiveChordBox1005Cell002Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell002Node09 TraceData.positiveChordBox1005Cell002Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell002Node10 TraceData.positiveChordBox1005Cell002Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell002Node11 TraceData.positiveChordBox1005Cell002Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell002Node12 TraceData.positiveChordBox1005Cell002Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell002Node13 TraceData.positiveChordBox1005Cell002Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell002Node14 TraceData.positiveChordBox1005Cell002Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell002Node15 TraceData.positiveChordBox1005Cell002Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell002Node16 TraceData.positiveChordBox1005Cell002Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell002Node17 TraceData.positiveChordBox1005Cell002Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell002Node18 TraceData.positiveChordBox1005Cell002Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell002Node19 TraceData.positiveChordBox1005Cell002Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell002Node20 TraceData.positiveChordBox1005Cell002Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell002Node21 TraceData.positiveChordBox1005Cell002Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell002Node22 TraceData.positiveChordBox1005Cell002Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell002Node23 TraceData.positiveChordBox1005Cell002Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell002Node24 TraceData.positiveChordBox1005Cell002Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell002Node25 TraceData.positiveChordBox1005Cell002Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell002Node26 TraceData.positiveChordBox1005Cell002Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell002Node27 TraceData.positiveChordBox1005Cell002Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell002Node28 TraceData.positiveChordBox1005Cell002Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell002Node29 TraceData.positiveChordBox1005Cell002Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell002Node30 TraceData.positiveChordBox1005Cell002Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell002.center (1/32768) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell002Node31 TraceData.positiveChordBox1005Cell002Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell003 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell003.interpret
theorem positiveChordBox1005Cell003_valid : positiveChordBox1005Cell003.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-32761/32768) (1/32768) (1/16384) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.disk TraceData.positiveChordBox1005Cell003.diskFunction TraceData.positiveChordBox1005Cell003Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell003Node00 TraceData.positiveChordBox1005Cell003Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell003Node01 TraceData.positiveChordBox1005Cell003Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell003Node02 TraceData.positiveChordBox1005Cell003Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell003Node03 TraceData.positiveChordBox1005Cell003Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell003Node04 TraceData.positiveChordBox1005Cell003Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell003Node05 TraceData.positiveChordBox1005Cell003Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell003Node06 TraceData.positiveChordBox1005Cell003Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell003Node07 TraceData.positiveChordBox1005Cell003Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell003Node08 TraceData.positiveChordBox1005Cell003Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell003Node09 TraceData.positiveChordBox1005Cell003Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell003Node10 TraceData.positiveChordBox1005Cell003Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell003Node11 TraceData.positiveChordBox1005Cell003Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell003Node12 TraceData.positiveChordBox1005Cell003Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell003Node13 TraceData.positiveChordBox1005Cell003Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell003Node14 TraceData.positiveChordBox1005Cell003Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell003Node15 TraceData.positiveChordBox1005Cell003Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell003Node16 TraceData.positiveChordBox1005Cell003Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell003Node17 TraceData.positiveChordBox1005Cell003Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell003Node18 TraceData.positiveChordBox1005Cell003Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell003Node19 TraceData.positiveChordBox1005Cell003Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell003Node20 TraceData.positiveChordBox1005Cell003Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell003Node21 TraceData.positiveChordBox1005Cell003Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell003Node22 TraceData.positiveChordBox1005Cell003Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell003Node23 TraceData.positiveChordBox1005Cell003Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell003Node24 TraceData.positiveChordBox1005Cell003Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell003Node25 TraceData.positiveChordBox1005Cell003Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell003Node26 TraceData.positiveChordBox1005Cell003Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell003Node27 TraceData.positiveChordBox1005Cell003Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell003Node28 TraceData.positiveChordBox1005Cell003Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell003Node29 TraceData.positiveChordBox1005Cell003Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell003Node30 TraceData.positiveChordBox1005Cell003Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell003.center (1/32768) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell003Node31 TraceData.positiveChordBox1005Cell003Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell004 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell004.interpret
theorem positiveChordBox1005Cell004_valid : positiveChordBox1005Cell004.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-8189/8192) (1/8192) (1/4096) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.disk TraceData.positiveChordBox1005Cell004.diskFunction TraceData.positiveChordBox1005Cell004Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell004Node00 TraceData.positiveChordBox1005Cell004Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell004Node01 TraceData.positiveChordBox1005Cell004Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell004Node02 TraceData.positiveChordBox1005Cell004Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell004Node03 TraceData.positiveChordBox1005Cell004Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell004Node04 TraceData.positiveChordBox1005Cell004Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell004Node05 TraceData.positiveChordBox1005Cell004Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell004Node06 TraceData.positiveChordBox1005Cell004Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell004Node07 TraceData.positiveChordBox1005Cell004Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell004Node08 TraceData.positiveChordBox1005Cell004Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell004Node09 TraceData.positiveChordBox1005Cell004Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell004Node10 TraceData.positiveChordBox1005Cell004Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell004Node11 TraceData.positiveChordBox1005Cell004Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell004Node12 TraceData.positiveChordBox1005Cell004Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell004Node13 TraceData.positiveChordBox1005Cell004Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell004Node14 TraceData.positiveChordBox1005Cell004Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell004Node15 TraceData.positiveChordBox1005Cell004Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell004Node16 TraceData.positiveChordBox1005Cell004Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell004Node17 TraceData.positiveChordBox1005Cell004Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell004Node18 TraceData.positiveChordBox1005Cell004Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell004Node19 TraceData.positiveChordBox1005Cell004Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell004Node20 TraceData.positiveChordBox1005Cell004Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell004Node21 TraceData.positiveChordBox1005Cell004Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell004Node22 TraceData.positiveChordBox1005Cell004Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell004Node23 TraceData.positiveChordBox1005Cell004Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell004Node24 TraceData.positiveChordBox1005Cell004Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell004Node25 TraceData.positiveChordBox1005Cell004Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell004Node26 TraceData.positiveChordBox1005Cell004Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell004Node27 TraceData.positiveChordBox1005Cell004Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell004Node28 TraceData.positiveChordBox1005Cell004Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell004Node29 TraceData.positiveChordBox1005Cell004Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell004Node30 TraceData.positiveChordBox1005Cell004Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell004.center (1/8192) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell004Node31 TraceData.positiveChordBox1005Cell004Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell005 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell005.interpret
theorem positiveChordBox1005Cell005_valid : positiveChordBox1005Cell005.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-4093/4096) (1/4096) (1/2048) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.disk TraceData.positiveChordBox1005Cell005.diskFunction TraceData.positiveChordBox1005Cell005Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell005Node00 TraceData.positiveChordBox1005Cell005Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell005Node01 TraceData.positiveChordBox1005Cell005Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell005Node02 TraceData.positiveChordBox1005Cell005Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell005Node03 TraceData.positiveChordBox1005Cell005Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell005Node04 TraceData.positiveChordBox1005Cell005Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell005Node05 TraceData.positiveChordBox1005Cell005Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell005Node06 TraceData.positiveChordBox1005Cell005Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell005Node07 TraceData.positiveChordBox1005Cell005Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell005Node08 TraceData.positiveChordBox1005Cell005Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell005Node09 TraceData.positiveChordBox1005Cell005Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell005Node10 TraceData.positiveChordBox1005Cell005Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell005Node11 TraceData.positiveChordBox1005Cell005Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell005Node12 TraceData.positiveChordBox1005Cell005Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell005Node13 TraceData.positiveChordBox1005Cell005Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell005Node14 TraceData.positiveChordBox1005Cell005Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell005Node15 TraceData.positiveChordBox1005Cell005Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell005Node16 TraceData.positiveChordBox1005Cell005Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell005Node17 TraceData.positiveChordBox1005Cell005Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell005Node18 TraceData.positiveChordBox1005Cell005Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell005Node19 TraceData.positiveChordBox1005Cell005Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell005Node20 TraceData.positiveChordBox1005Cell005Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell005Node21 TraceData.positiveChordBox1005Cell005Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell005Node22 TraceData.positiveChordBox1005Cell005Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell005Node23 TraceData.positiveChordBox1005Cell005Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell005Node24 TraceData.positiveChordBox1005Cell005Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell005Node25 TraceData.positiveChordBox1005Cell005Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell005Node26 TraceData.positiveChordBox1005Cell005Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell005Node27 TraceData.positiveChordBox1005Cell005Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell005Node28 TraceData.positiveChordBox1005Cell005Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell005Node29 TraceData.positiveChordBox1005Cell005Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell005Node30 TraceData.positiveChordBox1005Cell005Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell005.center (1/4096) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell005Node31 TraceData.positiveChordBox1005Cell005Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell006 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell006.interpret
theorem positiveChordBox1005Cell006_valid : positiveChordBox1005Cell006.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-2045/2048) (1/2048) (1/1024) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.disk TraceData.positiveChordBox1005Cell006.diskFunction TraceData.positiveChordBox1005Cell006Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell006Node00 TraceData.positiveChordBox1005Cell006Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell006Node01 TraceData.positiveChordBox1005Cell006Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell006Node02 TraceData.positiveChordBox1005Cell006Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell006Node03 TraceData.positiveChordBox1005Cell006Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell006Node04 TraceData.positiveChordBox1005Cell006Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell006Node05 TraceData.positiveChordBox1005Cell006Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell006Node06 TraceData.positiveChordBox1005Cell006Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell006Node07 TraceData.positiveChordBox1005Cell006Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell006Node08 TraceData.positiveChordBox1005Cell006Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell006Node09 TraceData.positiveChordBox1005Cell006Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell006Node10 TraceData.positiveChordBox1005Cell006Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell006Node11 TraceData.positiveChordBox1005Cell006Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell006Node12 TraceData.positiveChordBox1005Cell006Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell006Node13 TraceData.positiveChordBox1005Cell006Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell006Node14 TraceData.positiveChordBox1005Cell006Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell006Node15 TraceData.positiveChordBox1005Cell006Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell006Node16 TraceData.positiveChordBox1005Cell006Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell006Node17 TraceData.positiveChordBox1005Cell006Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell006Node18 TraceData.positiveChordBox1005Cell006Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell006Node19 TraceData.positiveChordBox1005Cell006Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell006Node20 TraceData.positiveChordBox1005Cell006Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell006Node21 TraceData.positiveChordBox1005Cell006Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell006Node22 TraceData.positiveChordBox1005Cell006Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell006Node23 TraceData.positiveChordBox1005Cell006Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell006Node24 TraceData.positiveChordBox1005Cell006Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell006Node25 TraceData.positiveChordBox1005Cell006Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell006Node26 TraceData.positiveChordBox1005Cell006Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell006Node27 TraceData.positiveChordBox1005Cell006Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell006Node28 TraceData.positiveChordBox1005Cell006Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell006Node29 TraceData.positiveChordBox1005Cell006Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell006Node30 TraceData.positiveChordBox1005Cell006Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell006.center (1/2048) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell006Node31 TraceData.positiveChordBox1005Cell006Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell007 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell007.interpret
theorem positiveChordBox1005Cell007_valid : positiveChordBox1005Cell007.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-1021/1024) (1/1024) (1/512) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.disk TraceData.positiveChordBox1005Cell007.diskFunction TraceData.positiveChordBox1005Cell007Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell007Node00 TraceData.positiveChordBox1005Cell007Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell007Node01 TraceData.positiveChordBox1005Cell007Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell007Node02 TraceData.positiveChordBox1005Cell007Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell007Node03 TraceData.positiveChordBox1005Cell007Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell007Node04 TraceData.positiveChordBox1005Cell007Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell007Node05 TraceData.positiveChordBox1005Cell007Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell007Node06 TraceData.positiveChordBox1005Cell007Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell007Node07 TraceData.positiveChordBox1005Cell007Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell007Node08 TraceData.positiveChordBox1005Cell007Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell007Node09 TraceData.positiveChordBox1005Cell007Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell007Node10 TraceData.positiveChordBox1005Cell007Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell007Node11 TraceData.positiveChordBox1005Cell007Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell007Node12 TraceData.positiveChordBox1005Cell007Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell007Node13 TraceData.positiveChordBox1005Cell007Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell007Node14 TraceData.positiveChordBox1005Cell007Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell007Node15 TraceData.positiveChordBox1005Cell007Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell007Node16 TraceData.positiveChordBox1005Cell007Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell007Node17 TraceData.positiveChordBox1005Cell007Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell007Node18 TraceData.positiveChordBox1005Cell007Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell007Node19 TraceData.positiveChordBox1005Cell007Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell007Node20 TraceData.positiveChordBox1005Cell007Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell007Node21 TraceData.positiveChordBox1005Cell007Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell007Node22 TraceData.positiveChordBox1005Cell007Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell007Node23 TraceData.positiveChordBox1005Cell007Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell007Node24 TraceData.positiveChordBox1005Cell007Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell007Node25 TraceData.positiveChordBox1005Cell007Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell007Node26 TraceData.positiveChordBox1005Cell007Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell007Node27 TraceData.positiveChordBox1005Cell007Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell007Node28 TraceData.positiveChordBox1005Cell007Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell007Node29 TraceData.positiveChordBox1005Cell007Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell007Node30 TraceData.positiveChordBox1005Cell007Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell007.center (1/1024) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell007Node31 TraceData.positiveChordBox1005Cell007Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell008 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell008.interpret
theorem positiveChordBox1005Cell008_valid : positiveChordBox1005Cell008.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-509/512) (1/512) (1/256) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.disk TraceData.positiveChordBox1005Cell008.diskFunction TraceData.positiveChordBox1005Cell008Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell008Node00 TraceData.positiveChordBox1005Cell008Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell008Node01 TraceData.positiveChordBox1005Cell008Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell008Node02 TraceData.positiveChordBox1005Cell008Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell008Node03 TraceData.positiveChordBox1005Cell008Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell008Node04 TraceData.positiveChordBox1005Cell008Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell008Node05 TraceData.positiveChordBox1005Cell008Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell008Node06 TraceData.positiveChordBox1005Cell008Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell008Node07 TraceData.positiveChordBox1005Cell008Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell008Node08 TraceData.positiveChordBox1005Cell008Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell008Node09 TraceData.positiveChordBox1005Cell008Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell008Node10 TraceData.positiveChordBox1005Cell008Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell008Node11 TraceData.positiveChordBox1005Cell008Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell008Node12 TraceData.positiveChordBox1005Cell008Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell008Node13 TraceData.positiveChordBox1005Cell008Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell008Node14 TraceData.positiveChordBox1005Cell008Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell008Node15 TraceData.positiveChordBox1005Cell008Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell008Node16 TraceData.positiveChordBox1005Cell008Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell008Node17 TraceData.positiveChordBox1005Cell008Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell008Node18 TraceData.positiveChordBox1005Cell008Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell008Node19 TraceData.positiveChordBox1005Cell008Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell008Node20 TraceData.positiveChordBox1005Cell008Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell008Node21 TraceData.positiveChordBox1005Cell008Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell008Node22 TraceData.positiveChordBox1005Cell008Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell008Node23 TraceData.positiveChordBox1005Cell008Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell008Node24 TraceData.positiveChordBox1005Cell008Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell008Node25 TraceData.positiveChordBox1005Cell008Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell008Node26 TraceData.positiveChordBox1005Cell008Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell008Node27 TraceData.positiveChordBox1005Cell008Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell008Node28 TraceData.positiveChordBox1005Cell008Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell008Node29 TraceData.positiveChordBox1005Cell008Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell008Node30 TraceData.positiveChordBox1005Cell008Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell008.center (1/512) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell008Node31 TraceData.positiveChordBox1005Cell008Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell009 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell009.interpret
theorem positiveChordBox1005Cell009_valid : positiveChordBox1005Cell009.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-253/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.disk TraceData.positiveChordBox1005Cell009.diskFunction TraceData.positiveChordBox1005Cell009Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell009Node00 TraceData.positiveChordBox1005Cell009Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell009Node01 TraceData.positiveChordBox1005Cell009Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell009Node02 TraceData.positiveChordBox1005Cell009Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell009Node03 TraceData.positiveChordBox1005Cell009Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell009Node04 TraceData.positiveChordBox1005Cell009Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell009Node05 TraceData.positiveChordBox1005Cell009Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell009Node06 TraceData.positiveChordBox1005Cell009Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell009Node07 TraceData.positiveChordBox1005Cell009Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell009Node08 TraceData.positiveChordBox1005Cell009Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell009Node09 TraceData.positiveChordBox1005Cell009Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell009Node10 TraceData.positiveChordBox1005Cell009Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell009Node11 TraceData.positiveChordBox1005Cell009Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell009Node12 TraceData.positiveChordBox1005Cell009Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell009Node13 TraceData.positiveChordBox1005Cell009Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell009Node14 TraceData.positiveChordBox1005Cell009Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell009Node15 TraceData.positiveChordBox1005Cell009Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell009Node16 TraceData.positiveChordBox1005Cell009Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell009Node17 TraceData.positiveChordBox1005Cell009Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell009Node18 TraceData.positiveChordBox1005Cell009Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell009Node19 TraceData.positiveChordBox1005Cell009Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell009Node20 TraceData.positiveChordBox1005Cell009Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell009Node21 TraceData.positiveChordBox1005Cell009Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell009Node22 TraceData.positiveChordBox1005Cell009Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell009Node23 TraceData.positiveChordBox1005Cell009Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell009Node24 TraceData.positiveChordBox1005Cell009Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell009Node25 TraceData.positiveChordBox1005Cell009Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell009Node26 TraceData.positiveChordBox1005Cell009Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell009Node27 TraceData.positiveChordBox1005Cell009Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell009Node28 TraceData.positiveChordBox1005Cell009Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell009Node29 TraceData.positiveChordBox1005Cell009Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell009Node30 TraceData.positiveChordBox1005Cell009Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell009.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell009Node31 TraceData.positiveChordBox1005Cell009Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell010 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell010.interpret
theorem positiveChordBox1005Cell010_valid : positiveChordBox1005Cell010.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-125/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.disk TraceData.positiveChordBox1005Cell010.diskFunction TraceData.positiveChordBox1005Cell010Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell010Node00 TraceData.positiveChordBox1005Cell010Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell010Node01 TraceData.positiveChordBox1005Cell010Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell010Node02 TraceData.positiveChordBox1005Cell010Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell010Node03 TraceData.positiveChordBox1005Cell010Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell010Node04 TraceData.positiveChordBox1005Cell010Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell010Node05 TraceData.positiveChordBox1005Cell010Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell010Node06 TraceData.positiveChordBox1005Cell010Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell010Node07 TraceData.positiveChordBox1005Cell010Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell010Node08 TraceData.positiveChordBox1005Cell010Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell010Node09 TraceData.positiveChordBox1005Cell010Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell010Node10 TraceData.positiveChordBox1005Cell010Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell010Node11 TraceData.positiveChordBox1005Cell010Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell010Node12 TraceData.positiveChordBox1005Cell010Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell010Node13 TraceData.positiveChordBox1005Cell010Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell010Node14 TraceData.positiveChordBox1005Cell010Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell010Node15 TraceData.positiveChordBox1005Cell010Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell010Node16 TraceData.positiveChordBox1005Cell010Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell010Node17 TraceData.positiveChordBox1005Cell010Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell010Node18 TraceData.positiveChordBox1005Cell010Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell010Node19 TraceData.positiveChordBox1005Cell010Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell010Node20 TraceData.positiveChordBox1005Cell010Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell010Node21 TraceData.positiveChordBox1005Cell010Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell010Node22 TraceData.positiveChordBox1005Cell010Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell010Node23 TraceData.positiveChordBox1005Cell010Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell010Node24 TraceData.positiveChordBox1005Cell010Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell010Node25 TraceData.positiveChordBox1005Cell010Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell010Node26 TraceData.positiveChordBox1005Cell010Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell010Node27 TraceData.positiveChordBox1005Cell010Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell010Node28 TraceData.positiveChordBox1005Cell010Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell010Node29 TraceData.positiveChordBox1005Cell010Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell010Node30 TraceData.positiveChordBox1005Cell010Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell010.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell010Node31 TraceData.positiveChordBox1005Cell010Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell011 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell011.interpret
theorem positiveChordBox1005Cell011_valid : positiveChordBox1005Cell011.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-61/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.disk TraceData.positiveChordBox1005Cell011.diskFunction TraceData.positiveChordBox1005Cell011Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell011Node00 TraceData.positiveChordBox1005Cell011Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell011Node01 TraceData.positiveChordBox1005Cell011Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell011Node02 TraceData.positiveChordBox1005Cell011Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell011Node03 TraceData.positiveChordBox1005Cell011Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell011Node04 TraceData.positiveChordBox1005Cell011Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell011Node05 TraceData.positiveChordBox1005Cell011Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell011Node06 TraceData.positiveChordBox1005Cell011Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell011Node07 TraceData.positiveChordBox1005Cell011Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell011Node08 TraceData.positiveChordBox1005Cell011Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell011Node09 TraceData.positiveChordBox1005Cell011Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell011Node10 TraceData.positiveChordBox1005Cell011Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell011Node11 TraceData.positiveChordBox1005Cell011Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell011Node12 TraceData.positiveChordBox1005Cell011Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell011Node13 TraceData.positiveChordBox1005Cell011Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell011Node14 TraceData.positiveChordBox1005Cell011Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell011Node15 TraceData.positiveChordBox1005Cell011Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell011Node16 TraceData.positiveChordBox1005Cell011Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell011Node17 TraceData.positiveChordBox1005Cell011Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell011Node18 TraceData.positiveChordBox1005Cell011Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell011Node19 TraceData.positiveChordBox1005Cell011Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell011Node20 TraceData.positiveChordBox1005Cell011Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell011Node21 TraceData.positiveChordBox1005Cell011Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell011Node22 TraceData.positiveChordBox1005Cell011Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell011Node23 TraceData.positiveChordBox1005Cell011Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell011Node24 TraceData.positiveChordBox1005Cell011Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell011Node25 TraceData.positiveChordBox1005Cell011Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell011Node26 TraceData.positiveChordBox1005Cell011Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell011Node27 TraceData.positiveChordBox1005Cell011Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell011Node28 TraceData.positiveChordBox1005Cell011Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell011Node29 TraceData.positiveChordBox1005Cell011Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell011Node30 TraceData.positiveChordBox1005Cell011Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell011Node31 TraceData.positiveChordBox1005Cell011Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell012 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell012.interpret
theorem positiveChordBox1005Cell012_valid : positiveChordBox1005Cell012.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-29/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.disk TraceData.positiveChordBox1005Cell012.diskFunction TraceData.positiveChordBox1005Cell012Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell012Node00 TraceData.positiveChordBox1005Cell012Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell012Node01 TraceData.positiveChordBox1005Cell012Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell012Node02 TraceData.positiveChordBox1005Cell012Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell012Node03 TraceData.positiveChordBox1005Cell012Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell012Node04 TraceData.positiveChordBox1005Cell012Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell012Node05 TraceData.positiveChordBox1005Cell012Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell012Node06 TraceData.positiveChordBox1005Cell012Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell012Node07 TraceData.positiveChordBox1005Cell012Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell012Node08 TraceData.positiveChordBox1005Cell012Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell012Node09 TraceData.positiveChordBox1005Cell012Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell012Node10 TraceData.positiveChordBox1005Cell012Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell012Node11 TraceData.positiveChordBox1005Cell012Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell012Node12 TraceData.positiveChordBox1005Cell012Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell012Node13 TraceData.positiveChordBox1005Cell012Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell012Node14 TraceData.positiveChordBox1005Cell012Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell012Node15 TraceData.positiveChordBox1005Cell012Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell012Node16 TraceData.positiveChordBox1005Cell012Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell012Node17 TraceData.positiveChordBox1005Cell012Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell012Node18 TraceData.positiveChordBox1005Cell012Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell012Node19 TraceData.positiveChordBox1005Cell012Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell012Node20 TraceData.positiveChordBox1005Cell012Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell012Node21 TraceData.positiveChordBox1005Cell012Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell012Node22 TraceData.positiveChordBox1005Cell012Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell012Node23 TraceData.positiveChordBox1005Cell012Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell012Node24 TraceData.positiveChordBox1005Cell012Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell012Node25 TraceData.positiveChordBox1005Cell012Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell012Node26 TraceData.positiveChordBox1005Cell012Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell012Node27 TraceData.positiveChordBox1005Cell012Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell012Node28 TraceData.positiveChordBox1005Cell012Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell012Node29 TraceData.positiveChordBox1005Cell012Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell012Node30 TraceData.positiveChordBox1005Cell012Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell012Node31 TraceData.positiveChordBox1005Cell012Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell013 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell013.interpret
theorem positiveChordBox1005Cell013_valid : positiveChordBox1005Cell013.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-13/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.disk TraceData.positiveChordBox1005Cell013.diskFunction TraceData.positiveChordBox1005Cell013Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell013Node00 TraceData.positiveChordBox1005Cell013Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell013Node01 TraceData.positiveChordBox1005Cell013Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell013Node02 TraceData.positiveChordBox1005Cell013Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell013Node03 TraceData.positiveChordBox1005Cell013Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell013Node04 TraceData.positiveChordBox1005Cell013Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell013Node05 TraceData.positiveChordBox1005Cell013Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell013Node06 TraceData.positiveChordBox1005Cell013Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell013Node07 TraceData.positiveChordBox1005Cell013Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell013Node08 TraceData.positiveChordBox1005Cell013Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell013Node09 TraceData.positiveChordBox1005Cell013Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell013Node10 TraceData.positiveChordBox1005Cell013Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell013Node11 TraceData.positiveChordBox1005Cell013Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell013Node12 TraceData.positiveChordBox1005Cell013Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell013Node13 TraceData.positiveChordBox1005Cell013Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell013Node14 TraceData.positiveChordBox1005Cell013Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell013Node15 TraceData.positiveChordBox1005Cell013Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell013Node16 TraceData.positiveChordBox1005Cell013Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell013Node17 TraceData.positiveChordBox1005Cell013Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell013Node18 TraceData.positiveChordBox1005Cell013Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell013Node19 TraceData.positiveChordBox1005Cell013Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell013Node20 TraceData.positiveChordBox1005Cell013Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell013Node21 TraceData.positiveChordBox1005Cell013Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell013Node22 TraceData.positiveChordBox1005Cell013Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell013Node23 TraceData.positiveChordBox1005Cell013Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell013Node24 TraceData.positiveChordBox1005Cell013Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell013Node25 TraceData.positiveChordBox1005Cell013Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell013Node26 TraceData.positiveChordBox1005Cell013Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell013Node27 TraceData.positiveChordBox1005Cell013Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell013Node28 TraceData.positiveChordBox1005Cell013Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell013Node29 TraceData.positiveChordBox1005Cell013Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell013Node30 TraceData.positiveChordBox1005Cell013Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell013.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell013Node31 TraceData.positiveChordBox1005Cell013Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell014 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell014.interpret
theorem positiveChordBox1005Cell014_valid : positiveChordBox1005Cell014.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-5/8) (1/8) (1/4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.disk TraceData.positiveChordBox1005Cell014.diskFunction TraceData.positiveChordBox1005Cell014Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell014Node00 TraceData.positiveChordBox1005Cell014Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell014Node01 TraceData.positiveChordBox1005Cell014Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell014Node02 TraceData.positiveChordBox1005Cell014Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell014Node03 TraceData.positiveChordBox1005Cell014Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell014Node04 TraceData.positiveChordBox1005Cell014Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell014Node05 TraceData.positiveChordBox1005Cell014Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell014Node06 TraceData.positiveChordBox1005Cell014Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell014Node07 TraceData.positiveChordBox1005Cell014Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell014Node08 TraceData.positiveChordBox1005Cell014Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell014Node09 TraceData.positiveChordBox1005Cell014Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell014Node10 TraceData.positiveChordBox1005Cell014Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell014Node11 TraceData.positiveChordBox1005Cell014Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell014Node12 TraceData.positiveChordBox1005Cell014Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell014Node13 TraceData.positiveChordBox1005Cell014Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell014Node14 TraceData.positiveChordBox1005Cell014Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell014Node15 TraceData.positiveChordBox1005Cell014Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell014Node16 TraceData.positiveChordBox1005Cell014Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell014Node17 TraceData.positiveChordBox1005Cell014Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell014Node18 TraceData.positiveChordBox1005Cell014Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell014Node19 TraceData.positiveChordBox1005Cell014Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell014Node20 TraceData.positiveChordBox1005Cell014Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell014Node21 TraceData.positiveChordBox1005Cell014Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell014Node22 TraceData.positiveChordBox1005Cell014Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell014Node23 TraceData.positiveChordBox1005Cell014Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell014Node24 TraceData.positiveChordBox1005Cell014Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell014Node25 TraceData.positiveChordBox1005Cell014Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell014Node26 TraceData.positiveChordBox1005Cell014Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell014Node27 TraceData.positiveChordBox1005Cell014Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell014Node28 TraceData.positiveChordBox1005Cell014Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell014Node29 TraceData.positiveChordBox1005Cell014Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell014Node30 TraceData.positiveChordBox1005Cell014Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell014.center (1/8) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell014Node31 TraceData.positiveChordBox1005Cell014Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell015 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell015.interpret
theorem positiveChordBox1005Cell015_valid : positiveChordBox1005Cell015.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (-1/4) (1/4) (1/2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.disk TraceData.positiveChordBox1005Cell015.diskFunction TraceData.positiveChordBox1005Cell015Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell015Node00 TraceData.positiveChordBox1005Cell015Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell015Node01 TraceData.positiveChordBox1005Cell015Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell015Node02 TraceData.positiveChordBox1005Cell015Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell015Node03 TraceData.positiveChordBox1005Cell015Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell015Node04 TraceData.positiveChordBox1005Cell015Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell015Node05 TraceData.positiveChordBox1005Cell015Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell015Node06 TraceData.positiveChordBox1005Cell015Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell015Node07 TraceData.positiveChordBox1005Cell015Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell015Node08 TraceData.positiveChordBox1005Cell015Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell015Node09 TraceData.positiveChordBox1005Cell015Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell015Node10 TraceData.positiveChordBox1005Cell015Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell015Node11 TraceData.positiveChordBox1005Cell015Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell015Node12 TraceData.positiveChordBox1005Cell015Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell015Node13 TraceData.positiveChordBox1005Cell015Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell015Node14 TraceData.positiveChordBox1005Cell015Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell015Node15 TraceData.positiveChordBox1005Cell015Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell015Node16 TraceData.positiveChordBox1005Cell015Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell015Node17 TraceData.positiveChordBox1005Cell015Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell015Node18 TraceData.positiveChordBox1005Cell015Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell015Node19 TraceData.positiveChordBox1005Cell015Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell015Node20 TraceData.positiveChordBox1005Cell015Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell015Node21 TraceData.positiveChordBox1005Cell015Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell015Node22 TraceData.positiveChordBox1005Cell015Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell015Node23 TraceData.positiveChordBox1005Cell015Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell015Node24 TraceData.positiveChordBox1005Cell015Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell015Node25 TraceData.positiveChordBox1005Cell015Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell015Node26 TraceData.positiveChordBox1005Cell015Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell015Node27 TraceData.positiveChordBox1005Cell015Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell015Node28 TraceData.positiveChordBox1005Cell015Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell015Node29 TraceData.positiveChordBox1005Cell015Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell015Node30 TraceData.positiveChordBox1005Cell015Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell015.center (1/4) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell015Node31 TraceData.positiveChordBox1005Cell015Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell016 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell016.interpret
theorem positiveChordBox1005Cell016_valid : positiveChordBox1005Cell016.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (1/4) (1/4) (1/2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.disk TraceData.positiveChordBox1005Cell016.diskFunction TraceData.positiveChordBox1005Cell016Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell016Node00 TraceData.positiveChordBox1005Cell016Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell016Node01 TraceData.positiveChordBox1005Cell016Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell016Node02 TraceData.positiveChordBox1005Cell016Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell016Node03 TraceData.positiveChordBox1005Cell016Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell016Node04 TraceData.positiveChordBox1005Cell016Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell016Node05 TraceData.positiveChordBox1005Cell016Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell016Node06 TraceData.positiveChordBox1005Cell016Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell016Node07 TraceData.positiveChordBox1005Cell016Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell016Node08 TraceData.positiveChordBox1005Cell016Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell016Node09 TraceData.positiveChordBox1005Cell016Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell016Node10 TraceData.positiveChordBox1005Cell016Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell016Node11 TraceData.positiveChordBox1005Cell016Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell016Node12 TraceData.positiveChordBox1005Cell016Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell016Node13 TraceData.positiveChordBox1005Cell016Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell016Node14 TraceData.positiveChordBox1005Cell016Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell016Node15 TraceData.positiveChordBox1005Cell016Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell016Node16 TraceData.positiveChordBox1005Cell016Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell016Node17 TraceData.positiveChordBox1005Cell016Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell016Node18 TraceData.positiveChordBox1005Cell016Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell016Node19 TraceData.positiveChordBox1005Cell016Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell016Node20 TraceData.positiveChordBox1005Cell016Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell016Node21 TraceData.positiveChordBox1005Cell016Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell016Node22 TraceData.positiveChordBox1005Cell016Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell016Node23 TraceData.positiveChordBox1005Cell016Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell016Node24 TraceData.positiveChordBox1005Cell016Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell016Node25 TraceData.positiveChordBox1005Cell016Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell016Node26 TraceData.positiveChordBox1005Cell016Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell016Node27 TraceData.positiveChordBox1005Cell016Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell016Node28 TraceData.positiveChordBox1005Cell016Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell016Node29 TraceData.positiveChordBox1005Cell016Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell016Node30 TraceData.positiveChordBox1005Cell016Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell016.center (1/4) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell016Node31 TraceData.positiveChordBox1005Cell016Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell017 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell017.interpret
theorem positiveChordBox1005Cell017_valid : positiveChordBox1005Cell017.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (5/8) (1/8) (1/4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.disk TraceData.positiveChordBox1005Cell017.diskFunction TraceData.positiveChordBox1005Cell017Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell017Node00 TraceData.positiveChordBox1005Cell017Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell017Node01 TraceData.positiveChordBox1005Cell017Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell017Node02 TraceData.positiveChordBox1005Cell017Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell017Node03 TraceData.positiveChordBox1005Cell017Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell017Node04 TraceData.positiveChordBox1005Cell017Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell017Node05 TraceData.positiveChordBox1005Cell017Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell017Node06 TraceData.positiveChordBox1005Cell017Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell017Node07 TraceData.positiveChordBox1005Cell017Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell017Node08 TraceData.positiveChordBox1005Cell017Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell017Node09 TraceData.positiveChordBox1005Cell017Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell017Node10 TraceData.positiveChordBox1005Cell017Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell017Node11 TraceData.positiveChordBox1005Cell017Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell017Node12 TraceData.positiveChordBox1005Cell017Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell017Node13 TraceData.positiveChordBox1005Cell017Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell017Node14 TraceData.positiveChordBox1005Cell017Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell017Node15 TraceData.positiveChordBox1005Cell017Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell017Node16 TraceData.positiveChordBox1005Cell017Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell017Node17 TraceData.positiveChordBox1005Cell017Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell017Node18 TraceData.positiveChordBox1005Cell017Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell017Node19 TraceData.positiveChordBox1005Cell017Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell017Node20 TraceData.positiveChordBox1005Cell017Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell017Node21 TraceData.positiveChordBox1005Cell017Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell017Node22 TraceData.positiveChordBox1005Cell017Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell017Node23 TraceData.positiveChordBox1005Cell017Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell017Node24 TraceData.positiveChordBox1005Cell017Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell017Node25 TraceData.positiveChordBox1005Cell017Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell017Node26 TraceData.positiveChordBox1005Cell017Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell017Node27 TraceData.positiveChordBox1005Cell017Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell017Node28 TraceData.positiveChordBox1005Cell017Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell017Node29 TraceData.positiveChordBox1005Cell017Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell017Node30 TraceData.positiveChordBox1005Cell017Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell017.center (1/8) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell017Node31 TraceData.positiveChordBox1005Cell017Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell018 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell018.interpret
theorem positiveChordBox1005Cell018_valid : positiveChordBox1005Cell018.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (13/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.disk TraceData.positiveChordBox1005Cell018.diskFunction TraceData.positiveChordBox1005Cell018Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell018Node00 TraceData.positiveChordBox1005Cell018Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell018Node01 TraceData.positiveChordBox1005Cell018Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell018Node02 TraceData.positiveChordBox1005Cell018Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell018Node03 TraceData.positiveChordBox1005Cell018Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell018Node04 TraceData.positiveChordBox1005Cell018Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell018Node05 TraceData.positiveChordBox1005Cell018Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell018Node06 TraceData.positiveChordBox1005Cell018Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell018Node07 TraceData.positiveChordBox1005Cell018Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell018Node08 TraceData.positiveChordBox1005Cell018Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell018Node09 TraceData.positiveChordBox1005Cell018Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell018Node10 TraceData.positiveChordBox1005Cell018Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell018Node11 TraceData.positiveChordBox1005Cell018Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell018Node12 TraceData.positiveChordBox1005Cell018Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell018Node13 TraceData.positiveChordBox1005Cell018Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell018Node14 TraceData.positiveChordBox1005Cell018Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell018Node15 TraceData.positiveChordBox1005Cell018Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell018Node16 TraceData.positiveChordBox1005Cell018Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell018Node17 TraceData.positiveChordBox1005Cell018Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell018Node18 TraceData.positiveChordBox1005Cell018Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell018Node19 TraceData.positiveChordBox1005Cell018Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell018Node20 TraceData.positiveChordBox1005Cell018Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell018Node21 TraceData.positiveChordBox1005Cell018Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell018Node22 TraceData.positiveChordBox1005Cell018Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell018Node23 TraceData.positiveChordBox1005Cell018Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell018Node24 TraceData.positiveChordBox1005Cell018Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell018Node25 TraceData.positiveChordBox1005Cell018Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell018Node26 TraceData.positiveChordBox1005Cell018Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell018Node27 TraceData.positiveChordBox1005Cell018Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell018Node28 TraceData.positiveChordBox1005Cell018Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell018Node29 TraceData.positiveChordBox1005Cell018Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell018Node30 TraceData.positiveChordBox1005Cell018Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell018.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell018Node31 TraceData.positiveChordBox1005Cell018Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell019 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell019.interpret
theorem positiveChordBox1005Cell019_valid : positiveChordBox1005Cell019.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (29/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.disk TraceData.positiveChordBox1005Cell019.diskFunction TraceData.positiveChordBox1005Cell019Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell019Node00 TraceData.positiveChordBox1005Cell019Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell019Node01 TraceData.positiveChordBox1005Cell019Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell019Node02 TraceData.positiveChordBox1005Cell019Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell019Node03 TraceData.positiveChordBox1005Cell019Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell019Node04 TraceData.positiveChordBox1005Cell019Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell019Node05 TraceData.positiveChordBox1005Cell019Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell019Node06 TraceData.positiveChordBox1005Cell019Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell019Node07 TraceData.positiveChordBox1005Cell019Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell019Node08 TraceData.positiveChordBox1005Cell019Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell019Node09 TraceData.positiveChordBox1005Cell019Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell019Node10 TraceData.positiveChordBox1005Cell019Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell019Node11 TraceData.positiveChordBox1005Cell019Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell019Node12 TraceData.positiveChordBox1005Cell019Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell019Node13 TraceData.positiveChordBox1005Cell019Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell019Node14 TraceData.positiveChordBox1005Cell019Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell019Node15 TraceData.positiveChordBox1005Cell019Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell019Node16 TraceData.positiveChordBox1005Cell019Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell019Node17 TraceData.positiveChordBox1005Cell019Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell019Node18 TraceData.positiveChordBox1005Cell019Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell019Node19 TraceData.positiveChordBox1005Cell019Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell019Node20 TraceData.positiveChordBox1005Cell019Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell019Node21 TraceData.positiveChordBox1005Cell019Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell019Node22 TraceData.positiveChordBox1005Cell019Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell019Node23 TraceData.positiveChordBox1005Cell019Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell019Node24 TraceData.positiveChordBox1005Cell019Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell019Node25 TraceData.positiveChordBox1005Cell019Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell019Node26 TraceData.positiveChordBox1005Cell019Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell019Node27 TraceData.positiveChordBox1005Cell019Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell019Node28 TraceData.positiveChordBox1005Cell019Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell019Node29 TraceData.positiveChordBox1005Cell019Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell019Node30 TraceData.positiveChordBox1005Cell019Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell019.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell019Node31 TraceData.positiveChordBox1005Cell019Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell020 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell020.interpret
theorem positiveChordBox1005Cell020_valid : positiveChordBox1005Cell020.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (61/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.disk TraceData.positiveChordBox1005Cell020.diskFunction TraceData.positiveChordBox1005Cell020Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell020Node00 TraceData.positiveChordBox1005Cell020Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell020Node01 TraceData.positiveChordBox1005Cell020Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell020Node02 TraceData.positiveChordBox1005Cell020Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell020Node03 TraceData.positiveChordBox1005Cell020Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell020Node04 TraceData.positiveChordBox1005Cell020Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell020Node05 TraceData.positiveChordBox1005Cell020Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell020Node06 TraceData.positiveChordBox1005Cell020Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell020Node07 TraceData.positiveChordBox1005Cell020Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell020Node08 TraceData.positiveChordBox1005Cell020Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell020Node09 TraceData.positiveChordBox1005Cell020Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell020Node10 TraceData.positiveChordBox1005Cell020Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell020Node11 TraceData.positiveChordBox1005Cell020Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell020Node12 TraceData.positiveChordBox1005Cell020Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell020Node13 TraceData.positiveChordBox1005Cell020Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell020Node14 TraceData.positiveChordBox1005Cell020Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell020Node15 TraceData.positiveChordBox1005Cell020Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell020Node16 TraceData.positiveChordBox1005Cell020Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell020Node17 TraceData.positiveChordBox1005Cell020Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell020Node18 TraceData.positiveChordBox1005Cell020Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell020Node19 TraceData.positiveChordBox1005Cell020Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell020Node20 TraceData.positiveChordBox1005Cell020Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell020Node21 TraceData.positiveChordBox1005Cell020Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell020Node22 TraceData.positiveChordBox1005Cell020Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell020Node23 TraceData.positiveChordBox1005Cell020Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell020Node24 TraceData.positiveChordBox1005Cell020Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell020Node25 TraceData.positiveChordBox1005Cell020Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell020Node26 TraceData.positiveChordBox1005Cell020Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell020Node27 TraceData.positiveChordBox1005Cell020Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell020Node28 TraceData.positiveChordBox1005Cell020Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell020Node29 TraceData.positiveChordBox1005Cell020Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell020Node30 TraceData.positiveChordBox1005Cell020Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell020.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell020Node31 TraceData.positiveChordBox1005Cell020Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell021 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell021.interpret
theorem positiveChordBox1005Cell021_valid : positiveChordBox1005Cell021.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (125/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.disk TraceData.positiveChordBox1005Cell021.diskFunction TraceData.positiveChordBox1005Cell021Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell021Node00 TraceData.positiveChordBox1005Cell021Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell021Node01 TraceData.positiveChordBox1005Cell021Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell021Node02 TraceData.positiveChordBox1005Cell021Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell021Node03 TraceData.positiveChordBox1005Cell021Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell021Node04 TraceData.positiveChordBox1005Cell021Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell021Node05 TraceData.positiveChordBox1005Cell021Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell021Node06 TraceData.positiveChordBox1005Cell021Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell021Node07 TraceData.positiveChordBox1005Cell021Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell021Node08 TraceData.positiveChordBox1005Cell021Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell021Node09 TraceData.positiveChordBox1005Cell021Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell021Node10 TraceData.positiveChordBox1005Cell021Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell021Node11 TraceData.positiveChordBox1005Cell021Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell021Node12 TraceData.positiveChordBox1005Cell021Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell021Node13 TraceData.positiveChordBox1005Cell021Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell021Node14 TraceData.positiveChordBox1005Cell021Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell021Node15 TraceData.positiveChordBox1005Cell021Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell021Node16 TraceData.positiveChordBox1005Cell021Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell021Node17 TraceData.positiveChordBox1005Cell021Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell021Node18 TraceData.positiveChordBox1005Cell021Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell021Node19 TraceData.positiveChordBox1005Cell021Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell021Node20 TraceData.positiveChordBox1005Cell021Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell021Node21 TraceData.positiveChordBox1005Cell021Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell021Node22 TraceData.positiveChordBox1005Cell021Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell021Node23 TraceData.positiveChordBox1005Cell021Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell021Node24 TraceData.positiveChordBox1005Cell021Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell021Node25 TraceData.positiveChordBox1005Cell021Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell021Node26 TraceData.positiveChordBox1005Cell021Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell021Node27 TraceData.positiveChordBox1005Cell021Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell021Node28 TraceData.positiveChordBox1005Cell021Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell021Node29 TraceData.positiveChordBox1005Cell021Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell021Node30 TraceData.positiveChordBox1005Cell021Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell021.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell021Node31 TraceData.positiveChordBox1005Cell021Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell022 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell022.interpret
theorem positiveChordBox1005Cell022_valid : positiveChordBox1005Cell022.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (253/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.disk TraceData.positiveChordBox1005Cell022.diskFunction TraceData.positiveChordBox1005Cell022Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell022Node00 TraceData.positiveChordBox1005Cell022Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell022Node01 TraceData.positiveChordBox1005Cell022Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell022Node02 TraceData.positiveChordBox1005Cell022Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell022Node03 TraceData.positiveChordBox1005Cell022Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell022Node04 TraceData.positiveChordBox1005Cell022Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell022Node05 TraceData.positiveChordBox1005Cell022Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell022Node06 TraceData.positiveChordBox1005Cell022Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell022Node07 TraceData.positiveChordBox1005Cell022Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell022Node08 TraceData.positiveChordBox1005Cell022Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell022Node09 TraceData.positiveChordBox1005Cell022Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell022Node10 TraceData.positiveChordBox1005Cell022Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell022Node11 TraceData.positiveChordBox1005Cell022Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell022Node12 TraceData.positiveChordBox1005Cell022Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell022Node13 TraceData.positiveChordBox1005Cell022Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell022Node14 TraceData.positiveChordBox1005Cell022Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell022Node15 TraceData.positiveChordBox1005Cell022Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell022Node16 TraceData.positiveChordBox1005Cell022Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell022Node17 TraceData.positiveChordBox1005Cell022Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell022Node18 TraceData.positiveChordBox1005Cell022Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell022Node19 TraceData.positiveChordBox1005Cell022Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell022Node20 TraceData.positiveChordBox1005Cell022Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell022Node21 TraceData.positiveChordBox1005Cell022Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell022Node22 TraceData.positiveChordBox1005Cell022Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell022Node23 TraceData.positiveChordBox1005Cell022Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell022Node24 TraceData.positiveChordBox1005Cell022Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell022Node25 TraceData.positiveChordBox1005Cell022Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell022Node26 TraceData.positiveChordBox1005Cell022Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell022Node27 TraceData.positiveChordBox1005Cell022Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell022Node28 TraceData.positiveChordBox1005Cell022Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell022Node29 TraceData.positiveChordBox1005Cell022Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell022Node30 TraceData.positiveChordBox1005Cell022Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell022.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell022Node31 TraceData.positiveChordBox1005Cell022Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell023 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell023.interpret
theorem positiveChordBox1005Cell023_valid : positiveChordBox1005Cell023.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (509/512) (1/512) (1/256) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.disk TraceData.positiveChordBox1005Cell023.diskFunction TraceData.positiveChordBox1005Cell023Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell023Node00 TraceData.positiveChordBox1005Cell023Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell023Node01 TraceData.positiveChordBox1005Cell023Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell023Node02 TraceData.positiveChordBox1005Cell023Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell023Node03 TraceData.positiveChordBox1005Cell023Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell023Node04 TraceData.positiveChordBox1005Cell023Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell023Node05 TraceData.positiveChordBox1005Cell023Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell023Node06 TraceData.positiveChordBox1005Cell023Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell023Node07 TraceData.positiveChordBox1005Cell023Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell023Node08 TraceData.positiveChordBox1005Cell023Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell023Node09 TraceData.positiveChordBox1005Cell023Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell023Node10 TraceData.positiveChordBox1005Cell023Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell023Node11 TraceData.positiveChordBox1005Cell023Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell023Node12 TraceData.positiveChordBox1005Cell023Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell023Node13 TraceData.positiveChordBox1005Cell023Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell023Node14 TraceData.positiveChordBox1005Cell023Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell023Node15 TraceData.positiveChordBox1005Cell023Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell023Node16 TraceData.positiveChordBox1005Cell023Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell023Node17 TraceData.positiveChordBox1005Cell023Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell023Node18 TraceData.positiveChordBox1005Cell023Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell023Node19 TraceData.positiveChordBox1005Cell023Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell023Node20 TraceData.positiveChordBox1005Cell023Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell023Node21 TraceData.positiveChordBox1005Cell023Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell023Node22 TraceData.positiveChordBox1005Cell023Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell023Node23 TraceData.positiveChordBox1005Cell023Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell023Node24 TraceData.positiveChordBox1005Cell023Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell023Node25 TraceData.positiveChordBox1005Cell023Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell023Node26 TraceData.positiveChordBox1005Cell023Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell023Node27 TraceData.positiveChordBox1005Cell023Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell023Node28 TraceData.positiveChordBox1005Cell023Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell023Node29 TraceData.positiveChordBox1005Cell023Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell023Node30 TraceData.positiveChordBox1005Cell023Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell023.center (1/512) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell023Node31 TraceData.positiveChordBox1005Cell023Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell024 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell024.interpret
theorem positiveChordBox1005Cell024_valid : positiveChordBox1005Cell024.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (1021/1024) (1/1024) (1/512) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.disk TraceData.positiveChordBox1005Cell024.diskFunction TraceData.positiveChordBox1005Cell024Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell024Node00 TraceData.positiveChordBox1005Cell024Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell024Node01 TraceData.positiveChordBox1005Cell024Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell024Node02 TraceData.positiveChordBox1005Cell024Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell024Node03 TraceData.positiveChordBox1005Cell024Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell024Node04 TraceData.positiveChordBox1005Cell024Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell024Node05 TraceData.positiveChordBox1005Cell024Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell024Node06 TraceData.positiveChordBox1005Cell024Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell024Node07 TraceData.positiveChordBox1005Cell024Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell024Node08 TraceData.positiveChordBox1005Cell024Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell024Node09 TraceData.positiveChordBox1005Cell024Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell024Node10 TraceData.positiveChordBox1005Cell024Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell024Node11 TraceData.positiveChordBox1005Cell024Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell024Node12 TraceData.positiveChordBox1005Cell024Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell024Node13 TraceData.positiveChordBox1005Cell024Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell024Node14 TraceData.positiveChordBox1005Cell024Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell024Node15 TraceData.positiveChordBox1005Cell024Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell024Node16 TraceData.positiveChordBox1005Cell024Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell024Node17 TraceData.positiveChordBox1005Cell024Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell024Node18 TraceData.positiveChordBox1005Cell024Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell024Node19 TraceData.positiveChordBox1005Cell024Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell024Node20 TraceData.positiveChordBox1005Cell024Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell024Node21 TraceData.positiveChordBox1005Cell024Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell024Node22 TraceData.positiveChordBox1005Cell024Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell024Node23 TraceData.positiveChordBox1005Cell024Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell024Node24 TraceData.positiveChordBox1005Cell024Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell024Node25 TraceData.positiveChordBox1005Cell024Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell024Node26 TraceData.positiveChordBox1005Cell024Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell024Node27 TraceData.positiveChordBox1005Cell024Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell024Node28 TraceData.positiveChordBox1005Cell024Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell024Node29 TraceData.positiveChordBox1005Cell024Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell024Node30 TraceData.positiveChordBox1005Cell024Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell024.center (1/1024) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell024Node31 TraceData.positiveChordBox1005Cell024Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell025 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell025.interpret
theorem positiveChordBox1005Cell025_valid : positiveChordBox1005Cell025.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (2045/2048) (1/2048) (1/1024) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.disk TraceData.positiveChordBox1005Cell025.diskFunction TraceData.positiveChordBox1005Cell025Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell025Node00 TraceData.positiveChordBox1005Cell025Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell025Node01 TraceData.positiveChordBox1005Cell025Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell025Node02 TraceData.positiveChordBox1005Cell025Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell025Node03 TraceData.positiveChordBox1005Cell025Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell025Node04 TraceData.positiveChordBox1005Cell025Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell025Node05 TraceData.positiveChordBox1005Cell025Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell025Node06 TraceData.positiveChordBox1005Cell025Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell025Node07 TraceData.positiveChordBox1005Cell025Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell025Node08 TraceData.positiveChordBox1005Cell025Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell025Node09 TraceData.positiveChordBox1005Cell025Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell025Node10 TraceData.positiveChordBox1005Cell025Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell025Node11 TraceData.positiveChordBox1005Cell025Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell025Node12 TraceData.positiveChordBox1005Cell025Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell025Node13 TraceData.positiveChordBox1005Cell025Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell025Node14 TraceData.positiveChordBox1005Cell025Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell025Node15 TraceData.positiveChordBox1005Cell025Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell025Node16 TraceData.positiveChordBox1005Cell025Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell025Node17 TraceData.positiveChordBox1005Cell025Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell025Node18 TraceData.positiveChordBox1005Cell025Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell025Node19 TraceData.positiveChordBox1005Cell025Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell025Node20 TraceData.positiveChordBox1005Cell025Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell025Node21 TraceData.positiveChordBox1005Cell025Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell025Node22 TraceData.positiveChordBox1005Cell025Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell025Node23 TraceData.positiveChordBox1005Cell025Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell025Node24 TraceData.positiveChordBox1005Cell025Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell025Node25 TraceData.positiveChordBox1005Cell025Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell025Node26 TraceData.positiveChordBox1005Cell025Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell025Node27 TraceData.positiveChordBox1005Cell025Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell025Node28 TraceData.positiveChordBox1005Cell025Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell025Node29 TraceData.positiveChordBox1005Cell025Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell025Node30 TraceData.positiveChordBox1005Cell025Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell025.center (1/2048) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell025Node31 TraceData.positiveChordBox1005Cell025Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell026 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell026.interpret
theorem positiveChordBox1005Cell026_valid : positiveChordBox1005Cell026.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (4093/4096) (1/4096) (1/2048) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.disk TraceData.positiveChordBox1005Cell026.diskFunction TraceData.positiveChordBox1005Cell026Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell026Node00 TraceData.positiveChordBox1005Cell026Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell026Node01 TraceData.positiveChordBox1005Cell026Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell026Node02 TraceData.positiveChordBox1005Cell026Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell026Node03 TraceData.positiveChordBox1005Cell026Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell026Node04 TraceData.positiveChordBox1005Cell026Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell026Node05 TraceData.positiveChordBox1005Cell026Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell026Node06 TraceData.positiveChordBox1005Cell026Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell026Node07 TraceData.positiveChordBox1005Cell026Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell026Node08 TraceData.positiveChordBox1005Cell026Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell026Node09 TraceData.positiveChordBox1005Cell026Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell026Node10 TraceData.positiveChordBox1005Cell026Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell026Node11 TraceData.positiveChordBox1005Cell026Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell026Node12 TraceData.positiveChordBox1005Cell026Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell026Node13 TraceData.positiveChordBox1005Cell026Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell026Node14 TraceData.positiveChordBox1005Cell026Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell026Node15 TraceData.positiveChordBox1005Cell026Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell026Node16 TraceData.positiveChordBox1005Cell026Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell026Node17 TraceData.positiveChordBox1005Cell026Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell026Node18 TraceData.positiveChordBox1005Cell026Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell026Node19 TraceData.positiveChordBox1005Cell026Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell026Node20 TraceData.positiveChordBox1005Cell026Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell026Node21 TraceData.positiveChordBox1005Cell026Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell026Node22 TraceData.positiveChordBox1005Cell026Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell026Node23 TraceData.positiveChordBox1005Cell026Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell026Node24 TraceData.positiveChordBox1005Cell026Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell026Node25 TraceData.positiveChordBox1005Cell026Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell026Node26 TraceData.positiveChordBox1005Cell026Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell026Node27 TraceData.positiveChordBox1005Cell026Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell026Node28 TraceData.positiveChordBox1005Cell026Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell026Node29 TraceData.positiveChordBox1005Cell026Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell026Node30 TraceData.positiveChordBox1005Cell026Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell026.center (1/4096) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell026Node31 TraceData.positiveChordBox1005Cell026Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell027 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell027.interpret
theorem positiveChordBox1005Cell027_valid : positiveChordBox1005Cell027.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (8189/8192) (1/8192) (1/4096) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.disk TraceData.positiveChordBox1005Cell027.diskFunction TraceData.positiveChordBox1005Cell027Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell027Node00 TraceData.positiveChordBox1005Cell027Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell027Node01 TraceData.positiveChordBox1005Cell027Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell027Node02 TraceData.positiveChordBox1005Cell027Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell027Node03 TraceData.positiveChordBox1005Cell027Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell027Node04 TraceData.positiveChordBox1005Cell027Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell027Node05 TraceData.positiveChordBox1005Cell027Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell027Node06 TraceData.positiveChordBox1005Cell027Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell027Node07 TraceData.positiveChordBox1005Cell027Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell027Node08 TraceData.positiveChordBox1005Cell027Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell027Node09 TraceData.positiveChordBox1005Cell027Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell027Node10 TraceData.positiveChordBox1005Cell027Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell027Node11 TraceData.positiveChordBox1005Cell027Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell027Node12 TraceData.positiveChordBox1005Cell027Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell027Node13 TraceData.positiveChordBox1005Cell027Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell027Node14 TraceData.positiveChordBox1005Cell027Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell027Node15 TraceData.positiveChordBox1005Cell027Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell027Node16 TraceData.positiveChordBox1005Cell027Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell027Node17 TraceData.positiveChordBox1005Cell027Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell027Node18 TraceData.positiveChordBox1005Cell027Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell027Node19 TraceData.positiveChordBox1005Cell027Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell027Node20 TraceData.positiveChordBox1005Cell027Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell027Node21 TraceData.positiveChordBox1005Cell027Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell027Node22 TraceData.positiveChordBox1005Cell027Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell027Node23 TraceData.positiveChordBox1005Cell027Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell027Node24 TraceData.positiveChordBox1005Cell027Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell027Node25 TraceData.positiveChordBox1005Cell027Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell027Node26 TraceData.positiveChordBox1005Cell027Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell027Node27 TraceData.positiveChordBox1005Cell027Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell027Node28 TraceData.positiveChordBox1005Cell027Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell027Node29 TraceData.positiveChordBox1005Cell027Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell027Node30 TraceData.positiveChordBox1005Cell027Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell027.center (1/8192) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell027Node31 TraceData.positiveChordBox1005Cell027Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell028 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell028.interpret
theorem positiveChordBox1005Cell028_valid : positiveChordBox1005Cell028.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (32761/32768) (1/32768) (1/16384) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.disk TraceData.positiveChordBox1005Cell028.diskFunction TraceData.positiveChordBox1005Cell028Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell028Node00 TraceData.positiveChordBox1005Cell028Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell028Node01 TraceData.positiveChordBox1005Cell028Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell028Node02 TraceData.positiveChordBox1005Cell028Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell028Node03 TraceData.positiveChordBox1005Cell028Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell028Node04 TraceData.positiveChordBox1005Cell028Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell028Node05 TraceData.positiveChordBox1005Cell028Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell028Node06 TraceData.positiveChordBox1005Cell028Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell028Node07 TraceData.positiveChordBox1005Cell028Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell028Node08 TraceData.positiveChordBox1005Cell028Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell028Node09 TraceData.positiveChordBox1005Cell028Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell028Node10 TraceData.positiveChordBox1005Cell028Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell028Node11 TraceData.positiveChordBox1005Cell028Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell028Node12 TraceData.positiveChordBox1005Cell028Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell028Node13 TraceData.positiveChordBox1005Cell028Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell028Node14 TraceData.positiveChordBox1005Cell028Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell028Node15 TraceData.positiveChordBox1005Cell028Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell028Node16 TraceData.positiveChordBox1005Cell028Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell028Node17 TraceData.positiveChordBox1005Cell028Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell028Node18 TraceData.positiveChordBox1005Cell028Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell028Node19 TraceData.positiveChordBox1005Cell028Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell028Node20 TraceData.positiveChordBox1005Cell028Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell028Node21 TraceData.positiveChordBox1005Cell028Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell028Node22 TraceData.positiveChordBox1005Cell028Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell028Node23 TraceData.positiveChordBox1005Cell028Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell028Node24 TraceData.positiveChordBox1005Cell028Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell028Node25 TraceData.positiveChordBox1005Cell028Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell028Node26 TraceData.positiveChordBox1005Cell028Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell028Node27 TraceData.positiveChordBox1005Cell028Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell028Node28 TraceData.positiveChordBox1005Cell028Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell028Node29 TraceData.positiveChordBox1005Cell028Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell028Node30 TraceData.positiveChordBox1005Cell028Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell028.center (1/32768) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell028Node31 TraceData.positiveChordBox1005Cell028Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell029 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell029.interpret
theorem positiveChordBox1005Cell029_valid : positiveChordBox1005Cell029.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (32763/32768) (1/32768) (1/16384) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.disk TraceData.positiveChordBox1005Cell029.diskFunction TraceData.positiveChordBox1005Cell029Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell029Node00 TraceData.positiveChordBox1005Cell029Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell029Node01 TraceData.positiveChordBox1005Cell029Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell029Node02 TraceData.positiveChordBox1005Cell029Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell029Node03 TraceData.positiveChordBox1005Cell029Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell029Node04 TraceData.positiveChordBox1005Cell029Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell029Node05 TraceData.positiveChordBox1005Cell029Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell029Node06 TraceData.positiveChordBox1005Cell029Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell029Node07 TraceData.positiveChordBox1005Cell029Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell029Node08 TraceData.positiveChordBox1005Cell029Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell029Node09 TraceData.positiveChordBox1005Cell029Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell029Node10 TraceData.positiveChordBox1005Cell029Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell029Node11 TraceData.positiveChordBox1005Cell029Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell029Node12 TraceData.positiveChordBox1005Cell029Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell029Node13 TraceData.positiveChordBox1005Cell029Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell029Node14 TraceData.positiveChordBox1005Cell029Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell029Node15 TraceData.positiveChordBox1005Cell029Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell029Node16 TraceData.positiveChordBox1005Cell029Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell029Node17 TraceData.positiveChordBox1005Cell029Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell029Node18 TraceData.positiveChordBox1005Cell029Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell029Node19 TraceData.positiveChordBox1005Cell029Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell029Node20 TraceData.positiveChordBox1005Cell029Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell029Node21 TraceData.positiveChordBox1005Cell029Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell029Node22 TraceData.positiveChordBox1005Cell029Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell029Node23 TraceData.positiveChordBox1005Cell029Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell029Node24 TraceData.positiveChordBox1005Cell029Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell029Node25 TraceData.positiveChordBox1005Cell029Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell029Node26 TraceData.positiveChordBox1005Cell029Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell029Node27 TraceData.positiveChordBox1005Cell029Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell029Node28 TraceData.positiveChordBox1005Cell029Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell029Node29 TraceData.positiveChordBox1005Cell029Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell029Node30 TraceData.positiveChordBox1005Cell029Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell029.center (1/32768) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell029Node31 TraceData.positiveChordBox1005Cell029Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell030 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell030.interpret
theorem positiveChordBox1005Cell030_valid : positiveChordBox1005Cell030.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (32765/32768) (1/32768) (1/16384) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.disk TraceData.positiveChordBox1005Cell030.diskFunction TraceData.positiveChordBox1005Cell030Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell030Node00 TraceData.positiveChordBox1005Cell030Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell030Node01 TraceData.positiveChordBox1005Cell030Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell030Node02 TraceData.positiveChordBox1005Cell030Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell030Node03 TraceData.positiveChordBox1005Cell030Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell030Node04 TraceData.positiveChordBox1005Cell030Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell030Node05 TraceData.positiveChordBox1005Cell030Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell030Node06 TraceData.positiveChordBox1005Cell030Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell030Node07 TraceData.positiveChordBox1005Cell030Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell030Node08 TraceData.positiveChordBox1005Cell030Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell030Node09 TraceData.positiveChordBox1005Cell030Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell030Node10 TraceData.positiveChordBox1005Cell030Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell030Node11 TraceData.positiveChordBox1005Cell030Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell030Node12 TraceData.positiveChordBox1005Cell030Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell030Node13 TraceData.positiveChordBox1005Cell030Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell030Node14 TraceData.positiveChordBox1005Cell030Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell030Node15 TraceData.positiveChordBox1005Cell030Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell030Node16 TraceData.positiveChordBox1005Cell030Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell030Node17 TraceData.positiveChordBox1005Cell030Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell030Node18 TraceData.positiveChordBox1005Cell030Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell030Node19 TraceData.positiveChordBox1005Cell030Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell030Node20 TraceData.positiveChordBox1005Cell030Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell030Node21 TraceData.positiveChordBox1005Cell030Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell030Node22 TraceData.positiveChordBox1005Cell030Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell030Node23 TraceData.positiveChordBox1005Cell030Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell030Node24 TraceData.positiveChordBox1005Cell030Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell030Node25 TraceData.positiveChordBox1005Cell030Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell030Node26 TraceData.positiveChordBox1005Cell030Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell030Node27 TraceData.positiveChordBox1005Cell030Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell030Node28 TraceData.positiveChordBox1005Cell030Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell030Node29 TraceData.positiveChordBox1005Cell030Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell030Node30 TraceData.positiveChordBox1005Cell030Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell030.center (1/32768) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell030Node31 TraceData.positiveChordBox1005Cell030Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1005Cell031 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1005Cell031.interpret
theorem positiveChordBox1005Cell031_valid : positiveChordBox1005Cell031.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (32767/32768) (1/32768) (1/16384) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.disk TraceData.positiveChordBox1005Cell031.diskFunction TraceData.positiveChordBox1005Cell031Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1005Cell031Node00 TraceData.positiveChordBox1005Cell031Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1005Cell031Node01 TraceData.positiveChordBox1005Cell031Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1005Cell031Node02 TraceData.positiveChordBox1005Cell031Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1005Cell031Node03 TraceData.positiveChordBox1005Cell031Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1005Cell031Node04 TraceData.positiveChordBox1005Cell031Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1005Cell031Node05 TraceData.positiveChordBox1005Cell031Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1005Cell031Node06 TraceData.positiveChordBox1005Cell031Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1005Cell031Node07 TraceData.positiveChordBox1005Cell031Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1005Cell031Node08 TraceData.positiveChordBox1005Cell031Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1005Cell031Node09 TraceData.positiveChordBox1005Cell031Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1005Cell031Node10 TraceData.positiveChordBox1005Cell031Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1005Cell031Node11 TraceData.positiveChordBox1005Cell031Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1005Cell031Node12 TraceData.positiveChordBox1005Cell031Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1005Cell031Node13 TraceData.positiveChordBox1005Cell031Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1005Cell031Node14 TraceData.positiveChordBox1005Cell031Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1005Cell031Node15 TraceData.positiveChordBox1005Cell031Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1005Cell031Node16 TraceData.positiveChordBox1005Cell031Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1005Cell031Node17 TraceData.positiveChordBox1005Cell031Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1005Cell031Node18 TraceData.positiveChordBox1005Cell031Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1005Cell031Node19 TraceData.positiveChordBox1005Cell031Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1005Cell031Node20 TraceData.positiveChordBox1005Cell031Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1005Cell031Node21 TraceData.positiveChordBox1005Cell031Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1005Cell031Node22 TraceData.positiveChordBox1005Cell031Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1005Cell031Node23 TraceData.positiveChordBox1005Cell031Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1005Cell031Node24 TraceData.positiveChordBox1005Cell031Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1005Cell031Node25 TraceData.positiveChordBox1005Cell031Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1005Cell031Node26 TraceData.positiveChordBox1005Cell031Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1005Cell031Node27 TraceData.positiveChordBox1005Cell031Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1005Cell031Node28 TraceData.positiveChordBox1005Cell031Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1005Cell031Node29 TraceData.positiveChordBox1005Cell031Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1005Cell031Node30 TraceData.positiveChordBox1005Cell031Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1005Parameters TraceData.positiveChordBox1005Cell031.center (1/32768) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1005Cell031Node31 TraceData.positiveChordBox1005Cell031Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
def positiveChordBox1005Boundary : ℕ → ℚ := fun i => match i with
  | 0 => (-1/1)
  | 1 => (-16383/16384)
  | 2 => (-8191/8192)
  | 3 => (-16381/16384)
  | 4 => (-4095/4096)
  | 5 => (-2047/2048)
  | 6 => (-1023/1024)
  | 7 => (-511/512)
  | 8 => (-255/256)
  | 9 => (-127/128)
  | 10 => (-63/64)
  | 11 => (-31/32)
  | 12 => (-15/16)
  | 13 => (-7/8)
  | 14 => (-3/4)
  | 15 => (-1/2)
  | 16 => (0/1)
  | 17 => (1/2)
  | 18 => (3/4)
  | 19 => (7/8)
  | 20 => (15/16)
  | 21 => (31/32)
  | 22 => (63/64)
  | 23 => (127/128)
  | 24 => (255/256)
  | 25 => (511/512)
  | 26 => (1023/1024)
  | 27 => (2047/2048)
  | 28 => (4095/4096)
  | 29 => (16381/16384)
  | 30 => (8191/8192)
  | 31 => (16383/16384)
  | _ => (1/1)
def positiveChordBox1005Radius : Fin 32 → ℚ := ![(1/16384),(1/16384),(1/16384),(1/16384),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(1/4),(1/2),(1/2),(1/4),(1/8),(1/16),(1/32),(1/64),(1/128),(1/256),(1/512),(1/1024),(1/2048),(1/4096),(1/16384),(1/16384),(1/16384),(1/16384)]
noncomputable def positiveChordBox1005Cells : Fin 32 → JacobiChordRangeCell 32 := ![positiveChordBox1005Cell000,positiveChordBox1005Cell001,positiveChordBox1005Cell002,positiveChordBox1005Cell003,positiveChordBox1005Cell004,positiveChordBox1005Cell005,positiveChordBox1005Cell006,positiveChordBox1005Cell007,positiveChordBox1005Cell008,positiveChordBox1005Cell009,positiveChordBox1005Cell010,positiveChordBox1005Cell011,positiveChordBox1005Cell012,positiveChordBox1005Cell013,positiveChordBox1005Cell014,positiveChordBox1005Cell015,positiveChordBox1005Cell016,positiveChordBox1005Cell017,positiveChordBox1005Cell018,positiveChordBox1005Cell019,positiveChordBox1005Cell020,positiveChordBox1005Cell021,positiveChordBox1005Cell022,positiveChordBox1005Cell023,positiveChordBox1005Cell024,positiveChordBox1005Cell025,positiveChordBox1005Cell026,positiveChordBox1005Cell027,positiveChordBox1005Cell028,positiveChordBox1005Cell029,positiveChordBox1005Cell030,positiveChordBox1005Cell031]
theorem positiveChordBox1005Cells_valid : ∀ i : Fin 32, (positiveChordBox1005Cells i).Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1005Parameters (jacobiCellCenter positiveChordBox1005Boundary i) (jacobiCellRadius positiveChordBox1005Boundary i) (positiveChordBox1005Radius i) := by
  intro i
  fin_cases i
  · convert positiveChordBox1005Cell000_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell001_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell002_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell003_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell004_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell005_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell006_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell007_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell008_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell009_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell010_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell011_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell012_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell013_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell014_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell015_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell016_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell017_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell018_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell019_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell020_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell021_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell022_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell023_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell024_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell025_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell026_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell027_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell028_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell029_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell030_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
  · convert positiveChordBox1005Cell031_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1005Boundary]
theorem positiveChordBox1005_lower : (3/10000 : ℚ) < (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).radius := by decide +kernel
theorem positiveChordBox1005_rectangle_positive {t a : ℝ}
    (htl : (((13/80) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((7/40) : ℚ) : ℝ))
    (hal : (((1/2) : ℚ) : ℝ) ≤ a) (hau : a ≤ (((36896752744623146505/73786976294838206464) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < thetaHorizontalPeriod t a := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1005Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1005Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1005Parameters positiveChordBox1005Parameters_valid hbt hba
    positiveChordBox1005Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1005Radius positiveChordBox1005Cells positiveChordBox1005Cells_valid
  have hl := (ComplexBall.re_bounds hb).1
  rw [← horizontalPeriod_eq_jacobiChordKernel ht0 ht85 ha0 ha1] at hl
  have hc : (((3/10000 : ℚ) : ℝ)) <
      (((combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).radius : ℚ) : ℝ) :=
    (Rat.cast_lt (K := ℝ)).mpr positiveChordBox1005_lower
  rw [show (((3/10000 : ℚ) : ℝ)) = (3/10000 : ℝ) by norm_num] at hc
  exact hc.trans_le hl

theorem positiveChordBox1005_vertical_enclosure {t : ℝ}
    (htl : (((13/80) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((7/40) : ℚ) : ℝ)) :
    verticalA t ∈ Set.Icc (((1/2) : ℚ) : ℝ) (((36896752744623146505/73786976294838206464) : ℚ) : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have hdomain : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper :=
    ⟨ht0, htu.trans_lt ((by norm_num : (((7/40) : ℚ) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  have hq := jacobiSmallNome_upper ⟨64,12,6⟩ (7/40) (2331855145745195/18446744073709551616) TraceData.positiveChordBox1005Nome.interpret
    (TraceData.jacobiSmallNome_valid_of_check ⟨64,12,6⟩ (7/40) TraceData.positiveChordBox1005Nome TraceData.positiveChordBox1005Nome_valid)
    (by decide +kernel)
  have hu := verticalA_small_rectangle_upper ht0 htu (by norm_num) hq
  have he : (1/2 : ℝ)+2*(((7/40) : ℚ) : ℝ)*(((2331855145745195/18446744073709551616) : ℚ) : ℝ) = (((36896752744623146505/73786976294838206464) : ℚ) : ℝ) := by norm_num
  rw [he] at hu
  exact ⟨by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (verticalA_gt_half hdomain).le, hu⟩
theorem positiveChordBox1005_positive {t : ℝ}
    (htl : (((13/80) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((7/40) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < actualPeriodAlong t := by
  have ha := positiveChordBox1005_vertical_enclosure htl htu
  exact positiveChordBox1005_rectangle_positive htl htu ha.1 ha.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positiveChordBox1005_positive
