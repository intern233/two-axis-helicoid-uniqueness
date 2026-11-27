import TwoAxisHelicoid.TraceDataPositiveChordBox1022
import TwoAxisHelicoid.TraceDataJacobiChordBridge
import TwoAxisHelicoid.TraceDataJacobiVerticalBridge
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def positiveChordBox1022Parameters : DyadicJacobiChordParameters := TraceData.positiveChordBox1022Parameters.interpret
theorem positiveChordBox1022Parameters_valid : positiveChordBox1022Parameters.Valid ⟨64,12,6⟩ 18446744074 :=
  TraceData.DyadicJacobiChordParameters.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Parameters_valid
noncomputable def positiveChordBox1022Cell000 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1022Cell000.interpret
theorem positiveChordBox1022Cell000_valid : positiveChordBox1022Cell000.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (-31/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.disk TraceData.positiveChordBox1022Cell000.diskFunction TraceData.positiveChordBox1022Cell000Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1022Cell000Node00 TraceData.positiveChordBox1022Cell000Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1022Cell000Node01 TraceData.positiveChordBox1022Cell000Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1022Cell000Node02 TraceData.positiveChordBox1022Cell000Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1022Cell000Node03 TraceData.positiveChordBox1022Cell000Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1022Cell000Node04 TraceData.positiveChordBox1022Cell000Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1022Cell000Node05 TraceData.positiveChordBox1022Cell000Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1022Cell000Node06 TraceData.positiveChordBox1022Cell000Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1022Cell000Node07 TraceData.positiveChordBox1022Cell000Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1022Cell000Node08 TraceData.positiveChordBox1022Cell000Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1022Cell000Node09 TraceData.positiveChordBox1022Cell000Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1022Cell000Node10 TraceData.positiveChordBox1022Cell000Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1022Cell000Node11 TraceData.positiveChordBox1022Cell000Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1022Cell000Node12 TraceData.positiveChordBox1022Cell000Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1022Cell000Node13 TraceData.positiveChordBox1022Cell000Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1022Cell000Node14 TraceData.positiveChordBox1022Cell000Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1022Cell000Node15 TraceData.positiveChordBox1022Cell000Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1022Cell000Node16 TraceData.positiveChordBox1022Cell000Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1022Cell000Node17 TraceData.positiveChordBox1022Cell000Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1022Cell000Node18 TraceData.positiveChordBox1022Cell000Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1022Cell000Node19 TraceData.positiveChordBox1022Cell000Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1022Cell000Node20 TraceData.positiveChordBox1022Cell000Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1022Cell000Node21 TraceData.positiveChordBox1022Cell000Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1022Cell000Node22 TraceData.positiveChordBox1022Cell000Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1022Cell000Node23 TraceData.positiveChordBox1022Cell000Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1022Cell000Node24 TraceData.positiveChordBox1022Cell000Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1022Cell000Node25 TraceData.positiveChordBox1022Cell000Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1022Cell000Node26 TraceData.positiveChordBox1022Cell000Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1022Cell000Node27 TraceData.positiveChordBox1022Cell000Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1022Cell000Node28 TraceData.positiveChordBox1022Cell000Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1022Cell000Node29 TraceData.positiveChordBox1022Cell000Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1022Cell000Node30 TraceData.positiveChordBox1022Cell000Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell000.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1022Cell000Node31 TraceData.positiveChordBox1022Cell000Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1022Cell001 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1022Cell001.interpret
theorem positiveChordBox1022Cell001_valid : positiveChordBox1022Cell001.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (-29/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.disk TraceData.positiveChordBox1022Cell001.diskFunction TraceData.positiveChordBox1022Cell001Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1022Cell001Node00 TraceData.positiveChordBox1022Cell001Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1022Cell001Node01 TraceData.positiveChordBox1022Cell001Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1022Cell001Node02 TraceData.positiveChordBox1022Cell001Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1022Cell001Node03 TraceData.positiveChordBox1022Cell001Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1022Cell001Node04 TraceData.positiveChordBox1022Cell001Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1022Cell001Node05 TraceData.positiveChordBox1022Cell001Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1022Cell001Node06 TraceData.positiveChordBox1022Cell001Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1022Cell001Node07 TraceData.positiveChordBox1022Cell001Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1022Cell001Node08 TraceData.positiveChordBox1022Cell001Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1022Cell001Node09 TraceData.positiveChordBox1022Cell001Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1022Cell001Node10 TraceData.positiveChordBox1022Cell001Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1022Cell001Node11 TraceData.positiveChordBox1022Cell001Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1022Cell001Node12 TraceData.positiveChordBox1022Cell001Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1022Cell001Node13 TraceData.positiveChordBox1022Cell001Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1022Cell001Node14 TraceData.positiveChordBox1022Cell001Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1022Cell001Node15 TraceData.positiveChordBox1022Cell001Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1022Cell001Node16 TraceData.positiveChordBox1022Cell001Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1022Cell001Node17 TraceData.positiveChordBox1022Cell001Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1022Cell001Node18 TraceData.positiveChordBox1022Cell001Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1022Cell001Node19 TraceData.positiveChordBox1022Cell001Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1022Cell001Node20 TraceData.positiveChordBox1022Cell001Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1022Cell001Node21 TraceData.positiveChordBox1022Cell001Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1022Cell001Node22 TraceData.positiveChordBox1022Cell001Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1022Cell001Node23 TraceData.positiveChordBox1022Cell001Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1022Cell001Node24 TraceData.positiveChordBox1022Cell001Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1022Cell001Node25 TraceData.positiveChordBox1022Cell001Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1022Cell001Node26 TraceData.positiveChordBox1022Cell001Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1022Cell001Node27 TraceData.positiveChordBox1022Cell001Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1022Cell001Node28 TraceData.positiveChordBox1022Cell001Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1022Cell001Node29 TraceData.positiveChordBox1022Cell001Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1022Cell001Node30 TraceData.positiveChordBox1022Cell001Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell001.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1022Cell001Node31 TraceData.positiveChordBox1022Cell001Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1022Cell002 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1022Cell002.interpret
theorem positiveChordBox1022Cell002_valid : positiveChordBox1022Cell002.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (-13/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.disk TraceData.positiveChordBox1022Cell002.diskFunction TraceData.positiveChordBox1022Cell002Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1022Cell002Node00 TraceData.positiveChordBox1022Cell002Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1022Cell002Node01 TraceData.positiveChordBox1022Cell002Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1022Cell002Node02 TraceData.positiveChordBox1022Cell002Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1022Cell002Node03 TraceData.positiveChordBox1022Cell002Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1022Cell002Node04 TraceData.positiveChordBox1022Cell002Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1022Cell002Node05 TraceData.positiveChordBox1022Cell002Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1022Cell002Node06 TraceData.positiveChordBox1022Cell002Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1022Cell002Node07 TraceData.positiveChordBox1022Cell002Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1022Cell002Node08 TraceData.positiveChordBox1022Cell002Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1022Cell002Node09 TraceData.positiveChordBox1022Cell002Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1022Cell002Node10 TraceData.positiveChordBox1022Cell002Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1022Cell002Node11 TraceData.positiveChordBox1022Cell002Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1022Cell002Node12 TraceData.positiveChordBox1022Cell002Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1022Cell002Node13 TraceData.positiveChordBox1022Cell002Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1022Cell002Node14 TraceData.positiveChordBox1022Cell002Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1022Cell002Node15 TraceData.positiveChordBox1022Cell002Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1022Cell002Node16 TraceData.positiveChordBox1022Cell002Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1022Cell002Node17 TraceData.positiveChordBox1022Cell002Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1022Cell002Node18 TraceData.positiveChordBox1022Cell002Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1022Cell002Node19 TraceData.positiveChordBox1022Cell002Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1022Cell002Node20 TraceData.positiveChordBox1022Cell002Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1022Cell002Node21 TraceData.positiveChordBox1022Cell002Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1022Cell002Node22 TraceData.positiveChordBox1022Cell002Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1022Cell002Node23 TraceData.positiveChordBox1022Cell002Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1022Cell002Node24 TraceData.positiveChordBox1022Cell002Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1022Cell002Node25 TraceData.positiveChordBox1022Cell002Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1022Cell002Node26 TraceData.positiveChordBox1022Cell002Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1022Cell002Node27 TraceData.positiveChordBox1022Cell002Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1022Cell002Node28 TraceData.positiveChordBox1022Cell002Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1022Cell002Node29 TraceData.positiveChordBox1022Cell002Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1022Cell002Node30 TraceData.positiveChordBox1022Cell002Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell002.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1022Cell002Node31 TraceData.positiveChordBox1022Cell002Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1022Cell003 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1022Cell003.interpret
theorem positiveChordBox1022Cell003_valid : positiveChordBox1022Cell003.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (-5/8) (1/8) (1/4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.disk TraceData.positiveChordBox1022Cell003.diskFunction TraceData.positiveChordBox1022Cell003Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1022Cell003Node00 TraceData.positiveChordBox1022Cell003Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1022Cell003Node01 TraceData.positiveChordBox1022Cell003Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1022Cell003Node02 TraceData.positiveChordBox1022Cell003Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1022Cell003Node03 TraceData.positiveChordBox1022Cell003Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1022Cell003Node04 TraceData.positiveChordBox1022Cell003Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1022Cell003Node05 TraceData.positiveChordBox1022Cell003Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1022Cell003Node06 TraceData.positiveChordBox1022Cell003Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1022Cell003Node07 TraceData.positiveChordBox1022Cell003Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1022Cell003Node08 TraceData.positiveChordBox1022Cell003Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1022Cell003Node09 TraceData.positiveChordBox1022Cell003Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1022Cell003Node10 TraceData.positiveChordBox1022Cell003Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1022Cell003Node11 TraceData.positiveChordBox1022Cell003Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1022Cell003Node12 TraceData.positiveChordBox1022Cell003Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1022Cell003Node13 TraceData.positiveChordBox1022Cell003Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1022Cell003Node14 TraceData.positiveChordBox1022Cell003Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1022Cell003Node15 TraceData.positiveChordBox1022Cell003Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1022Cell003Node16 TraceData.positiveChordBox1022Cell003Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1022Cell003Node17 TraceData.positiveChordBox1022Cell003Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1022Cell003Node18 TraceData.positiveChordBox1022Cell003Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1022Cell003Node19 TraceData.positiveChordBox1022Cell003Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1022Cell003Node20 TraceData.positiveChordBox1022Cell003Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1022Cell003Node21 TraceData.positiveChordBox1022Cell003Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1022Cell003Node22 TraceData.positiveChordBox1022Cell003Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1022Cell003Node23 TraceData.positiveChordBox1022Cell003Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1022Cell003Node24 TraceData.positiveChordBox1022Cell003Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1022Cell003Node25 TraceData.positiveChordBox1022Cell003Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1022Cell003Node26 TraceData.positiveChordBox1022Cell003Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1022Cell003Node27 TraceData.positiveChordBox1022Cell003Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1022Cell003Node28 TraceData.positiveChordBox1022Cell003Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1022Cell003Node29 TraceData.positiveChordBox1022Cell003Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1022Cell003Node30 TraceData.positiveChordBox1022Cell003Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell003.center (1/8) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1022Cell003Node31 TraceData.positiveChordBox1022Cell003Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1022Cell004 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1022Cell004.interpret
theorem positiveChordBox1022Cell004_valid : positiveChordBox1022Cell004.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (-1/4) (1/4) (1/2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.disk TraceData.positiveChordBox1022Cell004.diskFunction TraceData.positiveChordBox1022Cell004Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1022Cell004Node00 TraceData.positiveChordBox1022Cell004Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1022Cell004Node01 TraceData.positiveChordBox1022Cell004Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1022Cell004Node02 TraceData.positiveChordBox1022Cell004Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1022Cell004Node03 TraceData.positiveChordBox1022Cell004Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1022Cell004Node04 TraceData.positiveChordBox1022Cell004Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1022Cell004Node05 TraceData.positiveChordBox1022Cell004Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1022Cell004Node06 TraceData.positiveChordBox1022Cell004Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1022Cell004Node07 TraceData.positiveChordBox1022Cell004Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1022Cell004Node08 TraceData.positiveChordBox1022Cell004Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1022Cell004Node09 TraceData.positiveChordBox1022Cell004Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1022Cell004Node10 TraceData.positiveChordBox1022Cell004Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1022Cell004Node11 TraceData.positiveChordBox1022Cell004Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1022Cell004Node12 TraceData.positiveChordBox1022Cell004Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1022Cell004Node13 TraceData.positiveChordBox1022Cell004Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1022Cell004Node14 TraceData.positiveChordBox1022Cell004Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1022Cell004Node15 TraceData.positiveChordBox1022Cell004Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1022Cell004Node16 TraceData.positiveChordBox1022Cell004Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1022Cell004Node17 TraceData.positiveChordBox1022Cell004Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1022Cell004Node18 TraceData.positiveChordBox1022Cell004Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1022Cell004Node19 TraceData.positiveChordBox1022Cell004Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1022Cell004Node20 TraceData.positiveChordBox1022Cell004Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1022Cell004Node21 TraceData.positiveChordBox1022Cell004Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1022Cell004Node22 TraceData.positiveChordBox1022Cell004Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1022Cell004Node23 TraceData.positiveChordBox1022Cell004Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1022Cell004Node24 TraceData.positiveChordBox1022Cell004Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1022Cell004Node25 TraceData.positiveChordBox1022Cell004Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1022Cell004Node26 TraceData.positiveChordBox1022Cell004Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1022Cell004Node27 TraceData.positiveChordBox1022Cell004Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1022Cell004Node28 TraceData.positiveChordBox1022Cell004Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1022Cell004Node29 TraceData.positiveChordBox1022Cell004Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1022Cell004Node30 TraceData.positiveChordBox1022Cell004Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell004.center (1/4) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1022Cell004Node31 TraceData.positiveChordBox1022Cell004Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1022Cell005 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1022Cell005.interpret
theorem positiveChordBox1022Cell005_valid : positiveChordBox1022Cell005.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (1/4) (1/4) (1/2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.disk TraceData.positiveChordBox1022Cell005.diskFunction TraceData.positiveChordBox1022Cell005Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1022Cell005Node00 TraceData.positiveChordBox1022Cell005Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1022Cell005Node01 TraceData.positiveChordBox1022Cell005Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1022Cell005Node02 TraceData.positiveChordBox1022Cell005Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1022Cell005Node03 TraceData.positiveChordBox1022Cell005Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1022Cell005Node04 TraceData.positiveChordBox1022Cell005Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1022Cell005Node05 TraceData.positiveChordBox1022Cell005Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1022Cell005Node06 TraceData.positiveChordBox1022Cell005Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1022Cell005Node07 TraceData.positiveChordBox1022Cell005Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1022Cell005Node08 TraceData.positiveChordBox1022Cell005Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1022Cell005Node09 TraceData.positiveChordBox1022Cell005Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1022Cell005Node10 TraceData.positiveChordBox1022Cell005Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1022Cell005Node11 TraceData.positiveChordBox1022Cell005Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1022Cell005Node12 TraceData.positiveChordBox1022Cell005Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1022Cell005Node13 TraceData.positiveChordBox1022Cell005Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1022Cell005Node14 TraceData.positiveChordBox1022Cell005Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1022Cell005Node15 TraceData.positiveChordBox1022Cell005Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1022Cell005Node16 TraceData.positiveChordBox1022Cell005Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1022Cell005Node17 TraceData.positiveChordBox1022Cell005Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1022Cell005Node18 TraceData.positiveChordBox1022Cell005Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1022Cell005Node19 TraceData.positiveChordBox1022Cell005Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1022Cell005Node20 TraceData.positiveChordBox1022Cell005Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1022Cell005Node21 TraceData.positiveChordBox1022Cell005Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1022Cell005Node22 TraceData.positiveChordBox1022Cell005Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1022Cell005Node23 TraceData.positiveChordBox1022Cell005Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1022Cell005Node24 TraceData.positiveChordBox1022Cell005Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1022Cell005Node25 TraceData.positiveChordBox1022Cell005Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1022Cell005Node26 TraceData.positiveChordBox1022Cell005Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1022Cell005Node27 TraceData.positiveChordBox1022Cell005Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1022Cell005Node28 TraceData.positiveChordBox1022Cell005Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1022Cell005Node29 TraceData.positiveChordBox1022Cell005Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1022Cell005Node30 TraceData.positiveChordBox1022Cell005Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1022Cell005Node31 TraceData.positiveChordBox1022Cell005Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1022Cell006 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1022Cell006.interpret
theorem positiveChordBox1022Cell006_valid : positiveChordBox1022Cell006.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (5/8) (1/8) (1/4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.disk TraceData.positiveChordBox1022Cell006.diskFunction TraceData.positiveChordBox1022Cell006Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1022Cell006Node00 TraceData.positiveChordBox1022Cell006Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1022Cell006Node01 TraceData.positiveChordBox1022Cell006Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1022Cell006Node02 TraceData.positiveChordBox1022Cell006Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1022Cell006Node03 TraceData.positiveChordBox1022Cell006Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1022Cell006Node04 TraceData.positiveChordBox1022Cell006Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1022Cell006Node05 TraceData.positiveChordBox1022Cell006Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1022Cell006Node06 TraceData.positiveChordBox1022Cell006Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1022Cell006Node07 TraceData.positiveChordBox1022Cell006Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1022Cell006Node08 TraceData.positiveChordBox1022Cell006Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1022Cell006Node09 TraceData.positiveChordBox1022Cell006Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1022Cell006Node10 TraceData.positiveChordBox1022Cell006Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1022Cell006Node11 TraceData.positiveChordBox1022Cell006Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1022Cell006Node12 TraceData.positiveChordBox1022Cell006Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1022Cell006Node13 TraceData.positiveChordBox1022Cell006Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1022Cell006Node14 TraceData.positiveChordBox1022Cell006Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1022Cell006Node15 TraceData.positiveChordBox1022Cell006Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1022Cell006Node16 TraceData.positiveChordBox1022Cell006Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1022Cell006Node17 TraceData.positiveChordBox1022Cell006Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1022Cell006Node18 TraceData.positiveChordBox1022Cell006Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1022Cell006Node19 TraceData.positiveChordBox1022Cell006Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1022Cell006Node20 TraceData.positiveChordBox1022Cell006Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1022Cell006Node21 TraceData.positiveChordBox1022Cell006Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1022Cell006Node22 TraceData.positiveChordBox1022Cell006Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1022Cell006Node23 TraceData.positiveChordBox1022Cell006Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1022Cell006Node24 TraceData.positiveChordBox1022Cell006Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1022Cell006Node25 TraceData.positiveChordBox1022Cell006Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1022Cell006Node26 TraceData.positiveChordBox1022Cell006Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1022Cell006Node27 TraceData.positiveChordBox1022Cell006Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1022Cell006Node28 TraceData.positiveChordBox1022Cell006Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1022Cell006Node29 TraceData.positiveChordBox1022Cell006Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1022Cell006Node30 TraceData.positiveChordBox1022Cell006Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell006.center (1/8) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1022Cell006Node31 TraceData.positiveChordBox1022Cell006Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1022Cell007 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1022Cell007.interpret
theorem positiveChordBox1022Cell007_valid : positiveChordBox1022Cell007.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (13/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.disk TraceData.positiveChordBox1022Cell007.diskFunction TraceData.positiveChordBox1022Cell007Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1022Cell007Node00 TraceData.positiveChordBox1022Cell007Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1022Cell007Node01 TraceData.positiveChordBox1022Cell007Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1022Cell007Node02 TraceData.positiveChordBox1022Cell007Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1022Cell007Node03 TraceData.positiveChordBox1022Cell007Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1022Cell007Node04 TraceData.positiveChordBox1022Cell007Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1022Cell007Node05 TraceData.positiveChordBox1022Cell007Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1022Cell007Node06 TraceData.positiveChordBox1022Cell007Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1022Cell007Node07 TraceData.positiveChordBox1022Cell007Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1022Cell007Node08 TraceData.positiveChordBox1022Cell007Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1022Cell007Node09 TraceData.positiveChordBox1022Cell007Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1022Cell007Node10 TraceData.positiveChordBox1022Cell007Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1022Cell007Node11 TraceData.positiveChordBox1022Cell007Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1022Cell007Node12 TraceData.positiveChordBox1022Cell007Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1022Cell007Node13 TraceData.positiveChordBox1022Cell007Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1022Cell007Node14 TraceData.positiveChordBox1022Cell007Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1022Cell007Node15 TraceData.positiveChordBox1022Cell007Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1022Cell007Node16 TraceData.positiveChordBox1022Cell007Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1022Cell007Node17 TraceData.positiveChordBox1022Cell007Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1022Cell007Node18 TraceData.positiveChordBox1022Cell007Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1022Cell007Node19 TraceData.positiveChordBox1022Cell007Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1022Cell007Node20 TraceData.positiveChordBox1022Cell007Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1022Cell007Node21 TraceData.positiveChordBox1022Cell007Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1022Cell007Node22 TraceData.positiveChordBox1022Cell007Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1022Cell007Node23 TraceData.positiveChordBox1022Cell007Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1022Cell007Node24 TraceData.positiveChordBox1022Cell007Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1022Cell007Node25 TraceData.positiveChordBox1022Cell007Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1022Cell007Node26 TraceData.positiveChordBox1022Cell007Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1022Cell007Node27 TraceData.positiveChordBox1022Cell007Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1022Cell007Node28 TraceData.positiveChordBox1022Cell007Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1022Cell007Node29 TraceData.positiveChordBox1022Cell007Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1022Cell007Node30 TraceData.positiveChordBox1022Cell007Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell007.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1022Cell007Node31 TraceData.positiveChordBox1022Cell007Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1022Cell008 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1022Cell008.interpret
theorem positiveChordBox1022Cell008_valid : positiveChordBox1022Cell008.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (29/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.disk TraceData.positiveChordBox1022Cell008.diskFunction TraceData.positiveChordBox1022Cell008Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1022Cell008Node00 TraceData.positiveChordBox1022Cell008Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1022Cell008Node01 TraceData.positiveChordBox1022Cell008Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1022Cell008Node02 TraceData.positiveChordBox1022Cell008Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1022Cell008Node03 TraceData.positiveChordBox1022Cell008Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1022Cell008Node04 TraceData.positiveChordBox1022Cell008Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1022Cell008Node05 TraceData.positiveChordBox1022Cell008Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1022Cell008Node06 TraceData.positiveChordBox1022Cell008Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1022Cell008Node07 TraceData.positiveChordBox1022Cell008Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1022Cell008Node08 TraceData.positiveChordBox1022Cell008Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1022Cell008Node09 TraceData.positiveChordBox1022Cell008Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1022Cell008Node10 TraceData.positiveChordBox1022Cell008Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1022Cell008Node11 TraceData.positiveChordBox1022Cell008Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1022Cell008Node12 TraceData.positiveChordBox1022Cell008Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1022Cell008Node13 TraceData.positiveChordBox1022Cell008Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1022Cell008Node14 TraceData.positiveChordBox1022Cell008Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1022Cell008Node15 TraceData.positiveChordBox1022Cell008Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1022Cell008Node16 TraceData.positiveChordBox1022Cell008Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1022Cell008Node17 TraceData.positiveChordBox1022Cell008Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1022Cell008Node18 TraceData.positiveChordBox1022Cell008Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1022Cell008Node19 TraceData.positiveChordBox1022Cell008Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1022Cell008Node20 TraceData.positiveChordBox1022Cell008Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1022Cell008Node21 TraceData.positiveChordBox1022Cell008Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1022Cell008Node22 TraceData.positiveChordBox1022Cell008Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1022Cell008Node23 TraceData.positiveChordBox1022Cell008Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1022Cell008Node24 TraceData.positiveChordBox1022Cell008Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1022Cell008Node25 TraceData.positiveChordBox1022Cell008Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1022Cell008Node26 TraceData.positiveChordBox1022Cell008Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1022Cell008Node27 TraceData.positiveChordBox1022Cell008Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1022Cell008Node28 TraceData.positiveChordBox1022Cell008Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1022Cell008Node29 TraceData.positiveChordBox1022Cell008Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1022Cell008Node30 TraceData.positiveChordBox1022Cell008Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell008.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1022Cell008Node31 TraceData.positiveChordBox1022Cell008Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1022Cell009 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1022Cell009.interpret
theorem positiveChordBox1022Cell009_valid : positiveChordBox1022Cell009.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (31/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.disk TraceData.positiveChordBox1022Cell009.diskFunction TraceData.positiveChordBox1022Cell009Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1022Cell009Node00 TraceData.positiveChordBox1022Cell009Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1022Cell009Node01 TraceData.positiveChordBox1022Cell009Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1022Cell009Node02 TraceData.positiveChordBox1022Cell009Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1022Cell009Node03 TraceData.positiveChordBox1022Cell009Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1022Cell009Node04 TraceData.positiveChordBox1022Cell009Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1022Cell009Node05 TraceData.positiveChordBox1022Cell009Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1022Cell009Node06 TraceData.positiveChordBox1022Cell009Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1022Cell009Node07 TraceData.positiveChordBox1022Cell009Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1022Cell009Node08 TraceData.positiveChordBox1022Cell009Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1022Cell009Node09 TraceData.positiveChordBox1022Cell009Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1022Cell009Node10 TraceData.positiveChordBox1022Cell009Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1022Cell009Node11 TraceData.positiveChordBox1022Cell009Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1022Cell009Node12 TraceData.positiveChordBox1022Cell009Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1022Cell009Node13 TraceData.positiveChordBox1022Cell009Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1022Cell009Node14 TraceData.positiveChordBox1022Cell009Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1022Cell009Node15 TraceData.positiveChordBox1022Cell009Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1022Cell009Node16 TraceData.positiveChordBox1022Cell009Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1022Cell009Node17 TraceData.positiveChordBox1022Cell009Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1022Cell009Node18 TraceData.positiveChordBox1022Cell009Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1022Cell009Node19 TraceData.positiveChordBox1022Cell009Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1022Cell009Node20 TraceData.positiveChordBox1022Cell009Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1022Cell009Node21 TraceData.positiveChordBox1022Cell009Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1022Cell009Node22 TraceData.positiveChordBox1022Cell009Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1022Cell009Node23 TraceData.positiveChordBox1022Cell009Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1022Cell009Node24 TraceData.positiveChordBox1022Cell009Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1022Cell009Node25 TraceData.positiveChordBox1022Cell009Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1022Cell009Node26 TraceData.positiveChordBox1022Cell009Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1022Cell009Node27 TraceData.positiveChordBox1022Cell009Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1022Cell009Node28 TraceData.positiveChordBox1022Cell009Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1022Cell009Node29 TraceData.positiveChordBox1022Cell009Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1022Cell009Node30 TraceData.positiveChordBox1022Cell009Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1022Parameters TraceData.positiveChordBox1022Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1022Cell009Node31 TraceData.positiveChordBox1022Cell009Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
def positiveChordBox1022Boundary : ℕ → ℚ := fun i => match i with
  | 0 => (-1/1)
  | 1 => (-15/16)
  | 2 => (-7/8)
  | 3 => (-3/4)
  | 4 => (-1/2)
  | 5 => (0/1)
  | 6 => (1/2)
  | 7 => (3/4)
  | 8 => (7/8)
  | 9 => (15/16)
  | _ => (1/1)
def positiveChordBox1022Radius : Fin 10 → ℚ := ![(1/16),(1/16),(1/8),(1/4),(1/2),(1/2),(1/4),(1/8),(1/16),(1/16)]
noncomputable def positiveChordBox1022Cells : Fin 10 → JacobiChordRangeCell 32 := ![positiveChordBox1022Cell000,positiveChordBox1022Cell001,positiveChordBox1022Cell002,positiveChordBox1022Cell003,positiveChordBox1022Cell004,positiveChordBox1022Cell005,positiveChordBox1022Cell006,positiveChordBox1022Cell007,positiveChordBox1022Cell008,positiveChordBox1022Cell009]
theorem positiveChordBox1022Cells_valid : ∀ i : Fin 10, (positiveChordBox1022Cells i).Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1022Parameters (jacobiCellCenter positiveChordBox1022Boundary i) (jacobiCellRadius positiveChordBox1022Boundary i) (positiveChordBox1022Radius i) := by
  intro i
  fin_cases i
  · convert positiveChordBox1022Cell000_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1022Boundary]
  · convert positiveChordBox1022Cell001_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1022Boundary]
  · convert positiveChordBox1022Cell002_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1022Boundary]
  · convert positiveChordBox1022Cell003_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1022Boundary]
  · convert positiveChordBox1022Cell004_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1022Boundary]
  · convert positiveChordBox1022Cell005_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1022Boundary]
  · convert positiveChordBox1022Cell006_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1022Boundary]
  · convert positiveChordBox1022Cell007_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1022Boundary]
  · convert positiveChordBox1022Cell008_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1022Boundary]
  · convert positiveChordBox1022Cell009_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1022Boundary]
theorem positiveChordBox1022_lower : (3/10000 : ℚ) < (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).radius := by decide +kernel
theorem positiveChordBox1022_rectangle_positive {t a : ℝ}
    (htl : (((19/40) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((39/80) : ℚ) : ℝ))
    (hal : (((264035/524288) : ℚ) : ℝ) ≤ a) (hau : a ≤ (((272567/524288) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < thetaHorizontalPeriod t a := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1022Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1022Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1022Parameters positiveChordBox1022Parameters_valid hbt hba
    positiveChordBox1022Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1022Radius positiveChordBox1022Cells positiveChordBox1022Cells_valid
  have hl := (ComplexBall.re_bounds hb).1
  rw [← horizontalPeriod_eq_jacobiChordKernel ht0 ht85 ha0 ha1] at hl
  have hc : (((3/10000 : ℚ) : ℝ)) <
      (((combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).radius : ℚ) : ℝ) :=
    (Rat.cast_lt (K := ℝ)).mpr positiveChordBox1022_lower
  rw [show (((3/10000 : ℚ) : ℝ)) = (3/10000 : ℝ) by norm_num] at hc
  exact hc.trans_le hl

theorem positiveChordBox1022_vertical_enclosure {t : ℝ}
    (htl : (((19/40) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((39/80) : ℚ) : ℝ)) :
    verticalA t ∈ Set.Icc (((264035/524288) : ℚ) : ℝ) (((272567/524288) : ℚ) : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have hdomain : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper :=
    ⟨ht0, htu.trans_lt ((by norm_num : (((39/80) : ℚ) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  have hLowert : (TraceData.positiveChordBox1022LowerParameters.interpret.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hLowera : (TraceData.positiveChordBox1022LowerParameters.interpret.abscissa.toBall 64).Contains ((((264035/524288) : ℚ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_ratCast] using coarsen_contains (rational_contains (264035/524288))
      (by decide +kernel : (TraceData.positiveChordBox1022LowerParameters.interpret.abscissa.toBall 64).coarsens (ComplexBall.rational (264035/524288)))
  have hgLower := DyadicJacobiVerticalTrace.thetaG_pos ⟨64,12,6⟩ 18446744074 ht0
    (by norm_num : 0 < (((264035/524288) : ℚ) : ℝ)) (by norm_num : (((264035/524288) : ℚ) : ℝ) < 1)
    TraceData.positiveChordBox1022LowerParameters.interpret (TraceData.DyadicJacobiBaseParameters.valid_of_valid ⟨64,12,6⟩ TraceData.positiveChordBox1022LowerParameters TraceData.positiveChordBox1022LowerParameters_valid)
    hLowert hLowera TraceData.positiveChordBox1022Lower.interpret
    (TraceData.DyadicJacobiVerticalTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveChordBox1022LowerParameters TraceData.positiveChordBox1022Lower TraceData.positiveChordBox1022Lower_valid)
    (by decide +kernel)
  have hUppert : (TraceData.positiveChordBox1022UpperParameters.interpret.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hUppera : (TraceData.positiveChordBox1022UpperParameters.interpret.abscissa.toBall 64).Contains ((((272567/524288) : ℚ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_ratCast] using coarsen_contains (rational_contains (272567/524288))
      (by decide +kernel : (TraceData.positiveChordBox1022UpperParameters.interpret.abscissa.toBall 64).coarsens (ComplexBall.rational (272567/524288)))
  have hgUpper := DyadicJacobiVerticalTrace.thetaG_neg ⟨64,12,6⟩ 18446744074 ht0
    (by norm_num : 0 < (((272567/524288) : ℚ) : ℝ)) (by norm_num : (((272567/524288) : ℚ) : ℝ) < 1)
    TraceData.positiveChordBox1022UpperParameters.interpret (TraceData.DyadicJacobiBaseParameters.valid_of_valid ⟨64,12,6⟩ TraceData.positiveChordBox1022UpperParameters TraceData.positiveChordBox1022UpperParameters_valid)
    hUppert hUppera TraceData.positiveChordBox1022Upper.interpret
    (TraceData.DyadicJacobiVerticalTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveChordBox1022UpperParameters TraceData.positiveChordBox1022Upper TraceData.positiveChordBox1022Upper_valid)
    (by decide +kernel)
  have ha := verticalA_mem_of_boundary_signs hdomain (by norm_num) (by norm_num) hgLower hgUpper
  exact ⟨ha.1.le,ha.2.le⟩
theorem positiveChordBox1022_positive {t : ℝ}
    (htl : (((19/40) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((39/80) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < actualPeriodAlong t := by
  have ha := positiveChordBox1022_vertical_enclosure htl htu
  exact positiveChordBox1022_rectangle_positive htl htu ha.1 ha.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positiveChordBox1022_positive
