import TwoAxisHelicoid.TraceDataPositiveChordBox1020
import TwoAxisHelicoid.TraceDataJacobiChordBridge
import TwoAxisHelicoid.TraceDataJacobiVerticalBridge
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def positiveChordBox1020Parameters : DyadicJacobiChordParameters := TraceData.positiveChordBox1020Parameters.interpret
theorem positiveChordBox1020Parameters_valid : positiveChordBox1020Parameters.Valid ⟨64,12,6⟩ 18446744074 :=
  TraceData.DyadicJacobiChordParameters.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Parameters_valid
noncomputable def positiveChordBox1020Cell000 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell000.interpret
theorem positiveChordBox1020Cell000_valid : positiveChordBox1020Cell000.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (-63/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.disk TraceData.positiveChordBox1020Cell000.diskFunction TraceData.positiveChordBox1020Cell000Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell000Node00 TraceData.positiveChordBox1020Cell000Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell000Node01 TraceData.positiveChordBox1020Cell000Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell000Node02 TraceData.positiveChordBox1020Cell000Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell000Node03 TraceData.positiveChordBox1020Cell000Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell000Node04 TraceData.positiveChordBox1020Cell000Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell000Node05 TraceData.positiveChordBox1020Cell000Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell000Node06 TraceData.positiveChordBox1020Cell000Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell000Node07 TraceData.positiveChordBox1020Cell000Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell000Node08 TraceData.positiveChordBox1020Cell000Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell000Node09 TraceData.positiveChordBox1020Cell000Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell000Node10 TraceData.positiveChordBox1020Cell000Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell000Node11 TraceData.positiveChordBox1020Cell000Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell000Node12 TraceData.positiveChordBox1020Cell000Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell000Node13 TraceData.positiveChordBox1020Cell000Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell000Node14 TraceData.positiveChordBox1020Cell000Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell000Node15 TraceData.positiveChordBox1020Cell000Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell000Node16 TraceData.positiveChordBox1020Cell000Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell000Node17 TraceData.positiveChordBox1020Cell000Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell000Node18 TraceData.positiveChordBox1020Cell000Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell000Node19 TraceData.positiveChordBox1020Cell000Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell000Node20 TraceData.positiveChordBox1020Cell000Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell000Node21 TraceData.positiveChordBox1020Cell000Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell000Node22 TraceData.positiveChordBox1020Cell000Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell000Node23 TraceData.positiveChordBox1020Cell000Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell000Node24 TraceData.positiveChordBox1020Cell000Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell000Node25 TraceData.positiveChordBox1020Cell000Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell000Node26 TraceData.positiveChordBox1020Cell000Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell000Node27 TraceData.positiveChordBox1020Cell000Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell000Node28 TraceData.positiveChordBox1020Cell000Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell000Node29 TraceData.positiveChordBox1020Cell000Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell000Node30 TraceData.positiveChordBox1020Cell000Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell000.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell000Node31 TraceData.positiveChordBox1020Cell000Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell001 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell001.interpret
theorem positiveChordBox1020Cell001_valid : positiveChordBox1020Cell001.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (-61/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.disk TraceData.positiveChordBox1020Cell001.diskFunction TraceData.positiveChordBox1020Cell001Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell001Node00 TraceData.positiveChordBox1020Cell001Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell001Node01 TraceData.positiveChordBox1020Cell001Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell001Node02 TraceData.positiveChordBox1020Cell001Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell001Node03 TraceData.positiveChordBox1020Cell001Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell001Node04 TraceData.positiveChordBox1020Cell001Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell001Node05 TraceData.positiveChordBox1020Cell001Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell001Node06 TraceData.positiveChordBox1020Cell001Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell001Node07 TraceData.positiveChordBox1020Cell001Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell001Node08 TraceData.positiveChordBox1020Cell001Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell001Node09 TraceData.positiveChordBox1020Cell001Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell001Node10 TraceData.positiveChordBox1020Cell001Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell001Node11 TraceData.positiveChordBox1020Cell001Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell001Node12 TraceData.positiveChordBox1020Cell001Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell001Node13 TraceData.positiveChordBox1020Cell001Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell001Node14 TraceData.positiveChordBox1020Cell001Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell001Node15 TraceData.positiveChordBox1020Cell001Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell001Node16 TraceData.positiveChordBox1020Cell001Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell001Node17 TraceData.positiveChordBox1020Cell001Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell001Node18 TraceData.positiveChordBox1020Cell001Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell001Node19 TraceData.positiveChordBox1020Cell001Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell001Node20 TraceData.positiveChordBox1020Cell001Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell001Node21 TraceData.positiveChordBox1020Cell001Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell001Node22 TraceData.positiveChordBox1020Cell001Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell001Node23 TraceData.positiveChordBox1020Cell001Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell001Node24 TraceData.positiveChordBox1020Cell001Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell001Node25 TraceData.positiveChordBox1020Cell001Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell001Node26 TraceData.positiveChordBox1020Cell001Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell001Node27 TraceData.positiveChordBox1020Cell001Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell001Node28 TraceData.positiveChordBox1020Cell001Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell001Node29 TraceData.positiveChordBox1020Cell001Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell001Node30 TraceData.positiveChordBox1020Cell001Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell001.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell001Node31 TraceData.positiveChordBox1020Cell001Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell002 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell002.interpret
theorem positiveChordBox1020Cell002_valid : positiveChordBox1020Cell002.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (-29/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.disk TraceData.positiveChordBox1020Cell002.diskFunction TraceData.positiveChordBox1020Cell002Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell002Node00 TraceData.positiveChordBox1020Cell002Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell002Node01 TraceData.positiveChordBox1020Cell002Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell002Node02 TraceData.positiveChordBox1020Cell002Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell002Node03 TraceData.positiveChordBox1020Cell002Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell002Node04 TraceData.positiveChordBox1020Cell002Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell002Node05 TraceData.positiveChordBox1020Cell002Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell002Node06 TraceData.positiveChordBox1020Cell002Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell002Node07 TraceData.positiveChordBox1020Cell002Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell002Node08 TraceData.positiveChordBox1020Cell002Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell002Node09 TraceData.positiveChordBox1020Cell002Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell002Node10 TraceData.positiveChordBox1020Cell002Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell002Node11 TraceData.positiveChordBox1020Cell002Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell002Node12 TraceData.positiveChordBox1020Cell002Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell002Node13 TraceData.positiveChordBox1020Cell002Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell002Node14 TraceData.positiveChordBox1020Cell002Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell002Node15 TraceData.positiveChordBox1020Cell002Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell002Node16 TraceData.positiveChordBox1020Cell002Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell002Node17 TraceData.positiveChordBox1020Cell002Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell002Node18 TraceData.positiveChordBox1020Cell002Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell002Node19 TraceData.positiveChordBox1020Cell002Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell002Node20 TraceData.positiveChordBox1020Cell002Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell002Node21 TraceData.positiveChordBox1020Cell002Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell002Node22 TraceData.positiveChordBox1020Cell002Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell002Node23 TraceData.positiveChordBox1020Cell002Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell002Node24 TraceData.positiveChordBox1020Cell002Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell002Node25 TraceData.positiveChordBox1020Cell002Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell002Node26 TraceData.positiveChordBox1020Cell002Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell002Node27 TraceData.positiveChordBox1020Cell002Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell002Node28 TraceData.positiveChordBox1020Cell002Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell002Node29 TraceData.positiveChordBox1020Cell002Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell002Node30 TraceData.positiveChordBox1020Cell002Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell002.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell002Node31 TraceData.positiveChordBox1020Cell002Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell003 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell003.interpret
theorem positiveChordBox1020Cell003_valid : positiveChordBox1020Cell003.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (-13/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.disk TraceData.positiveChordBox1020Cell003.diskFunction TraceData.positiveChordBox1020Cell003Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell003Node00 TraceData.positiveChordBox1020Cell003Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell003Node01 TraceData.positiveChordBox1020Cell003Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell003Node02 TraceData.positiveChordBox1020Cell003Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell003Node03 TraceData.positiveChordBox1020Cell003Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell003Node04 TraceData.positiveChordBox1020Cell003Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell003Node05 TraceData.positiveChordBox1020Cell003Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell003Node06 TraceData.positiveChordBox1020Cell003Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell003Node07 TraceData.positiveChordBox1020Cell003Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell003Node08 TraceData.positiveChordBox1020Cell003Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell003Node09 TraceData.positiveChordBox1020Cell003Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell003Node10 TraceData.positiveChordBox1020Cell003Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell003Node11 TraceData.positiveChordBox1020Cell003Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell003Node12 TraceData.positiveChordBox1020Cell003Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell003Node13 TraceData.positiveChordBox1020Cell003Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell003Node14 TraceData.positiveChordBox1020Cell003Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell003Node15 TraceData.positiveChordBox1020Cell003Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell003Node16 TraceData.positiveChordBox1020Cell003Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell003Node17 TraceData.positiveChordBox1020Cell003Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell003Node18 TraceData.positiveChordBox1020Cell003Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell003Node19 TraceData.positiveChordBox1020Cell003Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell003Node20 TraceData.positiveChordBox1020Cell003Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell003Node21 TraceData.positiveChordBox1020Cell003Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell003Node22 TraceData.positiveChordBox1020Cell003Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell003Node23 TraceData.positiveChordBox1020Cell003Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell003Node24 TraceData.positiveChordBox1020Cell003Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell003Node25 TraceData.positiveChordBox1020Cell003Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell003Node26 TraceData.positiveChordBox1020Cell003Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell003Node27 TraceData.positiveChordBox1020Cell003Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell003Node28 TraceData.positiveChordBox1020Cell003Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell003Node29 TraceData.positiveChordBox1020Cell003Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell003Node30 TraceData.positiveChordBox1020Cell003Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell003.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell003Node31 TraceData.positiveChordBox1020Cell003Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell004 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell004.interpret
theorem positiveChordBox1020Cell004_valid : positiveChordBox1020Cell004.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (-5/8) (1/8) (1/4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.disk TraceData.positiveChordBox1020Cell004.diskFunction TraceData.positiveChordBox1020Cell004Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell004Node00 TraceData.positiveChordBox1020Cell004Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell004Node01 TraceData.positiveChordBox1020Cell004Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell004Node02 TraceData.positiveChordBox1020Cell004Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell004Node03 TraceData.positiveChordBox1020Cell004Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell004Node04 TraceData.positiveChordBox1020Cell004Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell004Node05 TraceData.positiveChordBox1020Cell004Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell004Node06 TraceData.positiveChordBox1020Cell004Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell004Node07 TraceData.positiveChordBox1020Cell004Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell004Node08 TraceData.positiveChordBox1020Cell004Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell004Node09 TraceData.positiveChordBox1020Cell004Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell004Node10 TraceData.positiveChordBox1020Cell004Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell004Node11 TraceData.positiveChordBox1020Cell004Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell004Node12 TraceData.positiveChordBox1020Cell004Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell004Node13 TraceData.positiveChordBox1020Cell004Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell004Node14 TraceData.positiveChordBox1020Cell004Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell004Node15 TraceData.positiveChordBox1020Cell004Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell004Node16 TraceData.positiveChordBox1020Cell004Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell004Node17 TraceData.positiveChordBox1020Cell004Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell004Node18 TraceData.positiveChordBox1020Cell004Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell004Node19 TraceData.positiveChordBox1020Cell004Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell004Node20 TraceData.positiveChordBox1020Cell004Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell004Node21 TraceData.positiveChordBox1020Cell004Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell004Node22 TraceData.positiveChordBox1020Cell004Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell004Node23 TraceData.positiveChordBox1020Cell004Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell004Node24 TraceData.positiveChordBox1020Cell004Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell004Node25 TraceData.positiveChordBox1020Cell004Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell004Node26 TraceData.positiveChordBox1020Cell004Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell004Node27 TraceData.positiveChordBox1020Cell004Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell004Node28 TraceData.positiveChordBox1020Cell004Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell004Node29 TraceData.positiveChordBox1020Cell004Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell004Node30 TraceData.positiveChordBox1020Cell004Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell004.center (1/8) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell004Node31 TraceData.positiveChordBox1020Cell004Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell005 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell005.interpret
theorem positiveChordBox1020Cell005_valid : positiveChordBox1020Cell005.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (-1/4) (1/4) (1/2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.disk TraceData.positiveChordBox1020Cell005.diskFunction TraceData.positiveChordBox1020Cell005Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell005Node00 TraceData.positiveChordBox1020Cell005Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell005Node01 TraceData.positiveChordBox1020Cell005Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell005Node02 TraceData.positiveChordBox1020Cell005Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell005Node03 TraceData.positiveChordBox1020Cell005Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell005Node04 TraceData.positiveChordBox1020Cell005Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell005Node05 TraceData.positiveChordBox1020Cell005Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell005Node06 TraceData.positiveChordBox1020Cell005Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell005Node07 TraceData.positiveChordBox1020Cell005Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell005Node08 TraceData.positiveChordBox1020Cell005Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell005Node09 TraceData.positiveChordBox1020Cell005Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell005Node10 TraceData.positiveChordBox1020Cell005Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell005Node11 TraceData.positiveChordBox1020Cell005Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell005Node12 TraceData.positiveChordBox1020Cell005Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell005Node13 TraceData.positiveChordBox1020Cell005Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell005Node14 TraceData.positiveChordBox1020Cell005Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell005Node15 TraceData.positiveChordBox1020Cell005Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell005Node16 TraceData.positiveChordBox1020Cell005Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell005Node17 TraceData.positiveChordBox1020Cell005Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell005Node18 TraceData.positiveChordBox1020Cell005Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell005Node19 TraceData.positiveChordBox1020Cell005Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell005Node20 TraceData.positiveChordBox1020Cell005Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell005Node21 TraceData.positiveChordBox1020Cell005Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell005Node22 TraceData.positiveChordBox1020Cell005Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell005Node23 TraceData.positiveChordBox1020Cell005Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell005Node24 TraceData.positiveChordBox1020Cell005Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell005Node25 TraceData.positiveChordBox1020Cell005Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell005Node26 TraceData.positiveChordBox1020Cell005Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell005Node27 TraceData.positiveChordBox1020Cell005Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell005Node28 TraceData.positiveChordBox1020Cell005Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell005Node29 TraceData.positiveChordBox1020Cell005Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell005Node30 TraceData.positiveChordBox1020Cell005Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell005.center (1/4) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell005Node31 TraceData.positiveChordBox1020Cell005Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell006 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell006.interpret
theorem positiveChordBox1020Cell006_valid : positiveChordBox1020Cell006.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (1/4) (1/4) (1/2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.disk TraceData.positiveChordBox1020Cell006.diskFunction TraceData.positiveChordBox1020Cell006Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell006Node00 TraceData.positiveChordBox1020Cell006Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell006Node01 TraceData.positiveChordBox1020Cell006Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell006Node02 TraceData.positiveChordBox1020Cell006Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell006Node03 TraceData.positiveChordBox1020Cell006Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell006Node04 TraceData.positiveChordBox1020Cell006Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell006Node05 TraceData.positiveChordBox1020Cell006Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell006Node06 TraceData.positiveChordBox1020Cell006Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell006Node07 TraceData.positiveChordBox1020Cell006Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell006Node08 TraceData.positiveChordBox1020Cell006Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell006Node09 TraceData.positiveChordBox1020Cell006Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell006Node10 TraceData.positiveChordBox1020Cell006Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell006Node11 TraceData.positiveChordBox1020Cell006Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell006Node12 TraceData.positiveChordBox1020Cell006Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell006Node13 TraceData.positiveChordBox1020Cell006Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell006Node14 TraceData.positiveChordBox1020Cell006Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell006Node15 TraceData.positiveChordBox1020Cell006Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell006Node16 TraceData.positiveChordBox1020Cell006Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell006Node17 TraceData.positiveChordBox1020Cell006Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell006Node18 TraceData.positiveChordBox1020Cell006Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell006Node19 TraceData.positiveChordBox1020Cell006Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell006Node20 TraceData.positiveChordBox1020Cell006Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell006Node21 TraceData.positiveChordBox1020Cell006Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell006Node22 TraceData.positiveChordBox1020Cell006Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell006Node23 TraceData.positiveChordBox1020Cell006Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell006Node24 TraceData.positiveChordBox1020Cell006Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell006Node25 TraceData.positiveChordBox1020Cell006Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell006Node26 TraceData.positiveChordBox1020Cell006Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell006Node27 TraceData.positiveChordBox1020Cell006Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell006Node28 TraceData.positiveChordBox1020Cell006Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell006Node29 TraceData.positiveChordBox1020Cell006Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell006Node30 TraceData.positiveChordBox1020Cell006Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell006.center (1/4) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell006Node31 TraceData.positiveChordBox1020Cell006Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell007 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell007.interpret
theorem positiveChordBox1020Cell007_valid : positiveChordBox1020Cell007.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (5/8) (1/8) (1/4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.disk TraceData.positiveChordBox1020Cell007.diskFunction TraceData.positiveChordBox1020Cell007Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell007Node00 TraceData.positiveChordBox1020Cell007Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell007Node01 TraceData.positiveChordBox1020Cell007Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell007Node02 TraceData.positiveChordBox1020Cell007Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell007Node03 TraceData.positiveChordBox1020Cell007Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell007Node04 TraceData.positiveChordBox1020Cell007Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell007Node05 TraceData.positiveChordBox1020Cell007Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell007Node06 TraceData.positiveChordBox1020Cell007Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell007Node07 TraceData.positiveChordBox1020Cell007Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell007Node08 TraceData.positiveChordBox1020Cell007Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell007Node09 TraceData.positiveChordBox1020Cell007Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell007Node10 TraceData.positiveChordBox1020Cell007Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell007Node11 TraceData.positiveChordBox1020Cell007Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell007Node12 TraceData.positiveChordBox1020Cell007Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell007Node13 TraceData.positiveChordBox1020Cell007Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell007Node14 TraceData.positiveChordBox1020Cell007Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell007Node15 TraceData.positiveChordBox1020Cell007Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell007Node16 TraceData.positiveChordBox1020Cell007Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell007Node17 TraceData.positiveChordBox1020Cell007Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell007Node18 TraceData.positiveChordBox1020Cell007Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell007Node19 TraceData.positiveChordBox1020Cell007Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell007Node20 TraceData.positiveChordBox1020Cell007Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell007Node21 TraceData.positiveChordBox1020Cell007Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell007Node22 TraceData.positiveChordBox1020Cell007Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell007Node23 TraceData.positiveChordBox1020Cell007Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell007Node24 TraceData.positiveChordBox1020Cell007Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell007Node25 TraceData.positiveChordBox1020Cell007Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell007Node26 TraceData.positiveChordBox1020Cell007Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell007Node27 TraceData.positiveChordBox1020Cell007Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell007Node28 TraceData.positiveChordBox1020Cell007Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell007Node29 TraceData.positiveChordBox1020Cell007Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell007Node30 TraceData.positiveChordBox1020Cell007Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell007Node31 TraceData.positiveChordBox1020Cell007Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell008 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell008.interpret
theorem positiveChordBox1020Cell008_valid : positiveChordBox1020Cell008.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (13/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.disk TraceData.positiveChordBox1020Cell008.diskFunction TraceData.positiveChordBox1020Cell008Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell008Node00 TraceData.positiveChordBox1020Cell008Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell008Node01 TraceData.positiveChordBox1020Cell008Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell008Node02 TraceData.positiveChordBox1020Cell008Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell008Node03 TraceData.positiveChordBox1020Cell008Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell008Node04 TraceData.positiveChordBox1020Cell008Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell008Node05 TraceData.positiveChordBox1020Cell008Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell008Node06 TraceData.positiveChordBox1020Cell008Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell008Node07 TraceData.positiveChordBox1020Cell008Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell008Node08 TraceData.positiveChordBox1020Cell008Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell008Node09 TraceData.positiveChordBox1020Cell008Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell008Node10 TraceData.positiveChordBox1020Cell008Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell008Node11 TraceData.positiveChordBox1020Cell008Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell008Node12 TraceData.positiveChordBox1020Cell008Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell008Node13 TraceData.positiveChordBox1020Cell008Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell008Node14 TraceData.positiveChordBox1020Cell008Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell008Node15 TraceData.positiveChordBox1020Cell008Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell008Node16 TraceData.positiveChordBox1020Cell008Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell008Node17 TraceData.positiveChordBox1020Cell008Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell008Node18 TraceData.positiveChordBox1020Cell008Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell008Node19 TraceData.positiveChordBox1020Cell008Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell008Node20 TraceData.positiveChordBox1020Cell008Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell008Node21 TraceData.positiveChordBox1020Cell008Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell008Node22 TraceData.positiveChordBox1020Cell008Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell008Node23 TraceData.positiveChordBox1020Cell008Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell008Node24 TraceData.positiveChordBox1020Cell008Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell008Node25 TraceData.positiveChordBox1020Cell008Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell008Node26 TraceData.positiveChordBox1020Cell008Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell008Node27 TraceData.positiveChordBox1020Cell008Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell008Node28 TraceData.positiveChordBox1020Cell008Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell008Node29 TraceData.positiveChordBox1020Cell008Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell008Node30 TraceData.positiveChordBox1020Cell008Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell008.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell008Node31 TraceData.positiveChordBox1020Cell008Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell009 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell009.interpret
theorem positiveChordBox1020Cell009_valid : positiveChordBox1020Cell009.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (29/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.disk TraceData.positiveChordBox1020Cell009.diskFunction TraceData.positiveChordBox1020Cell009Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell009Node00 TraceData.positiveChordBox1020Cell009Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell009Node01 TraceData.positiveChordBox1020Cell009Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell009Node02 TraceData.positiveChordBox1020Cell009Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell009Node03 TraceData.positiveChordBox1020Cell009Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell009Node04 TraceData.positiveChordBox1020Cell009Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell009Node05 TraceData.positiveChordBox1020Cell009Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell009Node06 TraceData.positiveChordBox1020Cell009Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell009Node07 TraceData.positiveChordBox1020Cell009Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell009Node08 TraceData.positiveChordBox1020Cell009Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell009Node09 TraceData.positiveChordBox1020Cell009Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell009Node10 TraceData.positiveChordBox1020Cell009Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell009Node11 TraceData.positiveChordBox1020Cell009Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell009Node12 TraceData.positiveChordBox1020Cell009Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell009Node13 TraceData.positiveChordBox1020Cell009Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell009Node14 TraceData.positiveChordBox1020Cell009Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell009Node15 TraceData.positiveChordBox1020Cell009Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell009Node16 TraceData.positiveChordBox1020Cell009Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell009Node17 TraceData.positiveChordBox1020Cell009Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell009Node18 TraceData.positiveChordBox1020Cell009Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell009Node19 TraceData.positiveChordBox1020Cell009Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell009Node20 TraceData.positiveChordBox1020Cell009Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell009Node21 TraceData.positiveChordBox1020Cell009Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell009Node22 TraceData.positiveChordBox1020Cell009Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell009Node23 TraceData.positiveChordBox1020Cell009Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell009Node24 TraceData.positiveChordBox1020Cell009Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell009Node25 TraceData.positiveChordBox1020Cell009Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell009Node26 TraceData.positiveChordBox1020Cell009Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell009Node27 TraceData.positiveChordBox1020Cell009Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell009Node28 TraceData.positiveChordBox1020Cell009Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell009Node29 TraceData.positiveChordBox1020Cell009Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell009Node30 TraceData.positiveChordBox1020Cell009Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell009.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell009Node31 TraceData.positiveChordBox1020Cell009Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell010 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell010.interpret
theorem positiveChordBox1020Cell010_valid : positiveChordBox1020Cell010.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (61/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.disk TraceData.positiveChordBox1020Cell010.diskFunction TraceData.positiveChordBox1020Cell010Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell010Node00 TraceData.positiveChordBox1020Cell010Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell010Node01 TraceData.positiveChordBox1020Cell010Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell010Node02 TraceData.positiveChordBox1020Cell010Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell010Node03 TraceData.positiveChordBox1020Cell010Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell010Node04 TraceData.positiveChordBox1020Cell010Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell010Node05 TraceData.positiveChordBox1020Cell010Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell010Node06 TraceData.positiveChordBox1020Cell010Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell010Node07 TraceData.positiveChordBox1020Cell010Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell010Node08 TraceData.positiveChordBox1020Cell010Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell010Node09 TraceData.positiveChordBox1020Cell010Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell010Node10 TraceData.positiveChordBox1020Cell010Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell010Node11 TraceData.positiveChordBox1020Cell010Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell010Node12 TraceData.positiveChordBox1020Cell010Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell010Node13 TraceData.positiveChordBox1020Cell010Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell010Node14 TraceData.positiveChordBox1020Cell010Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell010Node15 TraceData.positiveChordBox1020Cell010Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell010Node16 TraceData.positiveChordBox1020Cell010Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell010Node17 TraceData.positiveChordBox1020Cell010Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell010Node18 TraceData.positiveChordBox1020Cell010Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell010Node19 TraceData.positiveChordBox1020Cell010Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell010Node20 TraceData.positiveChordBox1020Cell010Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell010Node21 TraceData.positiveChordBox1020Cell010Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell010Node22 TraceData.positiveChordBox1020Cell010Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell010Node23 TraceData.positiveChordBox1020Cell010Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell010Node24 TraceData.positiveChordBox1020Cell010Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell010Node25 TraceData.positiveChordBox1020Cell010Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell010Node26 TraceData.positiveChordBox1020Cell010Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell010Node27 TraceData.positiveChordBox1020Cell010Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell010Node28 TraceData.positiveChordBox1020Cell010Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell010Node29 TraceData.positiveChordBox1020Cell010Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell010Node30 TraceData.positiveChordBox1020Cell010Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell010.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell010Node31 TraceData.positiveChordBox1020Cell010Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1020Cell011 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1020Cell011.interpret
theorem positiveChordBox1020Cell011_valid : positiveChordBox1020Cell011.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (63/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.disk TraceData.positiveChordBox1020Cell011.diskFunction TraceData.positiveChordBox1020Cell011Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1020Cell011Node00 TraceData.positiveChordBox1020Cell011Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1020Cell011Node01 TraceData.positiveChordBox1020Cell011Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1020Cell011Node02 TraceData.positiveChordBox1020Cell011Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1020Cell011Node03 TraceData.positiveChordBox1020Cell011Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1020Cell011Node04 TraceData.positiveChordBox1020Cell011Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1020Cell011Node05 TraceData.positiveChordBox1020Cell011Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1020Cell011Node06 TraceData.positiveChordBox1020Cell011Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1020Cell011Node07 TraceData.positiveChordBox1020Cell011Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1020Cell011Node08 TraceData.positiveChordBox1020Cell011Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1020Cell011Node09 TraceData.positiveChordBox1020Cell011Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1020Cell011Node10 TraceData.positiveChordBox1020Cell011Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1020Cell011Node11 TraceData.positiveChordBox1020Cell011Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1020Cell011Node12 TraceData.positiveChordBox1020Cell011Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1020Cell011Node13 TraceData.positiveChordBox1020Cell011Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1020Cell011Node14 TraceData.positiveChordBox1020Cell011Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1020Cell011Node15 TraceData.positiveChordBox1020Cell011Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1020Cell011Node16 TraceData.positiveChordBox1020Cell011Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1020Cell011Node17 TraceData.positiveChordBox1020Cell011Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1020Cell011Node18 TraceData.positiveChordBox1020Cell011Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1020Cell011Node19 TraceData.positiveChordBox1020Cell011Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1020Cell011Node20 TraceData.positiveChordBox1020Cell011Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1020Cell011Node21 TraceData.positiveChordBox1020Cell011Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1020Cell011Node22 TraceData.positiveChordBox1020Cell011Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1020Cell011Node23 TraceData.positiveChordBox1020Cell011Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1020Cell011Node24 TraceData.positiveChordBox1020Cell011Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1020Cell011Node25 TraceData.positiveChordBox1020Cell011Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1020Cell011Node26 TraceData.positiveChordBox1020Cell011Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1020Cell011Node27 TraceData.positiveChordBox1020Cell011Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1020Cell011Node28 TraceData.positiveChordBox1020Cell011Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1020Cell011Node29 TraceData.positiveChordBox1020Cell011Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1020Cell011Node30 TraceData.positiveChordBox1020Cell011Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1020Parameters TraceData.positiveChordBox1020Cell011.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1020Cell011Node31 TraceData.positiveChordBox1020Cell011Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
def positiveChordBox1020Boundary : ℕ → ℚ := fun i => match i with
  | 0 => (-1/1)
  | 1 => (-31/32)
  | 2 => (-15/16)
  | 3 => (-7/8)
  | 4 => (-3/4)
  | 5 => (-1/2)
  | 6 => (0/1)
  | 7 => (1/2)
  | 8 => (3/4)
  | 9 => (7/8)
  | 10 => (15/16)
  | 11 => (31/32)
  | _ => (1/1)
def positiveChordBox1020Radius : Fin 12 → ℚ := ![(1/32),(1/32),(1/16),(1/8),(1/4),(1/2),(1/2),(1/4),(1/8),(1/16),(1/32),(1/32)]
noncomputable def positiveChordBox1020Cells : Fin 12 → JacobiChordRangeCell 32 := ![positiveChordBox1020Cell000,positiveChordBox1020Cell001,positiveChordBox1020Cell002,positiveChordBox1020Cell003,positiveChordBox1020Cell004,positiveChordBox1020Cell005,positiveChordBox1020Cell006,positiveChordBox1020Cell007,positiveChordBox1020Cell008,positiveChordBox1020Cell009,positiveChordBox1020Cell010,positiveChordBox1020Cell011]
theorem positiveChordBox1020Cells_valid : ∀ i : Fin 12, (positiveChordBox1020Cells i).Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1020Parameters (jacobiCellCenter positiveChordBox1020Boundary i) (jacobiCellRadius positiveChordBox1020Boundary i) (positiveChordBox1020Radius i) := by
  intro i
  fin_cases i
  · convert positiveChordBox1020Cell000_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell001_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell002_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell003_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell004_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell005_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell006_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell007_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell008_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell009_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell010_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
  · convert positiveChordBox1020Cell011_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1020Boundary]
theorem positiveChordBox1020_lower : (3/10000 : ℚ) < (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).radius := by decide +kernel
theorem positiveChordBox1020_rectangle_positive {t a : ℝ}
    (htl : (((9/20) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((37/80) : ℚ) : ℝ))
    (hal : (((1050189/2097152) : ℚ) : ℝ) ≤ a) (hau : a ≤ (((271499/524288) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < thetaHorizontalPeriod t a := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1020Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1020Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1020Parameters positiveChordBox1020Parameters_valid hbt hba
    positiveChordBox1020Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1020Radius positiveChordBox1020Cells positiveChordBox1020Cells_valid
  have hl := (ComplexBall.re_bounds hb).1
  rw [← horizontalPeriod_eq_jacobiChordKernel ht0 ht85 ha0 ha1] at hl
  have hc : (((3/10000 : ℚ) : ℝ)) <
      (((combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).radius : ℚ) : ℝ) :=
    (Rat.cast_lt (K := ℝ)).mpr positiveChordBox1020_lower
  rw [show (((3/10000 : ℚ) : ℝ)) = (3/10000 : ℝ) by norm_num] at hc
  exact hc.trans_le hl

theorem positiveChordBox1020_vertical_enclosure {t : ℝ}
    (htl : (((9/20) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((37/80) : ℚ) : ℝ)) :
    verticalA t ∈ Set.Icc (((1050189/2097152) : ℚ) : ℝ) (((271499/524288) : ℚ) : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have hdomain : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper :=
    ⟨ht0, htu.trans_lt ((by norm_num : (((37/80) : ℚ) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  have hLowert : (TraceData.positiveChordBox1020LowerParameters.interpret.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hLowera : (TraceData.positiveChordBox1020LowerParameters.interpret.abscissa.toBall 64).Contains ((((1050189/2097152) : ℚ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_ratCast] using coarsen_contains (rational_contains (1050189/2097152))
      (by decide +kernel : (TraceData.positiveChordBox1020LowerParameters.interpret.abscissa.toBall 64).coarsens (ComplexBall.rational (1050189/2097152)))
  have hgLower := DyadicJacobiVerticalTrace.thetaG_pos ⟨64,12,6⟩ 18446744074 ht0
    (by norm_num : 0 < (((1050189/2097152) : ℚ) : ℝ)) (by norm_num : (((1050189/2097152) : ℚ) : ℝ) < 1)
    TraceData.positiveChordBox1020LowerParameters.interpret (TraceData.DyadicJacobiBaseParameters.valid_of_valid ⟨64,12,6⟩ TraceData.positiveChordBox1020LowerParameters TraceData.positiveChordBox1020LowerParameters_valid)
    hLowert hLowera TraceData.positiveChordBox1020Lower.interpret
    (TraceData.DyadicJacobiVerticalTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveChordBox1020LowerParameters TraceData.positiveChordBox1020Lower TraceData.positiveChordBox1020Lower_valid)
    (by decide +kernel)
  have hUppert : (TraceData.positiveChordBox1020UpperParameters.interpret.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hUppera : (TraceData.positiveChordBox1020UpperParameters.interpret.abscissa.toBall 64).Contains ((((271499/524288) : ℚ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_ratCast] using coarsen_contains (rational_contains (271499/524288))
      (by decide +kernel : (TraceData.positiveChordBox1020UpperParameters.interpret.abscissa.toBall 64).coarsens (ComplexBall.rational (271499/524288)))
  have hgUpper := DyadicJacobiVerticalTrace.thetaG_neg ⟨64,12,6⟩ 18446744074 ht0
    (by norm_num : 0 < (((271499/524288) : ℚ) : ℝ)) (by norm_num : (((271499/524288) : ℚ) : ℝ) < 1)
    TraceData.positiveChordBox1020UpperParameters.interpret (TraceData.DyadicJacobiBaseParameters.valid_of_valid ⟨64,12,6⟩ TraceData.positiveChordBox1020UpperParameters TraceData.positiveChordBox1020UpperParameters_valid)
    hUppert hUppera TraceData.positiveChordBox1020Upper.interpret
    (TraceData.DyadicJacobiVerticalTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveChordBox1020UpperParameters TraceData.positiveChordBox1020Upper TraceData.positiveChordBox1020Upper_valid)
    (by decide +kernel)
  have ha := verticalA_mem_of_boundary_signs hdomain (by norm_num) (by norm_num) hgLower hgUpper
  exact ⟨ha.1.le,ha.2.le⟩
theorem positiveChordBox1020_positive {t : ℝ}
    (htl : (((9/20) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((37/80) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < actualPeriodAlong t := by
  have ha := positiveChordBox1020_vertical_enclosure htl htu
  exact positiveChordBox1020_rectangle_positive htl htu ha.1 ha.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positiveChordBox1020_positive
