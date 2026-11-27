import TwoAxisHelicoid.TraceDataPositiveChordBox1011
import TwoAxisHelicoid.TraceDataJacobiChordBridge
import TwoAxisHelicoid.TraceDataJacobiVerticalBridge
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def positiveChordBox1011Parameters : DyadicJacobiChordParameters := TraceData.positiveChordBox1011Parameters.interpret
theorem positiveChordBox1011Parameters_valid : positiveChordBox1011Parameters.Valid ⟨64,12,6⟩ 18446744074 :=
  TraceData.DyadicJacobiChordParameters.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Parameters_valid
noncomputable def positiveChordBox1011Cell000 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell000.interpret
theorem positiveChordBox1011Cell000_valid : positiveChordBox1011Cell000.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (-511/512) (1/512) (1/256) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.disk TraceData.positiveChordBox1011Cell000.diskFunction TraceData.positiveChordBox1011Cell000Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell000Node00 TraceData.positiveChordBox1011Cell000Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell000Node01 TraceData.positiveChordBox1011Cell000Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell000Node02 TraceData.positiveChordBox1011Cell000Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell000Node03 TraceData.positiveChordBox1011Cell000Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell000Node04 TraceData.positiveChordBox1011Cell000Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell000Node05 TraceData.positiveChordBox1011Cell000Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell000Node06 TraceData.positiveChordBox1011Cell000Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell000Node07 TraceData.positiveChordBox1011Cell000Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell000Node08 TraceData.positiveChordBox1011Cell000Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell000Node09 TraceData.positiveChordBox1011Cell000Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell000Node10 TraceData.positiveChordBox1011Cell000Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell000Node11 TraceData.positiveChordBox1011Cell000Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell000Node12 TraceData.positiveChordBox1011Cell000Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell000Node13 TraceData.positiveChordBox1011Cell000Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell000Node14 TraceData.positiveChordBox1011Cell000Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell000Node15 TraceData.positiveChordBox1011Cell000Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell000Node16 TraceData.positiveChordBox1011Cell000Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell000Node17 TraceData.positiveChordBox1011Cell000Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell000Node18 TraceData.positiveChordBox1011Cell000Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell000Node19 TraceData.positiveChordBox1011Cell000Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell000Node20 TraceData.positiveChordBox1011Cell000Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell000Node21 TraceData.positiveChordBox1011Cell000Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell000Node22 TraceData.positiveChordBox1011Cell000Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell000Node23 TraceData.positiveChordBox1011Cell000Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell000Node24 TraceData.positiveChordBox1011Cell000Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell000Node25 TraceData.positiveChordBox1011Cell000Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell000Node26 TraceData.positiveChordBox1011Cell000Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell000Node27 TraceData.positiveChordBox1011Cell000Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell000Node28 TraceData.positiveChordBox1011Cell000Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell000Node29 TraceData.positiveChordBox1011Cell000Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell000Node30 TraceData.positiveChordBox1011Cell000Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell000.center (1/512) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell000Node31 TraceData.positiveChordBox1011Cell000Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell001 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell001.interpret
theorem positiveChordBox1011Cell001_valid : positiveChordBox1011Cell001.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (-509/512) (1/512) (1/256) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.disk TraceData.positiveChordBox1011Cell001.diskFunction TraceData.positiveChordBox1011Cell001Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell001Node00 TraceData.positiveChordBox1011Cell001Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell001Node01 TraceData.positiveChordBox1011Cell001Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell001Node02 TraceData.positiveChordBox1011Cell001Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell001Node03 TraceData.positiveChordBox1011Cell001Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell001Node04 TraceData.positiveChordBox1011Cell001Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell001Node05 TraceData.positiveChordBox1011Cell001Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell001Node06 TraceData.positiveChordBox1011Cell001Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell001Node07 TraceData.positiveChordBox1011Cell001Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell001Node08 TraceData.positiveChordBox1011Cell001Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell001Node09 TraceData.positiveChordBox1011Cell001Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell001Node10 TraceData.positiveChordBox1011Cell001Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell001Node11 TraceData.positiveChordBox1011Cell001Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell001Node12 TraceData.positiveChordBox1011Cell001Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell001Node13 TraceData.positiveChordBox1011Cell001Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell001Node14 TraceData.positiveChordBox1011Cell001Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell001Node15 TraceData.positiveChordBox1011Cell001Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell001Node16 TraceData.positiveChordBox1011Cell001Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell001Node17 TraceData.positiveChordBox1011Cell001Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell001Node18 TraceData.positiveChordBox1011Cell001Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell001Node19 TraceData.positiveChordBox1011Cell001Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell001Node20 TraceData.positiveChordBox1011Cell001Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell001Node21 TraceData.positiveChordBox1011Cell001Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell001Node22 TraceData.positiveChordBox1011Cell001Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell001Node23 TraceData.positiveChordBox1011Cell001Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell001Node24 TraceData.positiveChordBox1011Cell001Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell001Node25 TraceData.positiveChordBox1011Cell001Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell001Node26 TraceData.positiveChordBox1011Cell001Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell001Node27 TraceData.positiveChordBox1011Cell001Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell001Node28 TraceData.positiveChordBox1011Cell001Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell001Node29 TraceData.positiveChordBox1011Cell001Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell001Node30 TraceData.positiveChordBox1011Cell001Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell001.center (1/512) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell001Node31 TraceData.positiveChordBox1011Cell001Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell002 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell002.interpret
theorem positiveChordBox1011Cell002_valid : positiveChordBox1011Cell002.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (-253/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.disk TraceData.positiveChordBox1011Cell002.diskFunction TraceData.positiveChordBox1011Cell002Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell002Node00 TraceData.positiveChordBox1011Cell002Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell002Node01 TraceData.positiveChordBox1011Cell002Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell002Node02 TraceData.positiveChordBox1011Cell002Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell002Node03 TraceData.positiveChordBox1011Cell002Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell002Node04 TraceData.positiveChordBox1011Cell002Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell002Node05 TraceData.positiveChordBox1011Cell002Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell002Node06 TraceData.positiveChordBox1011Cell002Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell002Node07 TraceData.positiveChordBox1011Cell002Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell002Node08 TraceData.positiveChordBox1011Cell002Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell002Node09 TraceData.positiveChordBox1011Cell002Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell002Node10 TraceData.positiveChordBox1011Cell002Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell002Node11 TraceData.positiveChordBox1011Cell002Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell002Node12 TraceData.positiveChordBox1011Cell002Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell002Node13 TraceData.positiveChordBox1011Cell002Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell002Node14 TraceData.positiveChordBox1011Cell002Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell002Node15 TraceData.positiveChordBox1011Cell002Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell002Node16 TraceData.positiveChordBox1011Cell002Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell002Node17 TraceData.positiveChordBox1011Cell002Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell002Node18 TraceData.positiveChordBox1011Cell002Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell002Node19 TraceData.positiveChordBox1011Cell002Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell002Node20 TraceData.positiveChordBox1011Cell002Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell002Node21 TraceData.positiveChordBox1011Cell002Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell002Node22 TraceData.positiveChordBox1011Cell002Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell002Node23 TraceData.positiveChordBox1011Cell002Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell002Node24 TraceData.positiveChordBox1011Cell002Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell002Node25 TraceData.positiveChordBox1011Cell002Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell002Node26 TraceData.positiveChordBox1011Cell002Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell002Node27 TraceData.positiveChordBox1011Cell002Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell002Node28 TraceData.positiveChordBox1011Cell002Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell002Node29 TraceData.positiveChordBox1011Cell002Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell002Node30 TraceData.positiveChordBox1011Cell002Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell002.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell002Node31 TraceData.positiveChordBox1011Cell002Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell003 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell003.interpret
theorem positiveChordBox1011Cell003_valid : positiveChordBox1011Cell003.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (-125/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.disk TraceData.positiveChordBox1011Cell003.diskFunction TraceData.positiveChordBox1011Cell003Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell003Node00 TraceData.positiveChordBox1011Cell003Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell003Node01 TraceData.positiveChordBox1011Cell003Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell003Node02 TraceData.positiveChordBox1011Cell003Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell003Node03 TraceData.positiveChordBox1011Cell003Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell003Node04 TraceData.positiveChordBox1011Cell003Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell003Node05 TraceData.positiveChordBox1011Cell003Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell003Node06 TraceData.positiveChordBox1011Cell003Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell003Node07 TraceData.positiveChordBox1011Cell003Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell003Node08 TraceData.positiveChordBox1011Cell003Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell003Node09 TraceData.positiveChordBox1011Cell003Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell003Node10 TraceData.positiveChordBox1011Cell003Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell003Node11 TraceData.positiveChordBox1011Cell003Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell003Node12 TraceData.positiveChordBox1011Cell003Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell003Node13 TraceData.positiveChordBox1011Cell003Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell003Node14 TraceData.positiveChordBox1011Cell003Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell003Node15 TraceData.positiveChordBox1011Cell003Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell003Node16 TraceData.positiveChordBox1011Cell003Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell003Node17 TraceData.positiveChordBox1011Cell003Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell003Node18 TraceData.positiveChordBox1011Cell003Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell003Node19 TraceData.positiveChordBox1011Cell003Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell003Node20 TraceData.positiveChordBox1011Cell003Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell003Node21 TraceData.positiveChordBox1011Cell003Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell003Node22 TraceData.positiveChordBox1011Cell003Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell003Node23 TraceData.positiveChordBox1011Cell003Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell003Node24 TraceData.positiveChordBox1011Cell003Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell003Node25 TraceData.positiveChordBox1011Cell003Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell003Node26 TraceData.positiveChordBox1011Cell003Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell003Node27 TraceData.positiveChordBox1011Cell003Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell003Node28 TraceData.positiveChordBox1011Cell003Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell003Node29 TraceData.positiveChordBox1011Cell003Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell003Node30 TraceData.positiveChordBox1011Cell003Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell003.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell003Node31 TraceData.positiveChordBox1011Cell003Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell004 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell004.interpret
theorem positiveChordBox1011Cell004_valid : positiveChordBox1011Cell004.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (-61/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.disk TraceData.positiveChordBox1011Cell004.diskFunction TraceData.positiveChordBox1011Cell004Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell004Node00 TraceData.positiveChordBox1011Cell004Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell004Node01 TraceData.positiveChordBox1011Cell004Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell004Node02 TraceData.positiveChordBox1011Cell004Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell004Node03 TraceData.positiveChordBox1011Cell004Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell004Node04 TraceData.positiveChordBox1011Cell004Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell004Node05 TraceData.positiveChordBox1011Cell004Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell004Node06 TraceData.positiveChordBox1011Cell004Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell004Node07 TraceData.positiveChordBox1011Cell004Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell004Node08 TraceData.positiveChordBox1011Cell004Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell004Node09 TraceData.positiveChordBox1011Cell004Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell004Node10 TraceData.positiveChordBox1011Cell004Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell004Node11 TraceData.positiveChordBox1011Cell004Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell004Node12 TraceData.positiveChordBox1011Cell004Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell004Node13 TraceData.positiveChordBox1011Cell004Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell004Node14 TraceData.positiveChordBox1011Cell004Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell004Node15 TraceData.positiveChordBox1011Cell004Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell004Node16 TraceData.positiveChordBox1011Cell004Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell004Node17 TraceData.positiveChordBox1011Cell004Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell004Node18 TraceData.positiveChordBox1011Cell004Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell004Node19 TraceData.positiveChordBox1011Cell004Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell004Node20 TraceData.positiveChordBox1011Cell004Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell004Node21 TraceData.positiveChordBox1011Cell004Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell004Node22 TraceData.positiveChordBox1011Cell004Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell004Node23 TraceData.positiveChordBox1011Cell004Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell004Node24 TraceData.positiveChordBox1011Cell004Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell004Node25 TraceData.positiveChordBox1011Cell004Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell004Node26 TraceData.positiveChordBox1011Cell004Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell004Node27 TraceData.positiveChordBox1011Cell004Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell004Node28 TraceData.positiveChordBox1011Cell004Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell004Node29 TraceData.positiveChordBox1011Cell004Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell004Node30 TraceData.positiveChordBox1011Cell004Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell004.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell004Node31 TraceData.positiveChordBox1011Cell004Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell005 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell005.interpret
theorem positiveChordBox1011Cell005_valid : positiveChordBox1011Cell005.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (-29/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.disk TraceData.positiveChordBox1011Cell005.diskFunction TraceData.positiveChordBox1011Cell005Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell005Node00 TraceData.positiveChordBox1011Cell005Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell005Node01 TraceData.positiveChordBox1011Cell005Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell005Node02 TraceData.positiveChordBox1011Cell005Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell005Node03 TraceData.positiveChordBox1011Cell005Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell005Node04 TraceData.positiveChordBox1011Cell005Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell005Node05 TraceData.positiveChordBox1011Cell005Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell005Node06 TraceData.positiveChordBox1011Cell005Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell005Node07 TraceData.positiveChordBox1011Cell005Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell005Node08 TraceData.positiveChordBox1011Cell005Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell005Node09 TraceData.positiveChordBox1011Cell005Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell005Node10 TraceData.positiveChordBox1011Cell005Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell005Node11 TraceData.positiveChordBox1011Cell005Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell005Node12 TraceData.positiveChordBox1011Cell005Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell005Node13 TraceData.positiveChordBox1011Cell005Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell005Node14 TraceData.positiveChordBox1011Cell005Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell005Node15 TraceData.positiveChordBox1011Cell005Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell005Node16 TraceData.positiveChordBox1011Cell005Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell005Node17 TraceData.positiveChordBox1011Cell005Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell005Node18 TraceData.positiveChordBox1011Cell005Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell005Node19 TraceData.positiveChordBox1011Cell005Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell005Node20 TraceData.positiveChordBox1011Cell005Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell005Node21 TraceData.positiveChordBox1011Cell005Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell005Node22 TraceData.positiveChordBox1011Cell005Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell005Node23 TraceData.positiveChordBox1011Cell005Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell005Node24 TraceData.positiveChordBox1011Cell005Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell005Node25 TraceData.positiveChordBox1011Cell005Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell005Node26 TraceData.positiveChordBox1011Cell005Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell005Node27 TraceData.positiveChordBox1011Cell005Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell005Node28 TraceData.positiveChordBox1011Cell005Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell005Node29 TraceData.positiveChordBox1011Cell005Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell005Node30 TraceData.positiveChordBox1011Cell005Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell005.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell005Node31 TraceData.positiveChordBox1011Cell005Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell006 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell006.interpret
theorem positiveChordBox1011Cell006_valid : positiveChordBox1011Cell006.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (-13/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.disk TraceData.positiveChordBox1011Cell006.diskFunction TraceData.positiveChordBox1011Cell006Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell006Node00 TraceData.positiveChordBox1011Cell006Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell006Node01 TraceData.positiveChordBox1011Cell006Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell006Node02 TraceData.positiveChordBox1011Cell006Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell006Node03 TraceData.positiveChordBox1011Cell006Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell006Node04 TraceData.positiveChordBox1011Cell006Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell006Node05 TraceData.positiveChordBox1011Cell006Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell006Node06 TraceData.positiveChordBox1011Cell006Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell006Node07 TraceData.positiveChordBox1011Cell006Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell006Node08 TraceData.positiveChordBox1011Cell006Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell006Node09 TraceData.positiveChordBox1011Cell006Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell006Node10 TraceData.positiveChordBox1011Cell006Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell006Node11 TraceData.positiveChordBox1011Cell006Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell006Node12 TraceData.positiveChordBox1011Cell006Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell006Node13 TraceData.positiveChordBox1011Cell006Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell006Node14 TraceData.positiveChordBox1011Cell006Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell006Node15 TraceData.positiveChordBox1011Cell006Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell006Node16 TraceData.positiveChordBox1011Cell006Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell006Node17 TraceData.positiveChordBox1011Cell006Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell006Node18 TraceData.positiveChordBox1011Cell006Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell006Node19 TraceData.positiveChordBox1011Cell006Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell006Node20 TraceData.positiveChordBox1011Cell006Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell006Node21 TraceData.positiveChordBox1011Cell006Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell006Node22 TraceData.positiveChordBox1011Cell006Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell006Node23 TraceData.positiveChordBox1011Cell006Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell006Node24 TraceData.positiveChordBox1011Cell006Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell006Node25 TraceData.positiveChordBox1011Cell006Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell006Node26 TraceData.positiveChordBox1011Cell006Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell006Node27 TraceData.positiveChordBox1011Cell006Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell006Node28 TraceData.positiveChordBox1011Cell006Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell006Node29 TraceData.positiveChordBox1011Cell006Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell006Node30 TraceData.positiveChordBox1011Cell006Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell006.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell006Node31 TraceData.positiveChordBox1011Cell006Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell007 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell007.interpret
theorem positiveChordBox1011Cell007_valid : positiveChordBox1011Cell007.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (-5/8) (1/8) (1/4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.disk TraceData.positiveChordBox1011Cell007.diskFunction TraceData.positiveChordBox1011Cell007Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell007Node00 TraceData.positiveChordBox1011Cell007Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell007Node01 TraceData.positiveChordBox1011Cell007Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell007Node02 TraceData.positiveChordBox1011Cell007Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell007Node03 TraceData.positiveChordBox1011Cell007Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell007Node04 TraceData.positiveChordBox1011Cell007Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell007Node05 TraceData.positiveChordBox1011Cell007Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell007Node06 TraceData.positiveChordBox1011Cell007Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell007Node07 TraceData.positiveChordBox1011Cell007Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell007Node08 TraceData.positiveChordBox1011Cell007Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell007Node09 TraceData.positiveChordBox1011Cell007Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell007Node10 TraceData.positiveChordBox1011Cell007Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell007Node11 TraceData.positiveChordBox1011Cell007Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell007Node12 TraceData.positiveChordBox1011Cell007Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell007Node13 TraceData.positiveChordBox1011Cell007Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell007Node14 TraceData.positiveChordBox1011Cell007Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell007Node15 TraceData.positiveChordBox1011Cell007Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell007Node16 TraceData.positiveChordBox1011Cell007Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell007Node17 TraceData.positiveChordBox1011Cell007Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell007Node18 TraceData.positiveChordBox1011Cell007Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell007Node19 TraceData.positiveChordBox1011Cell007Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell007Node20 TraceData.positiveChordBox1011Cell007Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell007Node21 TraceData.positiveChordBox1011Cell007Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell007Node22 TraceData.positiveChordBox1011Cell007Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell007Node23 TraceData.positiveChordBox1011Cell007Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell007Node24 TraceData.positiveChordBox1011Cell007Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell007Node25 TraceData.positiveChordBox1011Cell007Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell007Node26 TraceData.positiveChordBox1011Cell007Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell007Node27 TraceData.positiveChordBox1011Cell007Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell007Node28 TraceData.positiveChordBox1011Cell007Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell007Node29 TraceData.positiveChordBox1011Cell007Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell007Node30 TraceData.positiveChordBox1011Cell007Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell007.center (1/8) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell007Node31 TraceData.positiveChordBox1011Cell007Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell008 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell008.interpret
theorem positiveChordBox1011Cell008_valid : positiveChordBox1011Cell008.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (-1/4) (1/4) (1/2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.disk TraceData.positiveChordBox1011Cell008.diskFunction TraceData.positiveChordBox1011Cell008Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell008Node00 TraceData.positiveChordBox1011Cell008Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell008Node01 TraceData.positiveChordBox1011Cell008Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell008Node02 TraceData.positiveChordBox1011Cell008Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell008Node03 TraceData.positiveChordBox1011Cell008Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell008Node04 TraceData.positiveChordBox1011Cell008Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell008Node05 TraceData.positiveChordBox1011Cell008Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell008Node06 TraceData.positiveChordBox1011Cell008Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell008Node07 TraceData.positiveChordBox1011Cell008Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell008Node08 TraceData.positiveChordBox1011Cell008Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell008Node09 TraceData.positiveChordBox1011Cell008Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell008Node10 TraceData.positiveChordBox1011Cell008Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell008Node11 TraceData.positiveChordBox1011Cell008Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell008Node12 TraceData.positiveChordBox1011Cell008Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell008Node13 TraceData.positiveChordBox1011Cell008Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell008Node14 TraceData.positiveChordBox1011Cell008Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell008Node15 TraceData.positiveChordBox1011Cell008Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell008Node16 TraceData.positiveChordBox1011Cell008Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell008Node17 TraceData.positiveChordBox1011Cell008Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell008Node18 TraceData.positiveChordBox1011Cell008Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell008Node19 TraceData.positiveChordBox1011Cell008Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell008Node20 TraceData.positiveChordBox1011Cell008Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell008Node21 TraceData.positiveChordBox1011Cell008Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell008Node22 TraceData.positiveChordBox1011Cell008Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell008Node23 TraceData.positiveChordBox1011Cell008Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell008Node24 TraceData.positiveChordBox1011Cell008Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell008Node25 TraceData.positiveChordBox1011Cell008Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell008Node26 TraceData.positiveChordBox1011Cell008Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell008Node27 TraceData.positiveChordBox1011Cell008Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell008Node28 TraceData.positiveChordBox1011Cell008Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell008Node29 TraceData.positiveChordBox1011Cell008Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell008Node30 TraceData.positiveChordBox1011Cell008Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell008.center (1/4) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell008Node31 TraceData.positiveChordBox1011Cell008Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell009 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell009.interpret
theorem positiveChordBox1011Cell009_valid : positiveChordBox1011Cell009.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (1/4) (1/4) (1/2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.disk TraceData.positiveChordBox1011Cell009.diskFunction TraceData.positiveChordBox1011Cell009Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell009Node00 TraceData.positiveChordBox1011Cell009Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell009Node01 TraceData.positiveChordBox1011Cell009Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell009Node02 TraceData.positiveChordBox1011Cell009Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell009Node03 TraceData.positiveChordBox1011Cell009Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell009Node04 TraceData.positiveChordBox1011Cell009Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell009Node05 TraceData.positiveChordBox1011Cell009Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell009Node06 TraceData.positiveChordBox1011Cell009Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell009Node07 TraceData.positiveChordBox1011Cell009Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell009Node08 TraceData.positiveChordBox1011Cell009Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell009Node09 TraceData.positiveChordBox1011Cell009Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell009Node10 TraceData.positiveChordBox1011Cell009Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell009Node11 TraceData.positiveChordBox1011Cell009Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell009Node12 TraceData.positiveChordBox1011Cell009Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell009Node13 TraceData.positiveChordBox1011Cell009Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell009Node14 TraceData.positiveChordBox1011Cell009Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell009Node15 TraceData.positiveChordBox1011Cell009Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell009Node16 TraceData.positiveChordBox1011Cell009Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell009Node17 TraceData.positiveChordBox1011Cell009Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell009Node18 TraceData.positiveChordBox1011Cell009Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell009Node19 TraceData.positiveChordBox1011Cell009Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell009Node20 TraceData.positiveChordBox1011Cell009Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell009Node21 TraceData.positiveChordBox1011Cell009Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell009Node22 TraceData.positiveChordBox1011Cell009Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell009Node23 TraceData.positiveChordBox1011Cell009Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell009Node24 TraceData.positiveChordBox1011Cell009Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell009Node25 TraceData.positiveChordBox1011Cell009Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell009Node26 TraceData.positiveChordBox1011Cell009Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell009Node27 TraceData.positiveChordBox1011Cell009Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell009Node28 TraceData.positiveChordBox1011Cell009Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell009Node29 TraceData.positiveChordBox1011Cell009Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell009Node30 TraceData.positiveChordBox1011Cell009Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell009.center (1/4) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell009Node31 TraceData.positiveChordBox1011Cell009Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell010 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell010.interpret
theorem positiveChordBox1011Cell010_valid : positiveChordBox1011Cell010.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (5/8) (1/8) (1/4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.disk TraceData.positiveChordBox1011Cell010.diskFunction TraceData.positiveChordBox1011Cell010Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell010Node00 TraceData.positiveChordBox1011Cell010Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell010Node01 TraceData.positiveChordBox1011Cell010Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell010Node02 TraceData.positiveChordBox1011Cell010Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell010Node03 TraceData.positiveChordBox1011Cell010Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell010Node04 TraceData.positiveChordBox1011Cell010Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell010Node05 TraceData.positiveChordBox1011Cell010Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell010Node06 TraceData.positiveChordBox1011Cell010Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell010Node07 TraceData.positiveChordBox1011Cell010Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell010Node08 TraceData.positiveChordBox1011Cell010Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell010Node09 TraceData.positiveChordBox1011Cell010Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell010Node10 TraceData.positiveChordBox1011Cell010Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell010Node11 TraceData.positiveChordBox1011Cell010Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell010Node12 TraceData.positiveChordBox1011Cell010Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell010Node13 TraceData.positiveChordBox1011Cell010Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell010Node14 TraceData.positiveChordBox1011Cell010Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell010Node15 TraceData.positiveChordBox1011Cell010Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell010Node16 TraceData.positiveChordBox1011Cell010Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell010Node17 TraceData.positiveChordBox1011Cell010Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell010Node18 TraceData.positiveChordBox1011Cell010Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell010Node19 TraceData.positiveChordBox1011Cell010Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell010Node20 TraceData.positiveChordBox1011Cell010Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell010Node21 TraceData.positiveChordBox1011Cell010Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell010Node22 TraceData.positiveChordBox1011Cell010Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell010Node23 TraceData.positiveChordBox1011Cell010Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell010Node24 TraceData.positiveChordBox1011Cell010Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell010Node25 TraceData.positiveChordBox1011Cell010Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell010Node26 TraceData.positiveChordBox1011Cell010Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell010Node27 TraceData.positiveChordBox1011Cell010Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell010Node28 TraceData.positiveChordBox1011Cell010Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell010Node29 TraceData.positiveChordBox1011Cell010Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell010Node30 TraceData.positiveChordBox1011Cell010Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell010.center (1/8) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell010Node31 TraceData.positiveChordBox1011Cell010Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell011 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell011.interpret
theorem positiveChordBox1011Cell011_valid : positiveChordBox1011Cell011.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (13/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.disk TraceData.positiveChordBox1011Cell011.diskFunction TraceData.positiveChordBox1011Cell011Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell011Node00 TraceData.positiveChordBox1011Cell011Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell011Node01 TraceData.positiveChordBox1011Cell011Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell011Node02 TraceData.positiveChordBox1011Cell011Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell011Node03 TraceData.positiveChordBox1011Cell011Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell011Node04 TraceData.positiveChordBox1011Cell011Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell011Node05 TraceData.positiveChordBox1011Cell011Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell011Node06 TraceData.positiveChordBox1011Cell011Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell011Node07 TraceData.positiveChordBox1011Cell011Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell011Node08 TraceData.positiveChordBox1011Cell011Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell011Node09 TraceData.positiveChordBox1011Cell011Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell011Node10 TraceData.positiveChordBox1011Cell011Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell011Node11 TraceData.positiveChordBox1011Cell011Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell011Node12 TraceData.positiveChordBox1011Cell011Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell011Node13 TraceData.positiveChordBox1011Cell011Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell011Node14 TraceData.positiveChordBox1011Cell011Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell011Node15 TraceData.positiveChordBox1011Cell011Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell011Node16 TraceData.positiveChordBox1011Cell011Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell011Node17 TraceData.positiveChordBox1011Cell011Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell011Node18 TraceData.positiveChordBox1011Cell011Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell011Node19 TraceData.positiveChordBox1011Cell011Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell011Node20 TraceData.positiveChordBox1011Cell011Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell011Node21 TraceData.positiveChordBox1011Cell011Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell011Node22 TraceData.positiveChordBox1011Cell011Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell011Node23 TraceData.positiveChordBox1011Cell011Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell011Node24 TraceData.positiveChordBox1011Cell011Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell011Node25 TraceData.positiveChordBox1011Cell011Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell011Node26 TraceData.positiveChordBox1011Cell011Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell011Node27 TraceData.positiveChordBox1011Cell011Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell011Node28 TraceData.positiveChordBox1011Cell011Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell011Node29 TraceData.positiveChordBox1011Cell011Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell011Node30 TraceData.positiveChordBox1011Cell011Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell011.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell011Node31 TraceData.positiveChordBox1011Cell011Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell012 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell012.interpret
theorem positiveChordBox1011Cell012_valid : positiveChordBox1011Cell012.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (29/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.disk TraceData.positiveChordBox1011Cell012.diskFunction TraceData.positiveChordBox1011Cell012Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell012Node00 TraceData.positiveChordBox1011Cell012Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell012Node01 TraceData.positiveChordBox1011Cell012Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell012Node02 TraceData.positiveChordBox1011Cell012Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell012Node03 TraceData.positiveChordBox1011Cell012Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell012Node04 TraceData.positiveChordBox1011Cell012Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell012Node05 TraceData.positiveChordBox1011Cell012Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell012Node06 TraceData.positiveChordBox1011Cell012Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell012Node07 TraceData.positiveChordBox1011Cell012Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell012Node08 TraceData.positiveChordBox1011Cell012Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell012Node09 TraceData.positiveChordBox1011Cell012Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell012Node10 TraceData.positiveChordBox1011Cell012Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell012Node11 TraceData.positiveChordBox1011Cell012Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell012Node12 TraceData.positiveChordBox1011Cell012Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell012Node13 TraceData.positiveChordBox1011Cell012Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell012Node14 TraceData.positiveChordBox1011Cell012Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell012Node15 TraceData.positiveChordBox1011Cell012Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell012Node16 TraceData.positiveChordBox1011Cell012Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell012Node17 TraceData.positiveChordBox1011Cell012Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell012Node18 TraceData.positiveChordBox1011Cell012Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell012Node19 TraceData.positiveChordBox1011Cell012Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell012Node20 TraceData.positiveChordBox1011Cell012Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell012Node21 TraceData.positiveChordBox1011Cell012Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell012Node22 TraceData.positiveChordBox1011Cell012Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell012Node23 TraceData.positiveChordBox1011Cell012Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell012Node24 TraceData.positiveChordBox1011Cell012Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell012Node25 TraceData.positiveChordBox1011Cell012Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell012Node26 TraceData.positiveChordBox1011Cell012Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell012Node27 TraceData.positiveChordBox1011Cell012Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell012Node28 TraceData.positiveChordBox1011Cell012Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell012Node29 TraceData.positiveChordBox1011Cell012Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell012Node30 TraceData.positiveChordBox1011Cell012Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell012.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell012Node31 TraceData.positiveChordBox1011Cell012Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell013 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell013.interpret
theorem positiveChordBox1011Cell013_valid : positiveChordBox1011Cell013.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (61/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.disk TraceData.positiveChordBox1011Cell013.diskFunction TraceData.positiveChordBox1011Cell013Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell013Node00 TraceData.positiveChordBox1011Cell013Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell013Node01 TraceData.positiveChordBox1011Cell013Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell013Node02 TraceData.positiveChordBox1011Cell013Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell013Node03 TraceData.positiveChordBox1011Cell013Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell013Node04 TraceData.positiveChordBox1011Cell013Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell013Node05 TraceData.positiveChordBox1011Cell013Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell013Node06 TraceData.positiveChordBox1011Cell013Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell013Node07 TraceData.positiveChordBox1011Cell013Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell013Node08 TraceData.positiveChordBox1011Cell013Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell013Node09 TraceData.positiveChordBox1011Cell013Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell013Node10 TraceData.positiveChordBox1011Cell013Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell013Node11 TraceData.positiveChordBox1011Cell013Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell013Node12 TraceData.positiveChordBox1011Cell013Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell013Node13 TraceData.positiveChordBox1011Cell013Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell013Node14 TraceData.positiveChordBox1011Cell013Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell013Node15 TraceData.positiveChordBox1011Cell013Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell013Node16 TraceData.positiveChordBox1011Cell013Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell013Node17 TraceData.positiveChordBox1011Cell013Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell013Node18 TraceData.positiveChordBox1011Cell013Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell013Node19 TraceData.positiveChordBox1011Cell013Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell013Node20 TraceData.positiveChordBox1011Cell013Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell013Node21 TraceData.positiveChordBox1011Cell013Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell013Node22 TraceData.positiveChordBox1011Cell013Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell013Node23 TraceData.positiveChordBox1011Cell013Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell013Node24 TraceData.positiveChordBox1011Cell013Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell013Node25 TraceData.positiveChordBox1011Cell013Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell013Node26 TraceData.positiveChordBox1011Cell013Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell013Node27 TraceData.positiveChordBox1011Cell013Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell013Node28 TraceData.positiveChordBox1011Cell013Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell013Node29 TraceData.positiveChordBox1011Cell013Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell013Node30 TraceData.positiveChordBox1011Cell013Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell013.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell013Node31 TraceData.positiveChordBox1011Cell013Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell014 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell014.interpret
theorem positiveChordBox1011Cell014_valid : positiveChordBox1011Cell014.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (125/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.disk TraceData.positiveChordBox1011Cell014.diskFunction TraceData.positiveChordBox1011Cell014Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell014Node00 TraceData.positiveChordBox1011Cell014Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell014Node01 TraceData.positiveChordBox1011Cell014Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell014Node02 TraceData.positiveChordBox1011Cell014Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell014Node03 TraceData.positiveChordBox1011Cell014Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell014Node04 TraceData.positiveChordBox1011Cell014Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell014Node05 TraceData.positiveChordBox1011Cell014Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell014Node06 TraceData.positiveChordBox1011Cell014Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell014Node07 TraceData.positiveChordBox1011Cell014Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell014Node08 TraceData.positiveChordBox1011Cell014Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell014Node09 TraceData.positiveChordBox1011Cell014Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell014Node10 TraceData.positiveChordBox1011Cell014Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell014Node11 TraceData.positiveChordBox1011Cell014Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell014Node12 TraceData.positiveChordBox1011Cell014Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell014Node13 TraceData.positiveChordBox1011Cell014Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell014Node14 TraceData.positiveChordBox1011Cell014Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell014Node15 TraceData.positiveChordBox1011Cell014Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell014Node16 TraceData.positiveChordBox1011Cell014Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell014Node17 TraceData.positiveChordBox1011Cell014Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell014Node18 TraceData.positiveChordBox1011Cell014Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell014Node19 TraceData.positiveChordBox1011Cell014Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell014Node20 TraceData.positiveChordBox1011Cell014Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell014Node21 TraceData.positiveChordBox1011Cell014Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell014Node22 TraceData.positiveChordBox1011Cell014Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell014Node23 TraceData.positiveChordBox1011Cell014Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell014Node24 TraceData.positiveChordBox1011Cell014Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell014Node25 TraceData.positiveChordBox1011Cell014Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell014Node26 TraceData.positiveChordBox1011Cell014Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell014Node27 TraceData.positiveChordBox1011Cell014Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell014Node28 TraceData.positiveChordBox1011Cell014Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell014Node29 TraceData.positiveChordBox1011Cell014Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell014Node30 TraceData.positiveChordBox1011Cell014Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell014.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell014Node31 TraceData.positiveChordBox1011Cell014Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell015 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell015.interpret
theorem positiveChordBox1011Cell015_valid : positiveChordBox1011Cell015.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (253/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.disk TraceData.positiveChordBox1011Cell015.diskFunction TraceData.positiveChordBox1011Cell015Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell015Node00 TraceData.positiveChordBox1011Cell015Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell015Node01 TraceData.positiveChordBox1011Cell015Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell015Node02 TraceData.positiveChordBox1011Cell015Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell015Node03 TraceData.positiveChordBox1011Cell015Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell015Node04 TraceData.positiveChordBox1011Cell015Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell015Node05 TraceData.positiveChordBox1011Cell015Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell015Node06 TraceData.positiveChordBox1011Cell015Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell015Node07 TraceData.positiveChordBox1011Cell015Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell015Node08 TraceData.positiveChordBox1011Cell015Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell015Node09 TraceData.positiveChordBox1011Cell015Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell015Node10 TraceData.positiveChordBox1011Cell015Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell015Node11 TraceData.positiveChordBox1011Cell015Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell015Node12 TraceData.positiveChordBox1011Cell015Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell015Node13 TraceData.positiveChordBox1011Cell015Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell015Node14 TraceData.positiveChordBox1011Cell015Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell015Node15 TraceData.positiveChordBox1011Cell015Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell015Node16 TraceData.positiveChordBox1011Cell015Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell015Node17 TraceData.positiveChordBox1011Cell015Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell015Node18 TraceData.positiveChordBox1011Cell015Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell015Node19 TraceData.positiveChordBox1011Cell015Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell015Node20 TraceData.positiveChordBox1011Cell015Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell015Node21 TraceData.positiveChordBox1011Cell015Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell015Node22 TraceData.positiveChordBox1011Cell015Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell015Node23 TraceData.positiveChordBox1011Cell015Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell015Node24 TraceData.positiveChordBox1011Cell015Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell015Node25 TraceData.positiveChordBox1011Cell015Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell015Node26 TraceData.positiveChordBox1011Cell015Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell015Node27 TraceData.positiveChordBox1011Cell015Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell015Node28 TraceData.positiveChordBox1011Cell015Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell015Node29 TraceData.positiveChordBox1011Cell015Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell015Node30 TraceData.positiveChordBox1011Cell015Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell015Node31 TraceData.positiveChordBox1011Cell015Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell016 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell016.interpret
theorem positiveChordBox1011Cell016_valid : positiveChordBox1011Cell016.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (509/512) (1/512) (1/256) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.disk TraceData.positiveChordBox1011Cell016.diskFunction TraceData.positiveChordBox1011Cell016Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell016Node00 TraceData.positiveChordBox1011Cell016Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell016Node01 TraceData.positiveChordBox1011Cell016Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell016Node02 TraceData.positiveChordBox1011Cell016Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell016Node03 TraceData.positiveChordBox1011Cell016Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell016Node04 TraceData.positiveChordBox1011Cell016Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell016Node05 TraceData.positiveChordBox1011Cell016Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell016Node06 TraceData.positiveChordBox1011Cell016Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell016Node07 TraceData.positiveChordBox1011Cell016Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell016Node08 TraceData.positiveChordBox1011Cell016Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell016Node09 TraceData.positiveChordBox1011Cell016Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell016Node10 TraceData.positiveChordBox1011Cell016Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell016Node11 TraceData.positiveChordBox1011Cell016Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell016Node12 TraceData.positiveChordBox1011Cell016Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell016Node13 TraceData.positiveChordBox1011Cell016Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell016Node14 TraceData.positiveChordBox1011Cell016Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell016Node15 TraceData.positiveChordBox1011Cell016Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell016Node16 TraceData.positiveChordBox1011Cell016Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell016Node17 TraceData.positiveChordBox1011Cell016Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell016Node18 TraceData.positiveChordBox1011Cell016Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell016Node19 TraceData.positiveChordBox1011Cell016Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell016Node20 TraceData.positiveChordBox1011Cell016Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell016Node21 TraceData.positiveChordBox1011Cell016Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell016Node22 TraceData.positiveChordBox1011Cell016Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell016Node23 TraceData.positiveChordBox1011Cell016Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell016Node24 TraceData.positiveChordBox1011Cell016Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell016Node25 TraceData.positiveChordBox1011Cell016Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell016Node26 TraceData.positiveChordBox1011Cell016Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell016Node27 TraceData.positiveChordBox1011Cell016Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell016Node28 TraceData.positiveChordBox1011Cell016Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell016Node29 TraceData.positiveChordBox1011Cell016Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell016Node30 TraceData.positiveChordBox1011Cell016Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell016.center (1/512) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell016Node31 TraceData.positiveChordBox1011Cell016Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1011Cell017 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1011Cell017.interpret
theorem positiveChordBox1011Cell017_valid : positiveChordBox1011Cell017.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (511/512) (1/512) (1/256) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.disk TraceData.positiveChordBox1011Cell017.diskFunction TraceData.positiveChordBox1011Cell017Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1011Cell017Node00 TraceData.positiveChordBox1011Cell017Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1011Cell017Node01 TraceData.positiveChordBox1011Cell017Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1011Cell017Node02 TraceData.positiveChordBox1011Cell017Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1011Cell017Node03 TraceData.positiveChordBox1011Cell017Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1011Cell017Node04 TraceData.positiveChordBox1011Cell017Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1011Cell017Node05 TraceData.positiveChordBox1011Cell017Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1011Cell017Node06 TraceData.positiveChordBox1011Cell017Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1011Cell017Node07 TraceData.positiveChordBox1011Cell017Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1011Cell017Node08 TraceData.positiveChordBox1011Cell017Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1011Cell017Node09 TraceData.positiveChordBox1011Cell017Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1011Cell017Node10 TraceData.positiveChordBox1011Cell017Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1011Cell017Node11 TraceData.positiveChordBox1011Cell017Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1011Cell017Node12 TraceData.positiveChordBox1011Cell017Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1011Cell017Node13 TraceData.positiveChordBox1011Cell017Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1011Cell017Node14 TraceData.positiveChordBox1011Cell017Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1011Cell017Node15 TraceData.positiveChordBox1011Cell017Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1011Cell017Node16 TraceData.positiveChordBox1011Cell017Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1011Cell017Node17 TraceData.positiveChordBox1011Cell017Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1011Cell017Node18 TraceData.positiveChordBox1011Cell017Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1011Cell017Node19 TraceData.positiveChordBox1011Cell017Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1011Cell017Node20 TraceData.positiveChordBox1011Cell017Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1011Cell017Node21 TraceData.positiveChordBox1011Cell017Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1011Cell017Node22 TraceData.positiveChordBox1011Cell017Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1011Cell017Node23 TraceData.positiveChordBox1011Cell017Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1011Cell017Node24 TraceData.positiveChordBox1011Cell017Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1011Cell017Node25 TraceData.positiveChordBox1011Cell017Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1011Cell017Node26 TraceData.positiveChordBox1011Cell017Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1011Cell017Node27 TraceData.positiveChordBox1011Cell017Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1011Cell017Node28 TraceData.positiveChordBox1011Cell017Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1011Cell017Node29 TraceData.positiveChordBox1011Cell017Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1011Cell017Node30 TraceData.positiveChordBox1011Cell017Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1011Parameters TraceData.positiveChordBox1011Cell017.center (1/512) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1011Cell017Node31 TraceData.positiveChordBox1011Cell017Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
def positiveChordBox1011Boundary : ℕ → ℚ := fun i => match i with
  | 0 => (-1/1)
  | 1 => (-255/256)
  | 2 => (-127/128)
  | 3 => (-63/64)
  | 4 => (-31/32)
  | 5 => (-15/16)
  | 6 => (-7/8)
  | 7 => (-3/4)
  | 8 => (-1/2)
  | 9 => (0/1)
  | 10 => (1/2)
  | 11 => (3/4)
  | 12 => (7/8)
  | 13 => (15/16)
  | 14 => (31/32)
  | 15 => (63/64)
  | 16 => (127/128)
  | 17 => (255/256)
  | _ => (1/1)
def positiveChordBox1011Radius : Fin 18 → ℚ := ![(1/256),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(1/4),(1/2),(1/2),(1/4),(1/8),(1/16),(1/32),(1/64),(1/128),(1/256),(1/256)]
noncomputable def positiveChordBox1011Cells : Fin 18 → JacobiChordRangeCell 32 := ![positiveChordBox1011Cell000,positiveChordBox1011Cell001,positiveChordBox1011Cell002,positiveChordBox1011Cell003,positiveChordBox1011Cell004,positiveChordBox1011Cell005,positiveChordBox1011Cell006,positiveChordBox1011Cell007,positiveChordBox1011Cell008,positiveChordBox1011Cell009,positiveChordBox1011Cell010,positiveChordBox1011Cell011,positiveChordBox1011Cell012,positiveChordBox1011Cell013,positiveChordBox1011Cell014,positiveChordBox1011Cell015,positiveChordBox1011Cell016,positiveChordBox1011Cell017]
theorem positiveChordBox1011Cells_valid : ∀ i : Fin 18, (positiveChordBox1011Cells i).Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1011Parameters (jacobiCellCenter positiveChordBox1011Boundary i) (jacobiCellRadius positiveChordBox1011Boundary i) (positiveChordBox1011Radius i) := by
  intro i
  fin_cases i
  · convert positiveChordBox1011Cell000_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell001_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell002_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell003_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell004_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell005_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell006_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell007_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell008_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell009_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell010_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell011_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell012_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell013_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell014_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell015_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell016_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
  · convert positiveChordBox1011Cell017_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1011Boundary]
theorem positiveChordBox1011_lower : (3/10000 : ℚ) < (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).radius := by decide +kernel
theorem positiveChordBox1011_rectangle_positive {t a : ℝ}
    (htl : (((11/40) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((3/10) : ℚ) : ℝ))
    (hal : (((1/2) : ℚ) : ℝ) ≤ a) (hau : a ≤ (((558827/1048576) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < thetaHorizontalPeriod t a := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1011Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1011Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1011Parameters positiveChordBox1011Parameters_valid hbt hba
    positiveChordBox1011Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1011Radius positiveChordBox1011Cells positiveChordBox1011Cells_valid
  have hl := (ComplexBall.re_bounds hb).1
  rw [← horizontalPeriod_eq_jacobiChordKernel ht0 ht85 ha0 ha1] at hl
  have hc : (((3/10000 : ℚ) : ℝ)) <
      (((combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).radius : ℚ) : ℝ) :=
    (Rat.cast_lt (K := ℝ)).mpr positiveChordBox1011_lower
  rw [show (((3/10000 : ℚ) : ℝ)) = (3/10000 : ℝ) by norm_num] at hc
  exact hc.trans_le hl

theorem positiveChordBox1011_vertical_enclosure {t : ℝ}
    (htl : (((11/40) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((3/10) : ℚ) : ℝ)) :
    verticalA t ∈ Set.Icc (((1/2) : ℚ) : ℝ) (((558827/1048576) : ℚ) : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have hdomain : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper :=
    ⟨ht0, htu.trans_lt ((by norm_num : (((3/10) : ℚ) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  have hgLower : 0 < (thetaG t (((1/2) : ℚ) : ℝ)).re := by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using thetaG_re_half_pos ht0
  have hUppert : (TraceData.positiveChordBox1011UpperParameters.interpret.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hUppera : (TraceData.positiveChordBox1011UpperParameters.interpret.abscissa.toBall 64).Contains ((((558827/1048576) : ℚ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_ratCast] using coarsen_contains (rational_contains (558827/1048576))
      (by decide +kernel : (TraceData.positiveChordBox1011UpperParameters.interpret.abscissa.toBall 64).coarsens (ComplexBall.rational (558827/1048576)))
  have hgUpper := DyadicJacobiVerticalTrace.thetaG_neg ⟨64,12,6⟩ 18446744074 ht0
    (by norm_num : 0 < (((558827/1048576) : ℚ) : ℝ)) (by norm_num : (((558827/1048576) : ℚ) : ℝ) < 1)
    TraceData.positiveChordBox1011UpperParameters.interpret (TraceData.DyadicJacobiBaseParameters.valid_of_valid ⟨64,12,6⟩ TraceData.positiveChordBox1011UpperParameters TraceData.positiveChordBox1011UpperParameters_valid)
    hUppert hUppera TraceData.positiveChordBox1011Upper.interpret
    (TraceData.DyadicJacobiVerticalTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveChordBox1011UpperParameters TraceData.positiveChordBox1011Upper TraceData.positiveChordBox1011Upper_valid)
    (by decide +kernel)
  have ha := verticalA_mem_of_boundary_signs hdomain (by norm_num) (by norm_num) hgLower hgUpper
  exact ⟨ha.1.le,ha.2.le⟩
theorem positiveChordBox1011_positive {t : ℝ}
    (htl : (((11/40) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((3/10) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < actualPeriodAlong t := by
  have ha := positiveChordBox1011_vertical_enclosure htl htu
  exact positiveChordBox1011_rectangle_positive htl htu ha.1 ha.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positiveChordBox1011_positive
