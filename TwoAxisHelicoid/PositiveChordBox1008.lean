import TwoAxisHelicoid.TraceDataPositiveChordBox1008
import TwoAxisHelicoid.TraceDataJacobiChordBridge
import TwoAxisHelicoid.TraceDataJacobiVerticalBridge
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def positiveChordBox1008Parameters : DyadicJacobiChordParameters := TraceData.positiveChordBox1008Parameters.interpret
theorem positiveChordBox1008Parameters_valid : positiveChordBox1008Parameters.Valid ⟨64,12,6⟩ 18446744074 :=
  TraceData.DyadicJacobiChordParameters.valid_of_valid ⟨64,12,6⟩ 18446744074 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Parameters_valid
noncomputable def positiveChordBox1008Cell000 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell000.interpret
theorem positiveChordBox1008Cell000_valid : positiveChordBox1008Cell000.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-16383/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.disk TraceData.positiveChordBox1008Cell000.diskFunction TraceData.positiveChordBox1008Cell000Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell000Node00 TraceData.positiveChordBox1008Cell000Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell000Node01 TraceData.positiveChordBox1008Cell000Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell000Node02 TraceData.positiveChordBox1008Cell000Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell000Node03 TraceData.positiveChordBox1008Cell000Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell000Node04 TraceData.positiveChordBox1008Cell000Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell000Node05 TraceData.positiveChordBox1008Cell000Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell000Node06 TraceData.positiveChordBox1008Cell000Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell000Node07 TraceData.positiveChordBox1008Cell000Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell000Node08 TraceData.positiveChordBox1008Cell000Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell000Node09 TraceData.positiveChordBox1008Cell000Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell000Node10 TraceData.positiveChordBox1008Cell000Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell000Node11 TraceData.positiveChordBox1008Cell000Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell000Node12 TraceData.positiveChordBox1008Cell000Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell000Node13 TraceData.positiveChordBox1008Cell000Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell000Node14 TraceData.positiveChordBox1008Cell000Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell000Node15 TraceData.positiveChordBox1008Cell000Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell000Node16 TraceData.positiveChordBox1008Cell000Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell000Node17 TraceData.positiveChordBox1008Cell000Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell000Node18 TraceData.positiveChordBox1008Cell000Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell000Node19 TraceData.positiveChordBox1008Cell000Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell000Node20 TraceData.positiveChordBox1008Cell000Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell000Node21 TraceData.positiveChordBox1008Cell000Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell000Node22 TraceData.positiveChordBox1008Cell000Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell000Node23 TraceData.positiveChordBox1008Cell000Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell000Node24 TraceData.positiveChordBox1008Cell000Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell000Node25 TraceData.positiveChordBox1008Cell000Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell000Node26 TraceData.positiveChordBox1008Cell000Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell000Node27 TraceData.positiveChordBox1008Cell000Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell000Node28 TraceData.positiveChordBox1008Cell000Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell000Node29 TraceData.positiveChordBox1008Cell000Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell000Node30 TraceData.positiveChordBox1008Cell000Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell000.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell000Node31 TraceData.positiveChordBox1008Cell000Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell001 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell001.interpret
theorem positiveChordBox1008Cell001_valid : positiveChordBox1008Cell001.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-16381/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.disk TraceData.positiveChordBox1008Cell001.diskFunction TraceData.positiveChordBox1008Cell001Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell001Node00 TraceData.positiveChordBox1008Cell001Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell001Node01 TraceData.positiveChordBox1008Cell001Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell001Node02 TraceData.positiveChordBox1008Cell001Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell001Node03 TraceData.positiveChordBox1008Cell001Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell001Node04 TraceData.positiveChordBox1008Cell001Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell001Node05 TraceData.positiveChordBox1008Cell001Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell001Node06 TraceData.positiveChordBox1008Cell001Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell001Node07 TraceData.positiveChordBox1008Cell001Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell001Node08 TraceData.positiveChordBox1008Cell001Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell001Node09 TraceData.positiveChordBox1008Cell001Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell001Node10 TraceData.positiveChordBox1008Cell001Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell001Node11 TraceData.positiveChordBox1008Cell001Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell001Node12 TraceData.positiveChordBox1008Cell001Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell001Node13 TraceData.positiveChordBox1008Cell001Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell001Node14 TraceData.positiveChordBox1008Cell001Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell001Node15 TraceData.positiveChordBox1008Cell001Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell001Node16 TraceData.positiveChordBox1008Cell001Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell001Node17 TraceData.positiveChordBox1008Cell001Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell001Node18 TraceData.positiveChordBox1008Cell001Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell001Node19 TraceData.positiveChordBox1008Cell001Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell001Node20 TraceData.positiveChordBox1008Cell001Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell001Node21 TraceData.positiveChordBox1008Cell001Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell001Node22 TraceData.positiveChordBox1008Cell001Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell001Node23 TraceData.positiveChordBox1008Cell001Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell001Node24 TraceData.positiveChordBox1008Cell001Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell001Node25 TraceData.positiveChordBox1008Cell001Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell001Node26 TraceData.positiveChordBox1008Cell001Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell001Node27 TraceData.positiveChordBox1008Cell001Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell001Node28 TraceData.positiveChordBox1008Cell001Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell001Node29 TraceData.positiveChordBox1008Cell001Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell001Node30 TraceData.positiveChordBox1008Cell001Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell001.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell001Node31 TraceData.positiveChordBox1008Cell001Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell002 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell002.interpret
theorem positiveChordBox1008Cell002_valid : positiveChordBox1008Cell002.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-16379/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.disk TraceData.positiveChordBox1008Cell002.diskFunction TraceData.positiveChordBox1008Cell002Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell002Node00 TraceData.positiveChordBox1008Cell002Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell002Node01 TraceData.positiveChordBox1008Cell002Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell002Node02 TraceData.positiveChordBox1008Cell002Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell002Node03 TraceData.positiveChordBox1008Cell002Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell002Node04 TraceData.positiveChordBox1008Cell002Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell002Node05 TraceData.positiveChordBox1008Cell002Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell002Node06 TraceData.positiveChordBox1008Cell002Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell002Node07 TraceData.positiveChordBox1008Cell002Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell002Node08 TraceData.positiveChordBox1008Cell002Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell002Node09 TraceData.positiveChordBox1008Cell002Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell002Node10 TraceData.positiveChordBox1008Cell002Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell002Node11 TraceData.positiveChordBox1008Cell002Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell002Node12 TraceData.positiveChordBox1008Cell002Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell002Node13 TraceData.positiveChordBox1008Cell002Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell002Node14 TraceData.positiveChordBox1008Cell002Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell002Node15 TraceData.positiveChordBox1008Cell002Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell002Node16 TraceData.positiveChordBox1008Cell002Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell002Node17 TraceData.positiveChordBox1008Cell002Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell002Node18 TraceData.positiveChordBox1008Cell002Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell002Node19 TraceData.positiveChordBox1008Cell002Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell002Node20 TraceData.positiveChordBox1008Cell002Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell002Node21 TraceData.positiveChordBox1008Cell002Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell002Node22 TraceData.positiveChordBox1008Cell002Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell002Node23 TraceData.positiveChordBox1008Cell002Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell002Node24 TraceData.positiveChordBox1008Cell002Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell002Node25 TraceData.positiveChordBox1008Cell002Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell002Node26 TraceData.positiveChordBox1008Cell002Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell002Node27 TraceData.positiveChordBox1008Cell002Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell002Node28 TraceData.positiveChordBox1008Cell002Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell002Node29 TraceData.positiveChordBox1008Cell002Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell002Node30 TraceData.positiveChordBox1008Cell002Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell002.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell002Node31 TraceData.positiveChordBox1008Cell002Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell003 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell003.interpret
theorem positiveChordBox1008Cell003_valid : positiveChordBox1008Cell003.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-16377/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.disk TraceData.positiveChordBox1008Cell003.diskFunction TraceData.positiveChordBox1008Cell003Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell003Node00 TraceData.positiveChordBox1008Cell003Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell003Node01 TraceData.positiveChordBox1008Cell003Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell003Node02 TraceData.positiveChordBox1008Cell003Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell003Node03 TraceData.positiveChordBox1008Cell003Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell003Node04 TraceData.positiveChordBox1008Cell003Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell003Node05 TraceData.positiveChordBox1008Cell003Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell003Node06 TraceData.positiveChordBox1008Cell003Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell003Node07 TraceData.positiveChordBox1008Cell003Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell003Node08 TraceData.positiveChordBox1008Cell003Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell003Node09 TraceData.positiveChordBox1008Cell003Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell003Node10 TraceData.positiveChordBox1008Cell003Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell003Node11 TraceData.positiveChordBox1008Cell003Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell003Node12 TraceData.positiveChordBox1008Cell003Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell003Node13 TraceData.positiveChordBox1008Cell003Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell003Node14 TraceData.positiveChordBox1008Cell003Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell003Node15 TraceData.positiveChordBox1008Cell003Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell003Node16 TraceData.positiveChordBox1008Cell003Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell003Node17 TraceData.positiveChordBox1008Cell003Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell003Node18 TraceData.positiveChordBox1008Cell003Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell003Node19 TraceData.positiveChordBox1008Cell003Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell003Node20 TraceData.positiveChordBox1008Cell003Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell003Node21 TraceData.positiveChordBox1008Cell003Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell003Node22 TraceData.positiveChordBox1008Cell003Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell003Node23 TraceData.positiveChordBox1008Cell003Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell003Node24 TraceData.positiveChordBox1008Cell003Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell003Node25 TraceData.positiveChordBox1008Cell003Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell003Node26 TraceData.positiveChordBox1008Cell003Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell003Node27 TraceData.positiveChordBox1008Cell003Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell003Node28 TraceData.positiveChordBox1008Cell003Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell003Node29 TraceData.positiveChordBox1008Cell003Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell003Node30 TraceData.positiveChordBox1008Cell003Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell003.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell003Node31 TraceData.positiveChordBox1008Cell003Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell004 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell004.interpret
theorem positiveChordBox1008Cell004_valid : positiveChordBox1008Cell004.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-16375/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.disk TraceData.positiveChordBox1008Cell004.diskFunction TraceData.positiveChordBox1008Cell004Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell004Node00 TraceData.positiveChordBox1008Cell004Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell004Node01 TraceData.positiveChordBox1008Cell004Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell004Node02 TraceData.positiveChordBox1008Cell004Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell004Node03 TraceData.positiveChordBox1008Cell004Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell004Node04 TraceData.positiveChordBox1008Cell004Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell004Node05 TraceData.positiveChordBox1008Cell004Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell004Node06 TraceData.positiveChordBox1008Cell004Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell004Node07 TraceData.positiveChordBox1008Cell004Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell004Node08 TraceData.positiveChordBox1008Cell004Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell004Node09 TraceData.positiveChordBox1008Cell004Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell004Node10 TraceData.positiveChordBox1008Cell004Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell004Node11 TraceData.positiveChordBox1008Cell004Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell004Node12 TraceData.positiveChordBox1008Cell004Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell004Node13 TraceData.positiveChordBox1008Cell004Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell004Node14 TraceData.positiveChordBox1008Cell004Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell004Node15 TraceData.positiveChordBox1008Cell004Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell004Node16 TraceData.positiveChordBox1008Cell004Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell004Node17 TraceData.positiveChordBox1008Cell004Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell004Node18 TraceData.positiveChordBox1008Cell004Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell004Node19 TraceData.positiveChordBox1008Cell004Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell004Node20 TraceData.positiveChordBox1008Cell004Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell004Node21 TraceData.positiveChordBox1008Cell004Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell004Node22 TraceData.positiveChordBox1008Cell004Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell004Node23 TraceData.positiveChordBox1008Cell004Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell004Node24 TraceData.positiveChordBox1008Cell004Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell004Node25 TraceData.positiveChordBox1008Cell004Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell004Node26 TraceData.positiveChordBox1008Cell004Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell004Node27 TraceData.positiveChordBox1008Cell004Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell004Node28 TraceData.positiveChordBox1008Cell004Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell004Node29 TraceData.positiveChordBox1008Cell004Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell004Node30 TraceData.positiveChordBox1008Cell004Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell004.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell004Node31 TraceData.positiveChordBox1008Cell004Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell005 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell005.interpret
theorem positiveChordBox1008Cell005_valid : positiveChordBox1008Cell005.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-16373/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.disk TraceData.positiveChordBox1008Cell005.diskFunction TraceData.positiveChordBox1008Cell005Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell005Node00 TraceData.positiveChordBox1008Cell005Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell005Node01 TraceData.positiveChordBox1008Cell005Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell005Node02 TraceData.positiveChordBox1008Cell005Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell005Node03 TraceData.positiveChordBox1008Cell005Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell005Node04 TraceData.positiveChordBox1008Cell005Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell005Node05 TraceData.positiveChordBox1008Cell005Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell005Node06 TraceData.positiveChordBox1008Cell005Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell005Node07 TraceData.positiveChordBox1008Cell005Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell005Node08 TraceData.positiveChordBox1008Cell005Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell005Node09 TraceData.positiveChordBox1008Cell005Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell005Node10 TraceData.positiveChordBox1008Cell005Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell005Node11 TraceData.positiveChordBox1008Cell005Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell005Node12 TraceData.positiveChordBox1008Cell005Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell005Node13 TraceData.positiveChordBox1008Cell005Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell005Node14 TraceData.positiveChordBox1008Cell005Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell005Node15 TraceData.positiveChordBox1008Cell005Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell005Node16 TraceData.positiveChordBox1008Cell005Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell005Node17 TraceData.positiveChordBox1008Cell005Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell005Node18 TraceData.positiveChordBox1008Cell005Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell005Node19 TraceData.positiveChordBox1008Cell005Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell005Node20 TraceData.positiveChordBox1008Cell005Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell005Node21 TraceData.positiveChordBox1008Cell005Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell005Node22 TraceData.positiveChordBox1008Cell005Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell005Node23 TraceData.positiveChordBox1008Cell005Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell005Node24 TraceData.positiveChordBox1008Cell005Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell005Node25 TraceData.positiveChordBox1008Cell005Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell005Node26 TraceData.positiveChordBox1008Cell005Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell005Node27 TraceData.positiveChordBox1008Cell005Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell005Node28 TraceData.positiveChordBox1008Cell005Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell005Node29 TraceData.positiveChordBox1008Cell005Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell005Node30 TraceData.positiveChordBox1008Cell005Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell005.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell005Node31 TraceData.positiveChordBox1008Cell005Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell006 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell006.interpret
theorem positiveChordBox1008Cell006_valid : positiveChordBox1008Cell006.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-16371/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.disk TraceData.positiveChordBox1008Cell006.diskFunction TraceData.positiveChordBox1008Cell006Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell006Node00 TraceData.positiveChordBox1008Cell006Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell006Node01 TraceData.positiveChordBox1008Cell006Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell006Node02 TraceData.positiveChordBox1008Cell006Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell006Node03 TraceData.positiveChordBox1008Cell006Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell006Node04 TraceData.positiveChordBox1008Cell006Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell006Node05 TraceData.positiveChordBox1008Cell006Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell006Node06 TraceData.positiveChordBox1008Cell006Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell006Node07 TraceData.positiveChordBox1008Cell006Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell006Node08 TraceData.positiveChordBox1008Cell006Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell006Node09 TraceData.positiveChordBox1008Cell006Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell006Node10 TraceData.positiveChordBox1008Cell006Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell006Node11 TraceData.positiveChordBox1008Cell006Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell006Node12 TraceData.positiveChordBox1008Cell006Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell006Node13 TraceData.positiveChordBox1008Cell006Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell006Node14 TraceData.positiveChordBox1008Cell006Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell006Node15 TraceData.positiveChordBox1008Cell006Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell006Node16 TraceData.positiveChordBox1008Cell006Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell006Node17 TraceData.positiveChordBox1008Cell006Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell006Node18 TraceData.positiveChordBox1008Cell006Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell006Node19 TraceData.positiveChordBox1008Cell006Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell006Node20 TraceData.positiveChordBox1008Cell006Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell006Node21 TraceData.positiveChordBox1008Cell006Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell006Node22 TraceData.positiveChordBox1008Cell006Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell006Node23 TraceData.positiveChordBox1008Cell006Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell006Node24 TraceData.positiveChordBox1008Cell006Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell006Node25 TraceData.positiveChordBox1008Cell006Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell006Node26 TraceData.positiveChordBox1008Cell006Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell006Node27 TraceData.positiveChordBox1008Cell006Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell006Node28 TraceData.positiveChordBox1008Cell006Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell006Node29 TraceData.positiveChordBox1008Cell006Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell006Node30 TraceData.positiveChordBox1008Cell006Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell006.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell006Node31 TraceData.positiveChordBox1008Cell006Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell007 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell007.interpret
theorem positiveChordBox1008Cell007_valid : positiveChordBox1008Cell007.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-16369/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.disk TraceData.positiveChordBox1008Cell007.diskFunction TraceData.positiveChordBox1008Cell007Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell007Node00 TraceData.positiveChordBox1008Cell007Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell007Node01 TraceData.positiveChordBox1008Cell007Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell007Node02 TraceData.positiveChordBox1008Cell007Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell007Node03 TraceData.positiveChordBox1008Cell007Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell007Node04 TraceData.positiveChordBox1008Cell007Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell007Node05 TraceData.positiveChordBox1008Cell007Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell007Node06 TraceData.positiveChordBox1008Cell007Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell007Node07 TraceData.positiveChordBox1008Cell007Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell007Node08 TraceData.positiveChordBox1008Cell007Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell007Node09 TraceData.positiveChordBox1008Cell007Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell007Node10 TraceData.positiveChordBox1008Cell007Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell007Node11 TraceData.positiveChordBox1008Cell007Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell007Node12 TraceData.positiveChordBox1008Cell007Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell007Node13 TraceData.positiveChordBox1008Cell007Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell007Node14 TraceData.positiveChordBox1008Cell007Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell007Node15 TraceData.positiveChordBox1008Cell007Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell007Node16 TraceData.positiveChordBox1008Cell007Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell007Node17 TraceData.positiveChordBox1008Cell007Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell007Node18 TraceData.positiveChordBox1008Cell007Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell007Node19 TraceData.positiveChordBox1008Cell007Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell007Node20 TraceData.positiveChordBox1008Cell007Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell007Node21 TraceData.positiveChordBox1008Cell007Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell007Node22 TraceData.positiveChordBox1008Cell007Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell007Node23 TraceData.positiveChordBox1008Cell007Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell007Node24 TraceData.positiveChordBox1008Cell007Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell007Node25 TraceData.positiveChordBox1008Cell007Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell007Node26 TraceData.positiveChordBox1008Cell007Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell007Node27 TraceData.positiveChordBox1008Cell007Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell007Node28 TraceData.positiveChordBox1008Cell007Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell007Node29 TraceData.positiveChordBox1008Cell007Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell007Node30 TraceData.positiveChordBox1008Cell007Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell007.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell007Node31 TraceData.positiveChordBox1008Cell007Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell008 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell008.interpret
theorem positiveChordBox1008Cell008_valid : positiveChordBox1008Cell008.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-16367/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.disk TraceData.positiveChordBox1008Cell008.diskFunction TraceData.positiveChordBox1008Cell008Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell008Node00 TraceData.positiveChordBox1008Cell008Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell008Node01 TraceData.positiveChordBox1008Cell008Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell008Node02 TraceData.positiveChordBox1008Cell008Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell008Node03 TraceData.positiveChordBox1008Cell008Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell008Node04 TraceData.positiveChordBox1008Cell008Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell008Node05 TraceData.positiveChordBox1008Cell008Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell008Node06 TraceData.positiveChordBox1008Cell008Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell008Node07 TraceData.positiveChordBox1008Cell008Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell008Node08 TraceData.positiveChordBox1008Cell008Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell008Node09 TraceData.positiveChordBox1008Cell008Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell008Node10 TraceData.positiveChordBox1008Cell008Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell008Node11 TraceData.positiveChordBox1008Cell008Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell008Node12 TraceData.positiveChordBox1008Cell008Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell008Node13 TraceData.positiveChordBox1008Cell008Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell008Node14 TraceData.positiveChordBox1008Cell008Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell008Node15 TraceData.positiveChordBox1008Cell008Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell008Node16 TraceData.positiveChordBox1008Cell008Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell008Node17 TraceData.positiveChordBox1008Cell008Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell008Node18 TraceData.positiveChordBox1008Cell008Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell008Node19 TraceData.positiveChordBox1008Cell008Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell008Node20 TraceData.positiveChordBox1008Cell008Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell008Node21 TraceData.positiveChordBox1008Cell008Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell008Node22 TraceData.positiveChordBox1008Cell008Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell008Node23 TraceData.positiveChordBox1008Cell008Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell008Node24 TraceData.positiveChordBox1008Cell008Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell008Node25 TraceData.positiveChordBox1008Cell008Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell008Node26 TraceData.positiveChordBox1008Cell008Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell008Node27 TraceData.positiveChordBox1008Cell008Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell008Node28 TraceData.positiveChordBox1008Cell008Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell008Node29 TraceData.positiveChordBox1008Cell008Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell008Node30 TraceData.positiveChordBox1008Cell008Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell008.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell008Node31 TraceData.positiveChordBox1008Cell008Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell009 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell009.interpret
theorem positiveChordBox1008Cell009_valid : positiveChordBox1008Cell009.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-16365/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.disk TraceData.positiveChordBox1008Cell009.diskFunction TraceData.positiveChordBox1008Cell009Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell009Node00 TraceData.positiveChordBox1008Cell009Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell009Node01 TraceData.positiveChordBox1008Cell009Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell009Node02 TraceData.positiveChordBox1008Cell009Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell009Node03 TraceData.positiveChordBox1008Cell009Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell009Node04 TraceData.positiveChordBox1008Cell009Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell009Node05 TraceData.positiveChordBox1008Cell009Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell009Node06 TraceData.positiveChordBox1008Cell009Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell009Node07 TraceData.positiveChordBox1008Cell009Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell009Node08 TraceData.positiveChordBox1008Cell009Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell009Node09 TraceData.positiveChordBox1008Cell009Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell009Node10 TraceData.positiveChordBox1008Cell009Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell009Node11 TraceData.positiveChordBox1008Cell009Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell009Node12 TraceData.positiveChordBox1008Cell009Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell009Node13 TraceData.positiveChordBox1008Cell009Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell009Node14 TraceData.positiveChordBox1008Cell009Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell009Node15 TraceData.positiveChordBox1008Cell009Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell009Node16 TraceData.positiveChordBox1008Cell009Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell009Node17 TraceData.positiveChordBox1008Cell009Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell009Node18 TraceData.positiveChordBox1008Cell009Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell009Node19 TraceData.positiveChordBox1008Cell009Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell009Node20 TraceData.positiveChordBox1008Cell009Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell009Node21 TraceData.positiveChordBox1008Cell009Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell009Node22 TraceData.positiveChordBox1008Cell009Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell009Node23 TraceData.positiveChordBox1008Cell009Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell009Node24 TraceData.positiveChordBox1008Cell009Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell009Node25 TraceData.positiveChordBox1008Cell009Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell009Node26 TraceData.positiveChordBox1008Cell009Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell009Node27 TraceData.positiveChordBox1008Cell009Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell009Node28 TraceData.positiveChordBox1008Cell009Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell009Node29 TraceData.positiveChordBox1008Cell009Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell009Node30 TraceData.positiveChordBox1008Cell009Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell009.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell009Node31 TraceData.positiveChordBox1008Cell009Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell010 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell010.interpret
theorem positiveChordBox1008Cell010_valid : positiveChordBox1008Cell010.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-8181/8192) (1/8192) (1/4096) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.disk TraceData.positiveChordBox1008Cell010.diskFunction TraceData.positiveChordBox1008Cell010Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell010Node00 TraceData.positiveChordBox1008Cell010Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell010Node01 TraceData.positiveChordBox1008Cell010Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell010Node02 TraceData.positiveChordBox1008Cell010Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell010Node03 TraceData.positiveChordBox1008Cell010Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell010Node04 TraceData.positiveChordBox1008Cell010Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell010Node05 TraceData.positiveChordBox1008Cell010Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell010Node06 TraceData.positiveChordBox1008Cell010Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell010Node07 TraceData.positiveChordBox1008Cell010Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell010Node08 TraceData.positiveChordBox1008Cell010Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell010Node09 TraceData.positiveChordBox1008Cell010Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell010Node10 TraceData.positiveChordBox1008Cell010Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell010Node11 TraceData.positiveChordBox1008Cell010Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell010Node12 TraceData.positiveChordBox1008Cell010Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell010Node13 TraceData.positiveChordBox1008Cell010Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell010Node14 TraceData.positiveChordBox1008Cell010Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell010Node15 TraceData.positiveChordBox1008Cell010Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell010Node16 TraceData.positiveChordBox1008Cell010Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell010Node17 TraceData.positiveChordBox1008Cell010Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell010Node18 TraceData.positiveChordBox1008Cell010Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell010Node19 TraceData.positiveChordBox1008Cell010Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell010Node20 TraceData.positiveChordBox1008Cell010Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell010Node21 TraceData.positiveChordBox1008Cell010Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell010Node22 TraceData.positiveChordBox1008Cell010Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell010Node23 TraceData.positiveChordBox1008Cell010Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell010Node24 TraceData.positiveChordBox1008Cell010Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell010Node25 TraceData.positiveChordBox1008Cell010Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell010Node26 TraceData.positiveChordBox1008Cell010Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell010Node27 TraceData.positiveChordBox1008Cell010Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell010Node28 TraceData.positiveChordBox1008Cell010Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell010Node29 TraceData.positiveChordBox1008Cell010Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell010Node30 TraceData.positiveChordBox1008Cell010Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell010.center (1/8192) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell010Node31 TraceData.positiveChordBox1008Cell010Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell011 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell011.interpret
theorem positiveChordBox1008Cell011_valid : positiveChordBox1008Cell011.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-4089/4096) (1/4096) (1/2048) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.disk TraceData.positiveChordBox1008Cell011.diskFunction TraceData.positiveChordBox1008Cell011Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell011Node00 TraceData.positiveChordBox1008Cell011Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell011Node01 TraceData.positiveChordBox1008Cell011Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell011Node02 TraceData.positiveChordBox1008Cell011Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell011Node03 TraceData.positiveChordBox1008Cell011Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell011Node04 TraceData.positiveChordBox1008Cell011Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell011Node05 TraceData.positiveChordBox1008Cell011Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell011Node06 TraceData.positiveChordBox1008Cell011Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell011Node07 TraceData.positiveChordBox1008Cell011Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell011Node08 TraceData.positiveChordBox1008Cell011Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell011Node09 TraceData.positiveChordBox1008Cell011Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell011Node10 TraceData.positiveChordBox1008Cell011Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell011Node11 TraceData.positiveChordBox1008Cell011Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell011Node12 TraceData.positiveChordBox1008Cell011Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell011Node13 TraceData.positiveChordBox1008Cell011Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell011Node14 TraceData.positiveChordBox1008Cell011Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell011Node15 TraceData.positiveChordBox1008Cell011Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell011Node16 TraceData.positiveChordBox1008Cell011Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell011Node17 TraceData.positiveChordBox1008Cell011Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell011Node18 TraceData.positiveChordBox1008Cell011Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell011Node19 TraceData.positiveChordBox1008Cell011Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell011Node20 TraceData.positiveChordBox1008Cell011Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell011Node21 TraceData.positiveChordBox1008Cell011Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell011Node22 TraceData.positiveChordBox1008Cell011Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell011Node23 TraceData.positiveChordBox1008Cell011Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell011Node24 TraceData.positiveChordBox1008Cell011Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell011Node25 TraceData.positiveChordBox1008Cell011Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell011Node26 TraceData.positiveChordBox1008Cell011Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell011Node27 TraceData.positiveChordBox1008Cell011Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell011Node28 TraceData.positiveChordBox1008Cell011Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell011Node29 TraceData.positiveChordBox1008Cell011Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell011Node30 TraceData.positiveChordBox1008Cell011Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell011.center (1/4096) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell011Node31 TraceData.positiveChordBox1008Cell011Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell012 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell012.interpret
theorem positiveChordBox1008Cell012_valid : positiveChordBox1008Cell012.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-2043/2048) (1/2048) (1/1024) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.disk TraceData.positiveChordBox1008Cell012.diskFunction TraceData.positiveChordBox1008Cell012Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell012Node00 TraceData.positiveChordBox1008Cell012Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell012Node01 TraceData.positiveChordBox1008Cell012Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell012Node02 TraceData.positiveChordBox1008Cell012Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell012Node03 TraceData.positiveChordBox1008Cell012Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell012Node04 TraceData.positiveChordBox1008Cell012Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell012Node05 TraceData.positiveChordBox1008Cell012Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell012Node06 TraceData.positiveChordBox1008Cell012Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell012Node07 TraceData.positiveChordBox1008Cell012Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell012Node08 TraceData.positiveChordBox1008Cell012Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell012Node09 TraceData.positiveChordBox1008Cell012Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell012Node10 TraceData.positiveChordBox1008Cell012Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell012Node11 TraceData.positiveChordBox1008Cell012Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell012Node12 TraceData.positiveChordBox1008Cell012Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell012Node13 TraceData.positiveChordBox1008Cell012Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell012Node14 TraceData.positiveChordBox1008Cell012Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell012Node15 TraceData.positiveChordBox1008Cell012Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell012Node16 TraceData.positiveChordBox1008Cell012Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell012Node17 TraceData.positiveChordBox1008Cell012Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell012Node18 TraceData.positiveChordBox1008Cell012Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell012Node19 TraceData.positiveChordBox1008Cell012Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell012Node20 TraceData.positiveChordBox1008Cell012Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell012Node21 TraceData.positiveChordBox1008Cell012Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell012Node22 TraceData.positiveChordBox1008Cell012Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell012Node23 TraceData.positiveChordBox1008Cell012Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell012Node24 TraceData.positiveChordBox1008Cell012Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell012Node25 TraceData.positiveChordBox1008Cell012Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell012Node26 TraceData.positiveChordBox1008Cell012Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell012Node27 TraceData.positiveChordBox1008Cell012Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell012Node28 TraceData.positiveChordBox1008Cell012Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell012Node29 TraceData.positiveChordBox1008Cell012Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell012Node30 TraceData.positiveChordBox1008Cell012Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell012.center (1/2048) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell012Node31 TraceData.positiveChordBox1008Cell012Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell013 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell013.interpret
theorem positiveChordBox1008Cell013_valid : positiveChordBox1008Cell013.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-2041/2048) (1/2048) (1/1024) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.disk TraceData.positiveChordBox1008Cell013.diskFunction TraceData.positiveChordBox1008Cell013Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell013Node00 TraceData.positiveChordBox1008Cell013Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell013Node01 TraceData.positiveChordBox1008Cell013Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell013Node02 TraceData.positiveChordBox1008Cell013Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell013Node03 TraceData.positiveChordBox1008Cell013Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell013Node04 TraceData.positiveChordBox1008Cell013Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell013Node05 TraceData.positiveChordBox1008Cell013Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell013Node06 TraceData.positiveChordBox1008Cell013Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell013Node07 TraceData.positiveChordBox1008Cell013Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell013Node08 TraceData.positiveChordBox1008Cell013Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell013Node09 TraceData.positiveChordBox1008Cell013Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell013Node10 TraceData.positiveChordBox1008Cell013Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell013Node11 TraceData.positiveChordBox1008Cell013Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell013Node12 TraceData.positiveChordBox1008Cell013Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell013Node13 TraceData.positiveChordBox1008Cell013Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell013Node14 TraceData.positiveChordBox1008Cell013Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell013Node15 TraceData.positiveChordBox1008Cell013Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell013Node16 TraceData.positiveChordBox1008Cell013Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell013Node17 TraceData.positiveChordBox1008Cell013Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell013Node18 TraceData.positiveChordBox1008Cell013Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell013Node19 TraceData.positiveChordBox1008Cell013Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell013Node20 TraceData.positiveChordBox1008Cell013Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell013Node21 TraceData.positiveChordBox1008Cell013Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell013Node22 TraceData.positiveChordBox1008Cell013Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell013Node23 TraceData.positiveChordBox1008Cell013Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell013Node24 TraceData.positiveChordBox1008Cell013Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell013Node25 TraceData.positiveChordBox1008Cell013Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell013Node26 TraceData.positiveChordBox1008Cell013Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell013Node27 TraceData.positiveChordBox1008Cell013Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell013Node28 TraceData.positiveChordBox1008Cell013Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell013Node29 TraceData.positiveChordBox1008Cell013Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell013Node30 TraceData.positiveChordBox1008Cell013Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell013.center (1/2048) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell013Node31 TraceData.positiveChordBox1008Cell013Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell014 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell014.interpret
theorem positiveChordBox1008Cell014_valid : positiveChordBox1008Cell014.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-509/512) (1/512) (1/256) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.disk TraceData.positiveChordBox1008Cell014.diskFunction TraceData.positiveChordBox1008Cell014Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell014Node00 TraceData.positiveChordBox1008Cell014Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell014Node01 TraceData.positiveChordBox1008Cell014Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell014Node02 TraceData.positiveChordBox1008Cell014Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell014Node03 TraceData.positiveChordBox1008Cell014Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell014Node04 TraceData.positiveChordBox1008Cell014Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell014Node05 TraceData.positiveChordBox1008Cell014Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell014Node06 TraceData.positiveChordBox1008Cell014Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell014Node07 TraceData.positiveChordBox1008Cell014Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell014Node08 TraceData.positiveChordBox1008Cell014Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell014Node09 TraceData.positiveChordBox1008Cell014Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell014Node10 TraceData.positiveChordBox1008Cell014Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell014Node11 TraceData.positiveChordBox1008Cell014Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell014Node12 TraceData.positiveChordBox1008Cell014Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell014Node13 TraceData.positiveChordBox1008Cell014Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell014Node14 TraceData.positiveChordBox1008Cell014Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell014Node15 TraceData.positiveChordBox1008Cell014Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell014Node16 TraceData.positiveChordBox1008Cell014Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell014Node17 TraceData.positiveChordBox1008Cell014Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell014Node18 TraceData.positiveChordBox1008Cell014Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell014Node19 TraceData.positiveChordBox1008Cell014Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell014Node20 TraceData.positiveChordBox1008Cell014Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell014Node21 TraceData.positiveChordBox1008Cell014Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell014Node22 TraceData.positiveChordBox1008Cell014Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell014Node23 TraceData.positiveChordBox1008Cell014Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell014Node24 TraceData.positiveChordBox1008Cell014Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell014Node25 TraceData.positiveChordBox1008Cell014Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell014Node26 TraceData.positiveChordBox1008Cell014Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell014Node27 TraceData.positiveChordBox1008Cell014Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell014Node28 TraceData.positiveChordBox1008Cell014Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell014Node29 TraceData.positiveChordBox1008Cell014Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell014Node30 TraceData.positiveChordBox1008Cell014Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell014.center (1/512) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell014Node31 TraceData.positiveChordBox1008Cell014Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell015 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell015.interpret
theorem positiveChordBox1008Cell015_valid : positiveChordBox1008Cell015.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-253/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.disk TraceData.positiveChordBox1008Cell015.diskFunction TraceData.positiveChordBox1008Cell015Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell015Node00 TraceData.positiveChordBox1008Cell015Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell015Node01 TraceData.positiveChordBox1008Cell015Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell015Node02 TraceData.positiveChordBox1008Cell015Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell015Node03 TraceData.positiveChordBox1008Cell015Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell015Node04 TraceData.positiveChordBox1008Cell015Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell015Node05 TraceData.positiveChordBox1008Cell015Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell015Node06 TraceData.positiveChordBox1008Cell015Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell015Node07 TraceData.positiveChordBox1008Cell015Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell015Node08 TraceData.positiveChordBox1008Cell015Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell015Node09 TraceData.positiveChordBox1008Cell015Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell015Node10 TraceData.positiveChordBox1008Cell015Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell015Node11 TraceData.positiveChordBox1008Cell015Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell015Node12 TraceData.positiveChordBox1008Cell015Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell015Node13 TraceData.positiveChordBox1008Cell015Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell015Node14 TraceData.positiveChordBox1008Cell015Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell015Node15 TraceData.positiveChordBox1008Cell015Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell015Node16 TraceData.positiveChordBox1008Cell015Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell015Node17 TraceData.positiveChordBox1008Cell015Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell015Node18 TraceData.positiveChordBox1008Cell015Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell015Node19 TraceData.positiveChordBox1008Cell015Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell015Node20 TraceData.positiveChordBox1008Cell015Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell015Node21 TraceData.positiveChordBox1008Cell015Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell015Node22 TraceData.positiveChordBox1008Cell015Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell015Node23 TraceData.positiveChordBox1008Cell015Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell015Node24 TraceData.positiveChordBox1008Cell015Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell015Node25 TraceData.positiveChordBox1008Cell015Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell015Node26 TraceData.positiveChordBox1008Cell015Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell015Node27 TraceData.positiveChordBox1008Cell015Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell015Node28 TraceData.positiveChordBox1008Cell015Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell015Node29 TraceData.positiveChordBox1008Cell015Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell015Node30 TraceData.positiveChordBox1008Cell015Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell015.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell015Node31 TraceData.positiveChordBox1008Cell015Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell016 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell016.interpret
theorem positiveChordBox1008Cell016_valid : positiveChordBox1008Cell016.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-125/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.disk TraceData.positiveChordBox1008Cell016.diskFunction TraceData.positiveChordBox1008Cell016Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell016Node00 TraceData.positiveChordBox1008Cell016Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell016Node01 TraceData.positiveChordBox1008Cell016Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell016Node02 TraceData.positiveChordBox1008Cell016Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell016Node03 TraceData.positiveChordBox1008Cell016Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell016Node04 TraceData.positiveChordBox1008Cell016Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell016Node05 TraceData.positiveChordBox1008Cell016Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell016Node06 TraceData.positiveChordBox1008Cell016Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell016Node07 TraceData.positiveChordBox1008Cell016Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell016Node08 TraceData.positiveChordBox1008Cell016Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell016Node09 TraceData.positiveChordBox1008Cell016Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell016Node10 TraceData.positiveChordBox1008Cell016Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell016Node11 TraceData.positiveChordBox1008Cell016Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell016Node12 TraceData.positiveChordBox1008Cell016Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell016Node13 TraceData.positiveChordBox1008Cell016Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell016Node14 TraceData.positiveChordBox1008Cell016Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell016Node15 TraceData.positiveChordBox1008Cell016Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell016Node16 TraceData.positiveChordBox1008Cell016Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell016Node17 TraceData.positiveChordBox1008Cell016Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell016Node18 TraceData.positiveChordBox1008Cell016Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell016Node19 TraceData.positiveChordBox1008Cell016Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell016Node20 TraceData.positiveChordBox1008Cell016Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell016Node21 TraceData.positiveChordBox1008Cell016Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell016Node22 TraceData.positiveChordBox1008Cell016Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell016Node23 TraceData.positiveChordBox1008Cell016Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell016Node24 TraceData.positiveChordBox1008Cell016Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell016Node25 TraceData.positiveChordBox1008Cell016Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell016Node26 TraceData.positiveChordBox1008Cell016Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell016Node27 TraceData.positiveChordBox1008Cell016Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell016Node28 TraceData.positiveChordBox1008Cell016Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell016Node29 TraceData.positiveChordBox1008Cell016Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell016Node30 TraceData.positiveChordBox1008Cell016Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell016.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell016Node31 TraceData.positiveChordBox1008Cell016Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell017 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell017.interpret
theorem positiveChordBox1008Cell017_valid : positiveChordBox1008Cell017.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-61/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.disk TraceData.positiveChordBox1008Cell017.diskFunction TraceData.positiveChordBox1008Cell017Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell017Node00 TraceData.positiveChordBox1008Cell017Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell017Node01 TraceData.positiveChordBox1008Cell017Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell017Node02 TraceData.positiveChordBox1008Cell017Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell017Node03 TraceData.positiveChordBox1008Cell017Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell017Node04 TraceData.positiveChordBox1008Cell017Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell017Node05 TraceData.positiveChordBox1008Cell017Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell017Node06 TraceData.positiveChordBox1008Cell017Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell017Node07 TraceData.positiveChordBox1008Cell017Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell017Node08 TraceData.positiveChordBox1008Cell017Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell017Node09 TraceData.positiveChordBox1008Cell017Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell017Node10 TraceData.positiveChordBox1008Cell017Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell017Node11 TraceData.positiveChordBox1008Cell017Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell017Node12 TraceData.positiveChordBox1008Cell017Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell017Node13 TraceData.positiveChordBox1008Cell017Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell017Node14 TraceData.positiveChordBox1008Cell017Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell017Node15 TraceData.positiveChordBox1008Cell017Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell017Node16 TraceData.positiveChordBox1008Cell017Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell017Node17 TraceData.positiveChordBox1008Cell017Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell017Node18 TraceData.positiveChordBox1008Cell017Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell017Node19 TraceData.positiveChordBox1008Cell017Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell017Node20 TraceData.positiveChordBox1008Cell017Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell017Node21 TraceData.positiveChordBox1008Cell017Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell017Node22 TraceData.positiveChordBox1008Cell017Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell017Node23 TraceData.positiveChordBox1008Cell017Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell017Node24 TraceData.positiveChordBox1008Cell017Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell017Node25 TraceData.positiveChordBox1008Cell017Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell017Node26 TraceData.positiveChordBox1008Cell017Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell017Node27 TraceData.positiveChordBox1008Cell017Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell017Node28 TraceData.positiveChordBox1008Cell017Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell017Node29 TraceData.positiveChordBox1008Cell017Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell017Node30 TraceData.positiveChordBox1008Cell017Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell017.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell017Node31 TraceData.positiveChordBox1008Cell017Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell018 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell018.interpret
theorem positiveChordBox1008Cell018_valid : positiveChordBox1008Cell018.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-29/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.disk TraceData.positiveChordBox1008Cell018.diskFunction TraceData.positiveChordBox1008Cell018Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell018Node00 TraceData.positiveChordBox1008Cell018Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell018Node01 TraceData.positiveChordBox1008Cell018Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell018Node02 TraceData.positiveChordBox1008Cell018Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell018Node03 TraceData.positiveChordBox1008Cell018Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell018Node04 TraceData.positiveChordBox1008Cell018Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell018Node05 TraceData.positiveChordBox1008Cell018Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell018Node06 TraceData.positiveChordBox1008Cell018Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell018Node07 TraceData.positiveChordBox1008Cell018Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell018Node08 TraceData.positiveChordBox1008Cell018Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell018Node09 TraceData.positiveChordBox1008Cell018Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell018Node10 TraceData.positiveChordBox1008Cell018Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell018Node11 TraceData.positiveChordBox1008Cell018Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell018Node12 TraceData.positiveChordBox1008Cell018Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell018Node13 TraceData.positiveChordBox1008Cell018Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell018Node14 TraceData.positiveChordBox1008Cell018Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell018Node15 TraceData.positiveChordBox1008Cell018Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell018Node16 TraceData.positiveChordBox1008Cell018Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell018Node17 TraceData.positiveChordBox1008Cell018Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell018Node18 TraceData.positiveChordBox1008Cell018Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell018Node19 TraceData.positiveChordBox1008Cell018Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell018Node20 TraceData.positiveChordBox1008Cell018Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell018Node21 TraceData.positiveChordBox1008Cell018Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell018Node22 TraceData.positiveChordBox1008Cell018Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell018Node23 TraceData.positiveChordBox1008Cell018Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell018Node24 TraceData.positiveChordBox1008Cell018Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell018Node25 TraceData.positiveChordBox1008Cell018Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell018Node26 TraceData.positiveChordBox1008Cell018Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell018Node27 TraceData.positiveChordBox1008Cell018Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell018Node28 TraceData.positiveChordBox1008Cell018Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell018Node29 TraceData.positiveChordBox1008Cell018Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell018Node30 TraceData.positiveChordBox1008Cell018Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell018.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell018Node31 TraceData.positiveChordBox1008Cell018Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell019 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell019.interpret
theorem positiveChordBox1008Cell019_valid : positiveChordBox1008Cell019.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-13/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.disk TraceData.positiveChordBox1008Cell019.diskFunction TraceData.positiveChordBox1008Cell019Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell019Node00 TraceData.positiveChordBox1008Cell019Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell019Node01 TraceData.positiveChordBox1008Cell019Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell019Node02 TraceData.positiveChordBox1008Cell019Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell019Node03 TraceData.positiveChordBox1008Cell019Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell019Node04 TraceData.positiveChordBox1008Cell019Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell019Node05 TraceData.positiveChordBox1008Cell019Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell019Node06 TraceData.positiveChordBox1008Cell019Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell019Node07 TraceData.positiveChordBox1008Cell019Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell019Node08 TraceData.positiveChordBox1008Cell019Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell019Node09 TraceData.positiveChordBox1008Cell019Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell019Node10 TraceData.positiveChordBox1008Cell019Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell019Node11 TraceData.positiveChordBox1008Cell019Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell019Node12 TraceData.positiveChordBox1008Cell019Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell019Node13 TraceData.positiveChordBox1008Cell019Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell019Node14 TraceData.positiveChordBox1008Cell019Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell019Node15 TraceData.positiveChordBox1008Cell019Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell019Node16 TraceData.positiveChordBox1008Cell019Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell019Node17 TraceData.positiveChordBox1008Cell019Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell019Node18 TraceData.positiveChordBox1008Cell019Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell019Node19 TraceData.positiveChordBox1008Cell019Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell019Node20 TraceData.positiveChordBox1008Cell019Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell019Node21 TraceData.positiveChordBox1008Cell019Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell019Node22 TraceData.positiveChordBox1008Cell019Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell019Node23 TraceData.positiveChordBox1008Cell019Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell019Node24 TraceData.positiveChordBox1008Cell019Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell019Node25 TraceData.positiveChordBox1008Cell019Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell019Node26 TraceData.positiveChordBox1008Cell019Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell019Node27 TraceData.positiveChordBox1008Cell019Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell019Node28 TraceData.positiveChordBox1008Cell019Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell019Node29 TraceData.positiveChordBox1008Cell019Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell019Node30 TraceData.positiveChordBox1008Cell019Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell019.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell019Node31 TraceData.positiveChordBox1008Cell019Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell020 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell020.interpret
theorem positiveChordBox1008Cell020_valid : positiveChordBox1008Cell020.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-5/8) (1/8) (1/4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.disk TraceData.positiveChordBox1008Cell020.diskFunction TraceData.positiveChordBox1008Cell020Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell020Node00 TraceData.positiveChordBox1008Cell020Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell020Node01 TraceData.positiveChordBox1008Cell020Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell020Node02 TraceData.positiveChordBox1008Cell020Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell020Node03 TraceData.positiveChordBox1008Cell020Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell020Node04 TraceData.positiveChordBox1008Cell020Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell020Node05 TraceData.positiveChordBox1008Cell020Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell020Node06 TraceData.positiveChordBox1008Cell020Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell020Node07 TraceData.positiveChordBox1008Cell020Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell020Node08 TraceData.positiveChordBox1008Cell020Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell020Node09 TraceData.positiveChordBox1008Cell020Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell020Node10 TraceData.positiveChordBox1008Cell020Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell020Node11 TraceData.positiveChordBox1008Cell020Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell020Node12 TraceData.positiveChordBox1008Cell020Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell020Node13 TraceData.positiveChordBox1008Cell020Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell020Node14 TraceData.positiveChordBox1008Cell020Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell020Node15 TraceData.positiveChordBox1008Cell020Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell020Node16 TraceData.positiveChordBox1008Cell020Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell020Node17 TraceData.positiveChordBox1008Cell020Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell020Node18 TraceData.positiveChordBox1008Cell020Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell020Node19 TraceData.positiveChordBox1008Cell020Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell020Node20 TraceData.positiveChordBox1008Cell020Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell020Node21 TraceData.positiveChordBox1008Cell020Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell020Node22 TraceData.positiveChordBox1008Cell020Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell020Node23 TraceData.positiveChordBox1008Cell020Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell020Node24 TraceData.positiveChordBox1008Cell020Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell020Node25 TraceData.positiveChordBox1008Cell020Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell020Node26 TraceData.positiveChordBox1008Cell020Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell020Node27 TraceData.positiveChordBox1008Cell020Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell020Node28 TraceData.positiveChordBox1008Cell020Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell020Node29 TraceData.positiveChordBox1008Cell020Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell020Node30 TraceData.positiveChordBox1008Cell020Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell020.center (1/8) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell020Node31 TraceData.positiveChordBox1008Cell020Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell021 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell021.interpret
theorem positiveChordBox1008Cell021_valid : positiveChordBox1008Cell021.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (-1/4) (1/4) (1/2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.disk TraceData.positiveChordBox1008Cell021.diskFunction TraceData.positiveChordBox1008Cell021Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell021Node00 TraceData.positiveChordBox1008Cell021Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell021Node01 TraceData.positiveChordBox1008Cell021Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell021Node02 TraceData.positiveChordBox1008Cell021Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell021Node03 TraceData.positiveChordBox1008Cell021Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell021Node04 TraceData.positiveChordBox1008Cell021Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell021Node05 TraceData.positiveChordBox1008Cell021Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell021Node06 TraceData.positiveChordBox1008Cell021Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell021Node07 TraceData.positiveChordBox1008Cell021Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell021Node08 TraceData.positiveChordBox1008Cell021Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell021Node09 TraceData.positiveChordBox1008Cell021Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell021Node10 TraceData.positiveChordBox1008Cell021Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell021Node11 TraceData.positiveChordBox1008Cell021Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell021Node12 TraceData.positiveChordBox1008Cell021Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell021Node13 TraceData.positiveChordBox1008Cell021Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell021Node14 TraceData.positiveChordBox1008Cell021Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell021Node15 TraceData.positiveChordBox1008Cell021Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell021Node16 TraceData.positiveChordBox1008Cell021Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell021Node17 TraceData.positiveChordBox1008Cell021Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell021Node18 TraceData.positiveChordBox1008Cell021Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell021Node19 TraceData.positiveChordBox1008Cell021Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell021Node20 TraceData.positiveChordBox1008Cell021Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell021Node21 TraceData.positiveChordBox1008Cell021Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell021Node22 TraceData.positiveChordBox1008Cell021Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell021Node23 TraceData.positiveChordBox1008Cell021Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell021Node24 TraceData.positiveChordBox1008Cell021Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell021Node25 TraceData.positiveChordBox1008Cell021Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell021Node26 TraceData.positiveChordBox1008Cell021Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell021Node27 TraceData.positiveChordBox1008Cell021Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell021Node28 TraceData.positiveChordBox1008Cell021Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell021Node29 TraceData.positiveChordBox1008Cell021Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell021Node30 TraceData.positiveChordBox1008Cell021Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell021.center (1/4) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell021Node31 TraceData.positiveChordBox1008Cell021Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell022 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell022.interpret
theorem positiveChordBox1008Cell022_valid : positiveChordBox1008Cell022.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (1/4) (1/4) (1/2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.disk TraceData.positiveChordBox1008Cell022.diskFunction TraceData.positiveChordBox1008Cell022Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell022Node00 TraceData.positiveChordBox1008Cell022Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell022Node01 TraceData.positiveChordBox1008Cell022Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell022Node02 TraceData.positiveChordBox1008Cell022Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell022Node03 TraceData.positiveChordBox1008Cell022Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell022Node04 TraceData.positiveChordBox1008Cell022Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell022Node05 TraceData.positiveChordBox1008Cell022Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell022Node06 TraceData.positiveChordBox1008Cell022Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell022Node07 TraceData.positiveChordBox1008Cell022Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell022Node08 TraceData.positiveChordBox1008Cell022Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell022Node09 TraceData.positiveChordBox1008Cell022Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell022Node10 TraceData.positiveChordBox1008Cell022Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell022Node11 TraceData.positiveChordBox1008Cell022Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell022Node12 TraceData.positiveChordBox1008Cell022Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell022Node13 TraceData.positiveChordBox1008Cell022Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell022Node14 TraceData.positiveChordBox1008Cell022Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell022Node15 TraceData.positiveChordBox1008Cell022Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell022Node16 TraceData.positiveChordBox1008Cell022Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell022Node17 TraceData.positiveChordBox1008Cell022Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell022Node18 TraceData.positiveChordBox1008Cell022Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell022Node19 TraceData.positiveChordBox1008Cell022Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell022Node20 TraceData.positiveChordBox1008Cell022Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell022Node21 TraceData.positiveChordBox1008Cell022Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell022Node22 TraceData.positiveChordBox1008Cell022Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell022Node23 TraceData.positiveChordBox1008Cell022Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell022Node24 TraceData.positiveChordBox1008Cell022Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell022Node25 TraceData.positiveChordBox1008Cell022Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell022Node26 TraceData.positiveChordBox1008Cell022Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell022Node27 TraceData.positiveChordBox1008Cell022Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell022Node28 TraceData.positiveChordBox1008Cell022Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell022Node29 TraceData.positiveChordBox1008Cell022Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell022Node30 TraceData.positiveChordBox1008Cell022Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell022.center (1/4) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell022Node31 TraceData.positiveChordBox1008Cell022Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell023 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell023.interpret
theorem positiveChordBox1008Cell023_valid : positiveChordBox1008Cell023.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (5/8) (1/8) (1/4) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.disk TraceData.positiveChordBox1008Cell023.diskFunction TraceData.positiveChordBox1008Cell023Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell023Node00 TraceData.positiveChordBox1008Cell023Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell023Node01 TraceData.positiveChordBox1008Cell023Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell023Node02 TraceData.positiveChordBox1008Cell023Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell023Node03 TraceData.positiveChordBox1008Cell023Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell023Node04 TraceData.positiveChordBox1008Cell023Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell023Node05 TraceData.positiveChordBox1008Cell023Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell023Node06 TraceData.positiveChordBox1008Cell023Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell023Node07 TraceData.positiveChordBox1008Cell023Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell023Node08 TraceData.positiveChordBox1008Cell023Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell023Node09 TraceData.positiveChordBox1008Cell023Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell023Node10 TraceData.positiveChordBox1008Cell023Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell023Node11 TraceData.positiveChordBox1008Cell023Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell023Node12 TraceData.positiveChordBox1008Cell023Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell023Node13 TraceData.positiveChordBox1008Cell023Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell023Node14 TraceData.positiveChordBox1008Cell023Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell023Node15 TraceData.positiveChordBox1008Cell023Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell023Node16 TraceData.positiveChordBox1008Cell023Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell023Node17 TraceData.positiveChordBox1008Cell023Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell023Node18 TraceData.positiveChordBox1008Cell023Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell023Node19 TraceData.positiveChordBox1008Cell023Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell023Node20 TraceData.positiveChordBox1008Cell023Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell023Node21 TraceData.positiveChordBox1008Cell023Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell023Node22 TraceData.positiveChordBox1008Cell023Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell023Node23 TraceData.positiveChordBox1008Cell023Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell023Node24 TraceData.positiveChordBox1008Cell023Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell023Node25 TraceData.positiveChordBox1008Cell023Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell023Node26 TraceData.positiveChordBox1008Cell023Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell023Node27 TraceData.positiveChordBox1008Cell023Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell023Node28 TraceData.positiveChordBox1008Cell023Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell023Node29 TraceData.positiveChordBox1008Cell023Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell023Node30 TraceData.positiveChordBox1008Cell023Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell023.center (1/8) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell023Node31 TraceData.positiveChordBox1008Cell023Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell024 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell024.interpret
theorem positiveChordBox1008Cell024_valid : positiveChordBox1008Cell024.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (13/16) (1/16) (1/8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.disk TraceData.positiveChordBox1008Cell024.diskFunction TraceData.positiveChordBox1008Cell024Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell024Node00 TraceData.positiveChordBox1008Cell024Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell024Node01 TraceData.positiveChordBox1008Cell024Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell024Node02 TraceData.positiveChordBox1008Cell024Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell024Node03 TraceData.positiveChordBox1008Cell024Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell024Node04 TraceData.positiveChordBox1008Cell024Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell024Node05 TraceData.positiveChordBox1008Cell024Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell024Node06 TraceData.positiveChordBox1008Cell024Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell024Node07 TraceData.positiveChordBox1008Cell024Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell024Node08 TraceData.positiveChordBox1008Cell024Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell024Node09 TraceData.positiveChordBox1008Cell024Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell024Node10 TraceData.positiveChordBox1008Cell024Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell024Node11 TraceData.positiveChordBox1008Cell024Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell024Node12 TraceData.positiveChordBox1008Cell024Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell024Node13 TraceData.positiveChordBox1008Cell024Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell024Node14 TraceData.positiveChordBox1008Cell024Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell024Node15 TraceData.positiveChordBox1008Cell024Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell024Node16 TraceData.positiveChordBox1008Cell024Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell024Node17 TraceData.positiveChordBox1008Cell024Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell024Node18 TraceData.positiveChordBox1008Cell024Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell024Node19 TraceData.positiveChordBox1008Cell024Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell024Node20 TraceData.positiveChordBox1008Cell024Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell024Node21 TraceData.positiveChordBox1008Cell024Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell024Node22 TraceData.positiveChordBox1008Cell024Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell024Node23 TraceData.positiveChordBox1008Cell024Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell024Node24 TraceData.positiveChordBox1008Cell024Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell024Node25 TraceData.positiveChordBox1008Cell024Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell024Node26 TraceData.positiveChordBox1008Cell024Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell024Node27 TraceData.positiveChordBox1008Cell024Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell024Node28 TraceData.positiveChordBox1008Cell024Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell024Node29 TraceData.positiveChordBox1008Cell024Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell024Node30 TraceData.positiveChordBox1008Cell024Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell024.center (1/16) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell024Node31 TraceData.positiveChordBox1008Cell024Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell025 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell025.interpret
theorem positiveChordBox1008Cell025_valid : positiveChordBox1008Cell025.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (29/32) (1/32) (1/16) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.disk TraceData.positiveChordBox1008Cell025.diskFunction TraceData.positiveChordBox1008Cell025Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell025Node00 TraceData.positiveChordBox1008Cell025Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell025Node01 TraceData.positiveChordBox1008Cell025Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell025Node02 TraceData.positiveChordBox1008Cell025Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell025Node03 TraceData.positiveChordBox1008Cell025Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell025Node04 TraceData.positiveChordBox1008Cell025Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell025Node05 TraceData.positiveChordBox1008Cell025Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell025Node06 TraceData.positiveChordBox1008Cell025Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell025Node07 TraceData.positiveChordBox1008Cell025Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell025Node08 TraceData.positiveChordBox1008Cell025Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell025Node09 TraceData.positiveChordBox1008Cell025Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell025Node10 TraceData.positiveChordBox1008Cell025Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell025Node11 TraceData.positiveChordBox1008Cell025Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell025Node12 TraceData.positiveChordBox1008Cell025Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell025Node13 TraceData.positiveChordBox1008Cell025Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell025Node14 TraceData.positiveChordBox1008Cell025Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell025Node15 TraceData.positiveChordBox1008Cell025Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell025Node16 TraceData.positiveChordBox1008Cell025Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell025Node17 TraceData.positiveChordBox1008Cell025Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell025Node18 TraceData.positiveChordBox1008Cell025Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell025Node19 TraceData.positiveChordBox1008Cell025Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell025Node20 TraceData.positiveChordBox1008Cell025Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell025Node21 TraceData.positiveChordBox1008Cell025Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell025Node22 TraceData.positiveChordBox1008Cell025Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell025Node23 TraceData.positiveChordBox1008Cell025Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell025Node24 TraceData.positiveChordBox1008Cell025Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell025Node25 TraceData.positiveChordBox1008Cell025Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell025Node26 TraceData.positiveChordBox1008Cell025Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell025Node27 TraceData.positiveChordBox1008Cell025Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell025Node28 TraceData.positiveChordBox1008Cell025Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell025Node29 TraceData.positiveChordBox1008Cell025Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell025Node30 TraceData.positiveChordBox1008Cell025Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell025.center (1/32) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell025Node31 TraceData.positiveChordBox1008Cell025Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell026 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell026.interpret
theorem positiveChordBox1008Cell026_valid : positiveChordBox1008Cell026.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (61/64) (1/64) (1/32) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.disk TraceData.positiveChordBox1008Cell026.diskFunction TraceData.positiveChordBox1008Cell026Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell026Node00 TraceData.positiveChordBox1008Cell026Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell026Node01 TraceData.positiveChordBox1008Cell026Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell026Node02 TraceData.positiveChordBox1008Cell026Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell026Node03 TraceData.positiveChordBox1008Cell026Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell026Node04 TraceData.positiveChordBox1008Cell026Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell026Node05 TraceData.positiveChordBox1008Cell026Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell026Node06 TraceData.positiveChordBox1008Cell026Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell026Node07 TraceData.positiveChordBox1008Cell026Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell026Node08 TraceData.positiveChordBox1008Cell026Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell026Node09 TraceData.positiveChordBox1008Cell026Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell026Node10 TraceData.positiveChordBox1008Cell026Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell026Node11 TraceData.positiveChordBox1008Cell026Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell026Node12 TraceData.positiveChordBox1008Cell026Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell026Node13 TraceData.positiveChordBox1008Cell026Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell026Node14 TraceData.positiveChordBox1008Cell026Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell026Node15 TraceData.positiveChordBox1008Cell026Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell026Node16 TraceData.positiveChordBox1008Cell026Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell026Node17 TraceData.positiveChordBox1008Cell026Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell026Node18 TraceData.positiveChordBox1008Cell026Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell026Node19 TraceData.positiveChordBox1008Cell026Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell026Node20 TraceData.positiveChordBox1008Cell026Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell026Node21 TraceData.positiveChordBox1008Cell026Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell026Node22 TraceData.positiveChordBox1008Cell026Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell026Node23 TraceData.positiveChordBox1008Cell026Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell026Node24 TraceData.positiveChordBox1008Cell026Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell026Node25 TraceData.positiveChordBox1008Cell026Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell026Node26 TraceData.positiveChordBox1008Cell026Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell026Node27 TraceData.positiveChordBox1008Cell026Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell026Node28 TraceData.positiveChordBox1008Cell026Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell026Node29 TraceData.positiveChordBox1008Cell026Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell026Node30 TraceData.positiveChordBox1008Cell026Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell026.center (1/64) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell026Node31 TraceData.positiveChordBox1008Cell026Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell027 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell027.interpret
theorem positiveChordBox1008Cell027_valid : positiveChordBox1008Cell027.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (125/128) (1/128) (1/64) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.disk TraceData.positiveChordBox1008Cell027.diskFunction TraceData.positiveChordBox1008Cell027Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell027Node00 TraceData.positiveChordBox1008Cell027Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell027Node01 TraceData.positiveChordBox1008Cell027Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell027Node02 TraceData.positiveChordBox1008Cell027Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell027Node03 TraceData.positiveChordBox1008Cell027Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell027Node04 TraceData.positiveChordBox1008Cell027Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell027Node05 TraceData.positiveChordBox1008Cell027Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell027Node06 TraceData.positiveChordBox1008Cell027Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell027Node07 TraceData.positiveChordBox1008Cell027Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell027Node08 TraceData.positiveChordBox1008Cell027Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell027Node09 TraceData.positiveChordBox1008Cell027Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell027Node10 TraceData.positiveChordBox1008Cell027Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell027Node11 TraceData.positiveChordBox1008Cell027Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell027Node12 TraceData.positiveChordBox1008Cell027Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell027Node13 TraceData.positiveChordBox1008Cell027Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell027Node14 TraceData.positiveChordBox1008Cell027Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell027Node15 TraceData.positiveChordBox1008Cell027Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell027Node16 TraceData.positiveChordBox1008Cell027Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell027Node17 TraceData.positiveChordBox1008Cell027Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell027Node18 TraceData.positiveChordBox1008Cell027Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell027Node19 TraceData.positiveChordBox1008Cell027Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell027Node20 TraceData.positiveChordBox1008Cell027Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell027Node21 TraceData.positiveChordBox1008Cell027Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell027Node22 TraceData.positiveChordBox1008Cell027Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell027Node23 TraceData.positiveChordBox1008Cell027Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell027Node24 TraceData.positiveChordBox1008Cell027Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell027Node25 TraceData.positiveChordBox1008Cell027Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell027Node26 TraceData.positiveChordBox1008Cell027Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell027Node27 TraceData.positiveChordBox1008Cell027Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell027Node28 TraceData.positiveChordBox1008Cell027Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell027Node29 TraceData.positiveChordBox1008Cell027Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell027Node30 TraceData.positiveChordBox1008Cell027Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell027.center (1/128) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell027Node31 TraceData.positiveChordBox1008Cell027Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell028 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell028.interpret
theorem positiveChordBox1008Cell028_valid : positiveChordBox1008Cell028.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (253/256) (1/256) (1/128) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.disk TraceData.positiveChordBox1008Cell028.diskFunction TraceData.positiveChordBox1008Cell028Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell028Node00 TraceData.positiveChordBox1008Cell028Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell028Node01 TraceData.positiveChordBox1008Cell028Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell028Node02 TraceData.positiveChordBox1008Cell028Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell028Node03 TraceData.positiveChordBox1008Cell028Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell028Node04 TraceData.positiveChordBox1008Cell028Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell028Node05 TraceData.positiveChordBox1008Cell028Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell028Node06 TraceData.positiveChordBox1008Cell028Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell028Node07 TraceData.positiveChordBox1008Cell028Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell028Node08 TraceData.positiveChordBox1008Cell028Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell028Node09 TraceData.positiveChordBox1008Cell028Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell028Node10 TraceData.positiveChordBox1008Cell028Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell028Node11 TraceData.positiveChordBox1008Cell028Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell028Node12 TraceData.positiveChordBox1008Cell028Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell028Node13 TraceData.positiveChordBox1008Cell028Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell028Node14 TraceData.positiveChordBox1008Cell028Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell028Node15 TraceData.positiveChordBox1008Cell028Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell028Node16 TraceData.positiveChordBox1008Cell028Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell028Node17 TraceData.positiveChordBox1008Cell028Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell028Node18 TraceData.positiveChordBox1008Cell028Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell028Node19 TraceData.positiveChordBox1008Cell028Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell028Node20 TraceData.positiveChordBox1008Cell028Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell028Node21 TraceData.positiveChordBox1008Cell028Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell028Node22 TraceData.positiveChordBox1008Cell028Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell028Node23 TraceData.positiveChordBox1008Cell028Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell028Node24 TraceData.positiveChordBox1008Cell028Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell028Node25 TraceData.positiveChordBox1008Cell028Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell028Node26 TraceData.positiveChordBox1008Cell028Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell028Node27 TraceData.positiveChordBox1008Cell028Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell028Node28 TraceData.positiveChordBox1008Cell028Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell028Node29 TraceData.positiveChordBox1008Cell028Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell028Node30 TraceData.positiveChordBox1008Cell028Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell028.center (1/256) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell028Node31 TraceData.positiveChordBox1008Cell028Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell029 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell029.interpret
theorem positiveChordBox1008Cell029_valid : positiveChordBox1008Cell029.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (509/512) (1/512) (1/256) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.disk TraceData.positiveChordBox1008Cell029.diskFunction TraceData.positiveChordBox1008Cell029Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell029Node00 TraceData.positiveChordBox1008Cell029Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell029Node01 TraceData.positiveChordBox1008Cell029Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell029Node02 TraceData.positiveChordBox1008Cell029Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell029Node03 TraceData.positiveChordBox1008Cell029Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell029Node04 TraceData.positiveChordBox1008Cell029Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell029Node05 TraceData.positiveChordBox1008Cell029Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell029Node06 TraceData.positiveChordBox1008Cell029Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell029Node07 TraceData.positiveChordBox1008Cell029Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell029Node08 TraceData.positiveChordBox1008Cell029Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell029Node09 TraceData.positiveChordBox1008Cell029Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell029Node10 TraceData.positiveChordBox1008Cell029Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell029Node11 TraceData.positiveChordBox1008Cell029Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell029Node12 TraceData.positiveChordBox1008Cell029Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell029Node13 TraceData.positiveChordBox1008Cell029Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell029Node14 TraceData.positiveChordBox1008Cell029Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell029Node15 TraceData.positiveChordBox1008Cell029Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell029Node16 TraceData.positiveChordBox1008Cell029Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell029Node17 TraceData.positiveChordBox1008Cell029Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell029Node18 TraceData.positiveChordBox1008Cell029Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell029Node19 TraceData.positiveChordBox1008Cell029Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell029Node20 TraceData.positiveChordBox1008Cell029Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell029Node21 TraceData.positiveChordBox1008Cell029Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell029Node22 TraceData.positiveChordBox1008Cell029Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell029Node23 TraceData.positiveChordBox1008Cell029Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell029Node24 TraceData.positiveChordBox1008Cell029Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell029Node25 TraceData.positiveChordBox1008Cell029Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell029Node26 TraceData.positiveChordBox1008Cell029Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell029Node27 TraceData.positiveChordBox1008Cell029Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell029Node28 TraceData.positiveChordBox1008Cell029Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell029Node29 TraceData.positiveChordBox1008Cell029Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell029Node30 TraceData.positiveChordBox1008Cell029Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell029.center (1/512) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell029Node31 TraceData.positiveChordBox1008Cell029Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell030 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell030.interpret
theorem positiveChordBox1008Cell030_valid : positiveChordBox1008Cell030.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (2041/2048) (1/2048) (1/1024) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.disk TraceData.positiveChordBox1008Cell030.diskFunction TraceData.positiveChordBox1008Cell030Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell030Node00 TraceData.positiveChordBox1008Cell030Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell030Node01 TraceData.positiveChordBox1008Cell030Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell030Node02 TraceData.positiveChordBox1008Cell030Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell030Node03 TraceData.positiveChordBox1008Cell030Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell030Node04 TraceData.positiveChordBox1008Cell030Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell030Node05 TraceData.positiveChordBox1008Cell030Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell030Node06 TraceData.positiveChordBox1008Cell030Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell030Node07 TraceData.positiveChordBox1008Cell030Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell030Node08 TraceData.positiveChordBox1008Cell030Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell030Node09 TraceData.positiveChordBox1008Cell030Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell030Node10 TraceData.positiveChordBox1008Cell030Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell030Node11 TraceData.positiveChordBox1008Cell030Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell030Node12 TraceData.positiveChordBox1008Cell030Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell030Node13 TraceData.positiveChordBox1008Cell030Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell030Node14 TraceData.positiveChordBox1008Cell030Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell030Node15 TraceData.positiveChordBox1008Cell030Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell030Node16 TraceData.positiveChordBox1008Cell030Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell030Node17 TraceData.positiveChordBox1008Cell030Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell030Node18 TraceData.positiveChordBox1008Cell030Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell030Node19 TraceData.positiveChordBox1008Cell030Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell030Node20 TraceData.positiveChordBox1008Cell030Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell030Node21 TraceData.positiveChordBox1008Cell030Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell030Node22 TraceData.positiveChordBox1008Cell030Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell030Node23 TraceData.positiveChordBox1008Cell030Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell030Node24 TraceData.positiveChordBox1008Cell030Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell030Node25 TraceData.positiveChordBox1008Cell030Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell030Node26 TraceData.positiveChordBox1008Cell030Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell030Node27 TraceData.positiveChordBox1008Cell030Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell030Node28 TraceData.positiveChordBox1008Cell030Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell030Node29 TraceData.positiveChordBox1008Cell030Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell030Node30 TraceData.positiveChordBox1008Cell030Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell030.center (1/2048) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell030Node31 TraceData.positiveChordBox1008Cell030Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell031 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell031.interpret
theorem positiveChordBox1008Cell031_valid : positiveChordBox1008Cell031.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (2043/2048) (1/2048) (1/1024) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.disk TraceData.positiveChordBox1008Cell031.diskFunction TraceData.positiveChordBox1008Cell031Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell031Node00 TraceData.positiveChordBox1008Cell031Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell031Node01 TraceData.positiveChordBox1008Cell031Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell031Node02 TraceData.positiveChordBox1008Cell031Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell031Node03 TraceData.positiveChordBox1008Cell031Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell031Node04 TraceData.positiveChordBox1008Cell031Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell031Node05 TraceData.positiveChordBox1008Cell031Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell031Node06 TraceData.positiveChordBox1008Cell031Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell031Node07 TraceData.positiveChordBox1008Cell031Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell031Node08 TraceData.positiveChordBox1008Cell031Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell031Node09 TraceData.positiveChordBox1008Cell031Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell031Node10 TraceData.positiveChordBox1008Cell031Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell031Node11 TraceData.positiveChordBox1008Cell031Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell031Node12 TraceData.positiveChordBox1008Cell031Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell031Node13 TraceData.positiveChordBox1008Cell031Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell031Node14 TraceData.positiveChordBox1008Cell031Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell031Node15 TraceData.positiveChordBox1008Cell031Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell031Node16 TraceData.positiveChordBox1008Cell031Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell031Node17 TraceData.positiveChordBox1008Cell031Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell031Node18 TraceData.positiveChordBox1008Cell031Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell031Node19 TraceData.positiveChordBox1008Cell031Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell031Node20 TraceData.positiveChordBox1008Cell031Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell031Node21 TraceData.positiveChordBox1008Cell031Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell031Node22 TraceData.positiveChordBox1008Cell031Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell031Node23 TraceData.positiveChordBox1008Cell031Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell031Node24 TraceData.positiveChordBox1008Cell031Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell031Node25 TraceData.positiveChordBox1008Cell031Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell031Node26 TraceData.positiveChordBox1008Cell031Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell031Node27 TraceData.positiveChordBox1008Cell031Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell031Node28 TraceData.positiveChordBox1008Cell031Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell031Node29 TraceData.positiveChordBox1008Cell031Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell031Node30 TraceData.positiveChordBox1008Cell031Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell031.center (1/2048) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell031Node31 TraceData.positiveChordBox1008Cell031Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell032 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell032.interpret
theorem positiveChordBox1008Cell032_valid : positiveChordBox1008Cell032.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (4089/4096) (1/4096) (1/2048) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.disk TraceData.positiveChordBox1008Cell032.diskFunction TraceData.positiveChordBox1008Cell032Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell032Node00 TraceData.positiveChordBox1008Cell032Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell032Node01 TraceData.positiveChordBox1008Cell032Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell032Node02 TraceData.positiveChordBox1008Cell032Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell032Node03 TraceData.positiveChordBox1008Cell032Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell032Node04 TraceData.positiveChordBox1008Cell032Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell032Node05 TraceData.positiveChordBox1008Cell032Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell032Node06 TraceData.positiveChordBox1008Cell032Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell032Node07 TraceData.positiveChordBox1008Cell032Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell032Node08 TraceData.positiveChordBox1008Cell032Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell032Node09 TraceData.positiveChordBox1008Cell032Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell032Node10 TraceData.positiveChordBox1008Cell032Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell032Node11 TraceData.positiveChordBox1008Cell032Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell032Node12 TraceData.positiveChordBox1008Cell032Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell032Node13 TraceData.positiveChordBox1008Cell032Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell032Node14 TraceData.positiveChordBox1008Cell032Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell032Node15 TraceData.positiveChordBox1008Cell032Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell032Node16 TraceData.positiveChordBox1008Cell032Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell032Node17 TraceData.positiveChordBox1008Cell032Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell032Node18 TraceData.positiveChordBox1008Cell032Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell032Node19 TraceData.positiveChordBox1008Cell032Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell032Node20 TraceData.positiveChordBox1008Cell032Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell032Node21 TraceData.positiveChordBox1008Cell032Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell032Node22 TraceData.positiveChordBox1008Cell032Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell032Node23 TraceData.positiveChordBox1008Cell032Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell032Node24 TraceData.positiveChordBox1008Cell032Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell032Node25 TraceData.positiveChordBox1008Cell032Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell032Node26 TraceData.positiveChordBox1008Cell032Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell032Node27 TraceData.positiveChordBox1008Cell032Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell032Node28 TraceData.positiveChordBox1008Cell032Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell032Node29 TraceData.positiveChordBox1008Cell032Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell032Node30 TraceData.positiveChordBox1008Cell032Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell032.center (1/4096) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell032Node31 TraceData.positiveChordBox1008Cell032Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell033 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell033.interpret
theorem positiveChordBox1008Cell033_valid : positiveChordBox1008Cell033.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (8181/8192) (1/8192) (1/4096) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.disk TraceData.positiveChordBox1008Cell033.diskFunction TraceData.positiveChordBox1008Cell033Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell033Node00 TraceData.positiveChordBox1008Cell033Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell033Node01 TraceData.positiveChordBox1008Cell033Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell033Node02 TraceData.positiveChordBox1008Cell033Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell033Node03 TraceData.positiveChordBox1008Cell033Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell033Node04 TraceData.positiveChordBox1008Cell033Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell033Node05 TraceData.positiveChordBox1008Cell033Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell033Node06 TraceData.positiveChordBox1008Cell033Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell033Node07 TraceData.positiveChordBox1008Cell033Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell033Node08 TraceData.positiveChordBox1008Cell033Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell033Node09 TraceData.positiveChordBox1008Cell033Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell033Node10 TraceData.positiveChordBox1008Cell033Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell033Node11 TraceData.positiveChordBox1008Cell033Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell033Node12 TraceData.positiveChordBox1008Cell033Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell033Node13 TraceData.positiveChordBox1008Cell033Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell033Node14 TraceData.positiveChordBox1008Cell033Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell033Node15 TraceData.positiveChordBox1008Cell033Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell033Node16 TraceData.positiveChordBox1008Cell033Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell033Node17 TraceData.positiveChordBox1008Cell033Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell033Node18 TraceData.positiveChordBox1008Cell033Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell033Node19 TraceData.positiveChordBox1008Cell033Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell033Node20 TraceData.positiveChordBox1008Cell033Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell033Node21 TraceData.positiveChordBox1008Cell033Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell033Node22 TraceData.positiveChordBox1008Cell033Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell033Node23 TraceData.positiveChordBox1008Cell033Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell033Node24 TraceData.positiveChordBox1008Cell033Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell033Node25 TraceData.positiveChordBox1008Cell033Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell033Node26 TraceData.positiveChordBox1008Cell033Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell033Node27 TraceData.positiveChordBox1008Cell033Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell033Node28 TraceData.positiveChordBox1008Cell033Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell033Node29 TraceData.positiveChordBox1008Cell033Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell033Node30 TraceData.positiveChordBox1008Cell033Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell033.center (1/8192) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell033Node31 TraceData.positiveChordBox1008Cell033Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell034 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell034.interpret
theorem positiveChordBox1008Cell034_valid : positiveChordBox1008Cell034.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (16365/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.disk TraceData.positiveChordBox1008Cell034.diskFunction TraceData.positiveChordBox1008Cell034Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell034Node00 TraceData.positiveChordBox1008Cell034Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell034Node01 TraceData.positiveChordBox1008Cell034Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell034Node02 TraceData.positiveChordBox1008Cell034Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell034Node03 TraceData.positiveChordBox1008Cell034Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell034Node04 TraceData.positiveChordBox1008Cell034Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell034Node05 TraceData.positiveChordBox1008Cell034Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell034Node06 TraceData.positiveChordBox1008Cell034Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell034Node07 TraceData.positiveChordBox1008Cell034Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell034Node08 TraceData.positiveChordBox1008Cell034Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell034Node09 TraceData.positiveChordBox1008Cell034Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell034Node10 TraceData.positiveChordBox1008Cell034Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell034Node11 TraceData.positiveChordBox1008Cell034Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell034Node12 TraceData.positiveChordBox1008Cell034Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell034Node13 TraceData.positiveChordBox1008Cell034Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell034Node14 TraceData.positiveChordBox1008Cell034Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell034Node15 TraceData.positiveChordBox1008Cell034Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell034Node16 TraceData.positiveChordBox1008Cell034Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell034Node17 TraceData.positiveChordBox1008Cell034Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell034Node18 TraceData.positiveChordBox1008Cell034Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell034Node19 TraceData.positiveChordBox1008Cell034Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell034Node20 TraceData.positiveChordBox1008Cell034Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell034Node21 TraceData.positiveChordBox1008Cell034Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell034Node22 TraceData.positiveChordBox1008Cell034Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell034Node23 TraceData.positiveChordBox1008Cell034Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell034Node24 TraceData.positiveChordBox1008Cell034Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell034Node25 TraceData.positiveChordBox1008Cell034Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell034Node26 TraceData.positiveChordBox1008Cell034Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell034Node27 TraceData.positiveChordBox1008Cell034Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell034Node28 TraceData.positiveChordBox1008Cell034Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell034Node29 TraceData.positiveChordBox1008Cell034Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell034Node30 TraceData.positiveChordBox1008Cell034Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell034.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell034Node31 TraceData.positiveChordBox1008Cell034Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell035 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell035.interpret
theorem positiveChordBox1008Cell035_valid : positiveChordBox1008Cell035.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (16367/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.disk TraceData.positiveChordBox1008Cell035.diskFunction TraceData.positiveChordBox1008Cell035Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell035Node00 TraceData.positiveChordBox1008Cell035Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell035Node01 TraceData.positiveChordBox1008Cell035Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell035Node02 TraceData.positiveChordBox1008Cell035Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell035Node03 TraceData.positiveChordBox1008Cell035Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell035Node04 TraceData.positiveChordBox1008Cell035Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell035Node05 TraceData.positiveChordBox1008Cell035Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell035Node06 TraceData.positiveChordBox1008Cell035Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell035Node07 TraceData.positiveChordBox1008Cell035Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell035Node08 TraceData.positiveChordBox1008Cell035Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell035Node09 TraceData.positiveChordBox1008Cell035Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell035Node10 TraceData.positiveChordBox1008Cell035Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell035Node11 TraceData.positiveChordBox1008Cell035Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell035Node12 TraceData.positiveChordBox1008Cell035Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell035Node13 TraceData.positiveChordBox1008Cell035Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell035Node14 TraceData.positiveChordBox1008Cell035Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell035Node15 TraceData.positiveChordBox1008Cell035Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell035Node16 TraceData.positiveChordBox1008Cell035Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell035Node17 TraceData.positiveChordBox1008Cell035Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell035Node18 TraceData.positiveChordBox1008Cell035Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell035Node19 TraceData.positiveChordBox1008Cell035Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell035Node20 TraceData.positiveChordBox1008Cell035Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell035Node21 TraceData.positiveChordBox1008Cell035Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell035Node22 TraceData.positiveChordBox1008Cell035Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell035Node23 TraceData.positiveChordBox1008Cell035Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell035Node24 TraceData.positiveChordBox1008Cell035Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell035Node25 TraceData.positiveChordBox1008Cell035Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell035Node26 TraceData.positiveChordBox1008Cell035Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell035Node27 TraceData.positiveChordBox1008Cell035Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell035Node28 TraceData.positiveChordBox1008Cell035Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell035Node29 TraceData.positiveChordBox1008Cell035Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell035Node30 TraceData.positiveChordBox1008Cell035Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell035.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell035Node31 TraceData.positiveChordBox1008Cell035Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell036 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell036.interpret
theorem positiveChordBox1008Cell036_valid : positiveChordBox1008Cell036.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (16369/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.disk TraceData.positiveChordBox1008Cell036.diskFunction TraceData.positiveChordBox1008Cell036Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell036Node00 TraceData.positiveChordBox1008Cell036Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell036Node01 TraceData.positiveChordBox1008Cell036Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell036Node02 TraceData.positiveChordBox1008Cell036Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell036Node03 TraceData.positiveChordBox1008Cell036Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell036Node04 TraceData.positiveChordBox1008Cell036Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell036Node05 TraceData.positiveChordBox1008Cell036Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell036Node06 TraceData.positiveChordBox1008Cell036Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell036Node07 TraceData.positiveChordBox1008Cell036Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell036Node08 TraceData.positiveChordBox1008Cell036Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell036Node09 TraceData.positiveChordBox1008Cell036Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell036Node10 TraceData.positiveChordBox1008Cell036Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell036Node11 TraceData.positiveChordBox1008Cell036Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell036Node12 TraceData.positiveChordBox1008Cell036Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell036Node13 TraceData.positiveChordBox1008Cell036Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell036Node14 TraceData.positiveChordBox1008Cell036Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell036Node15 TraceData.positiveChordBox1008Cell036Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell036Node16 TraceData.positiveChordBox1008Cell036Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell036Node17 TraceData.positiveChordBox1008Cell036Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell036Node18 TraceData.positiveChordBox1008Cell036Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell036Node19 TraceData.positiveChordBox1008Cell036Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell036Node20 TraceData.positiveChordBox1008Cell036Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell036Node21 TraceData.positiveChordBox1008Cell036Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell036Node22 TraceData.positiveChordBox1008Cell036Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell036Node23 TraceData.positiveChordBox1008Cell036Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell036Node24 TraceData.positiveChordBox1008Cell036Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell036Node25 TraceData.positiveChordBox1008Cell036Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell036Node26 TraceData.positiveChordBox1008Cell036Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell036Node27 TraceData.positiveChordBox1008Cell036Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell036Node28 TraceData.positiveChordBox1008Cell036Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell036Node29 TraceData.positiveChordBox1008Cell036Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell036Node30 TraceData.positiveChordBox1008Cell036Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell036.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell036Node31 TraceData.positiveChordBox1008Cell036Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell037 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell037.interpret
theorem positiveChordBox1008Cell037_valid : positiveChordBox1008Cell037.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (16371/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.disk TraceData.positiveChordBox1008Cell037.diskFunction TraceData.positiveChordBox1008Cell037Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell037Node00 TraceData.positiveChordBox1008Cell037Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell037Node01 TraceData.positiveChordBox1008Cell037Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell037Node02 TraceData.positiveChordBox1008Cell037Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell037Node03 TraceData.positiveChordBox1008Cell037Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell037Node04 TraceData.positiveChordBox1008Cell037Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell037Node05 TraceData.positiveChordBox1008Cell037Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell037Node06 TraceData.positiveChordBox1008Cell037Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell037Node07 TraceData.positiveChordBox1008Cell037Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell037Node08 TraceData.positiveChordBox1008Cell037Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell037Node09 TraceData.positiveChordBox1008Cell037Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell037Node10 TraceData.positiveChordBox1008Cell037Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell037Node11 TraceData.positiveChordBox1008Cell037Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell037Node12 TraceData.positiveChordBox1008Cell037Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell037Node13 TraceData.positiveChordBox1008Cell037Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell037Node14 TraceData.positiveChordBox1008Cell037Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell037Node15 TraceData.positiveChordBox1008Cell037Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell037Node16 TraceData.positiveChordBox1008Cell037Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell037Node17 TraceData.positiveChordBox1008Cell037Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell037Node18 TraceData.positiveChordBox1008Cell037Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell037Node19 TraceData.positiveChordBox1008Cell037Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell037Node20 TraceData.positiveChordBox1008Cell037Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell037Node21 TraceData.positiveChordBox1008Cell037Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell037Node22 TraceData.positiveChordBox1008Cell037Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell037Node23 TraceData.positiveChordBox1008Cell037Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell037Node24 TraceData.positiveChordBox1008Cell037Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell037Node25 TraceData.positiveChordBox1008Cell037Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell037Node26 TraceData.positiveChordBox1008Cell037Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell037Node27 TraceData.positiveChordBox1008Cell037Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell037Node28 TraceData.positiveChordBox1008Cell037Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell037Node29 TraceData.positiveChordBox1008Cell037Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell037Node30 TraceData.positiveChordBox1008Cell037Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell037.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell037Node31 TraceData.positiveChordBox1008Cell037Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell038 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell038.interpret
theorem positiveChordBox1008Cell038_valid : positiveChordBox1008Cell038.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (16373/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.disk TraceData.positiveChordBox1008Cell038.diskFunction TraceData.positiveChordBox1008Cell038Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell038Node00 TraceData.positiveChordBox1008Cell038Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell038Node01 TraceData.positiveChordBox1008Cell038Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell038Node02 TraceData.positiveChordBox1008Cell038Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell038Node03 TraceData.positiveChordBox1008Cell038Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell038Node04 TraceData.positiveChordBox1008Cell038Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell038Node05 TraceData.positiveChordBox1008Cell038Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell038Node06 TraceData.positiveChordBox1008Cell038Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell038Node07 TraceData.positiveChordBox1008Cell038Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell038Node08 TraceData.positiveChordBox1008Cell038Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell038Node09 TraceData.positiveChordBox1008Cell038Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell038Node10 TraceData.positiveChordBox1008Cell038Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell038Node11 TraceData.positiveChordBox1008Cell038Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell038Node12 TraceData.positiveChordBox1008Cell038Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell038Node13 TraceData.positiveChordBox1008Cell038Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell038Node14 TraceData.positiveChordBox1008Cell038Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell038Node15 TraceData.positiveChordBox1008Cell038Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell038Node16 TraceData.positiveChordBox1008Cell038Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell038Node17 TraceData.positiveChordBox1008Cell038Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell038Node18 TraceData.positiveChordBox1008Cell038Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell038Node19 TraceData.positiveChordBox1008Cell038Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell038Node20 TraceData.positiveChordBox1008Cell038Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell038Node21 TraceData.positiveChordBox1008Cell038Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell038Node22 TraceData.positiveChordBox1008Cell038Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell038Node23 TraceData.positiveChordBox1008Cell038Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell038Node24 TraceData.positiveChordBox1008Cell038Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell038Node25 TraceData.positiveChordBox1008Cell038Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell038Node26 TraceData.positiveChordBox1008Cell038Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell038Node27 TraceData.positiveChordBox1008Cell038Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell038Node28 TraceData.positiveChordBox1008Cell038Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell038Node29 TraceData.positiveChordBox1008Cell038Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell038Node30 TraceData.positiveChordBox1008Cell038Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell038.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell038Node31 TraceData.positiveChordBox1008Cell038Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell039 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell039.interpret
theorem positiveChordBox1008Cell039_valid : positiveChordBox1008Cell039.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (16375/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.disk TraceData.positiveChordBox1008Cell039.diskFunction TraceData.positiveChordBox1008Cell039Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell039Node00 TraceData.positiveChordBox1008Cell039Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell039Node01 TraceData.positiveChordBox1008Cell039Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell039Node02 TraceData.positiveChordBox1008Cell039Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell039Node03 TraceData.positiveChordBox1008Cell039Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell039Node04 TraceData.positiveChordBox1008Cell039Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell039Node05 TraceData.positiveChordBox1008Cell039Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell039Node06 TraceData.positiveChordBox1008Cell039Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell039Node07 TraceData.positiveChordBox1008Cell039Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell039Node08 TraceData.positiveChordBox1008Cell039Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell039Node09 TraceData.positiveChordBox1008Cell039Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell039Node10 TraceData.positiveChordBox1008Cell039Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell039Node11 TraceData.positiveChordBox1008Cell039Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell039Node12 TraceData.positiveChordBox1008Cell039Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell039Node13 TraceData.positiveChordBox1008Cell039Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell039Node14 TraceData.positiveChordBox1008Cell039Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell039Node15 TraceData.positiveChordBox1008Cell039Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell039Node16 TraceData.positiveChordBox1008Cell039Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell039Node17 TraceData.positiveChordBox1008Cell039Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell039Node18 TraceData.positiveChordBox1008Cell039Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell039Node19 TraceData.positiveChordBox1008Cell039Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell039Node20 TraceData.positiveChordBox1008Cell039Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell039Node21 TraceData.positiveChordBox1008Cell039Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell039Node22 TraceData.positiveChordBox1008Cell039Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell039Node23 TraceData.positiveChordBox1008Cell039Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell039Node24 TraceData.positiveChordBox1008Cell039Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell039Node25 TraceData.positiveChordBox1008Cell039Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell039Node26 TraceData.positiveChordBox1008Cell039Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell039Node27 TraceData.positiveChordBox1008Cell039Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell039Node28 TraceData.positiveChordBox1008Cell039Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell039Node29 TraceData.positiveChordBox1008Cell039Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell039Node30 TraceData.positiveChordBox1008Cell039Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell039.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell039Node31 TraceData.positiveChordBox1008Cell039Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell040 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell040.interpret
theorem positiveChordBox1008Cell040_valid : positiveChordBox1008Cell040.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (16377/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.disk TraceData.positiveChordBox1008Cell040.diskFunction TraceData.positiveChordBox1008Cell040Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell040Node00 TraceData.positiveChordBox1008Cell040Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell040Node01 TraceData.positiveChordBox1008Cell040Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell040Node02 TraceData.positiveChordBox1008Cell040Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell040Node03 TraceData.positiveChordBox1008Cell040Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell040Node04 TraceData.positiveChordBox1008Cell040Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell040Node05 TraceData.positiveChordBox1008Cell040Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell040Node06 TraceData.positiveChordBox1008Cell040Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell040Node07 TraceData.positiveChordBox1008Cell040Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell040Node08 TraceData.positiveChordBox1008Cell040Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell040Node09 TraceData.positiveChordBox1008Cell040Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell040Node10 TraceData.positiveChordBox1008Cell040Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell040Node11 TraceData.positiveChordBox1008Cell040Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell040Node12 TraceData.positiveChordBox1008Cell040Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell040Node13 TraceData.positiveChordBox1008Cell040Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell040Node14 TraceData.positiveChordBox1008Cell040Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell040Node15 TraceData.positiveChordBox1008Cell040Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell040Node16 TraceData.positiveChordBox1008Cell040Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell040Node17 TraceData.positiveChordBox1008Cell040Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell040Node18 TraceData.positiveChordBox1008Cell040Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell040Node19 TraceData.positiveChordBox1008Cell040Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell040Node20 TraceData.positiveChordBox1008Cell040Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell040Node21 TraceData.positiveChordBox1008Cell040Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell040Node22 TraceData.positiveChordBox1008Cell040Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell040Node23 TraceData.positiveChordBox1008Cell040Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell040Node24 TraceData.positiveChordBox1008Cell040Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell040Node25 TraceData.positiveChordBox1008Cell040Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell040Node26 TraceData.positiveChordBox1008Cell040Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell040Node27 TraceData.positiveChordBox1008Cell040Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell040Node28 TraceData.positiveChordBox1008Cell040Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell040Node29 TraceData.positiveChordBox1008Cell040Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell040Node30 TraceData.positiveChordBox1008Cell040Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell040.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell040Node31 TraceData.positiveChordBox1008Cell040Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell041 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell041.interpret
theorem positiveChordBox1008Cell041_valid : positiveChordBox1008Cell041.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (16379/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.disk TraceData.positiveChordBox1008Cell041.diskFunction TraceData.positiveChordBox1008Cell041Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell041Node00 TraceData.positiveChordBox1008Cell041Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell041Node01 TraceData.positiveChordBox1008Cell041Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell041Node02 TraceData.positiveChordBox1008Cell041Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell041Node03 TraceData.positiveChordBox1008Cell041Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell041Node04 TraceData.positiveChordBox1008Cell041Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell041Node05 TraceData.positiveChordBox1008Cell041Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell041Node06 TraceData.positiveChordBox1008Cell041Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell041Node07 TraceData.positiveChordBox1008Cell041Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell041Node08 TraceData.positiveChordBox1008Cell041Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell041Node09 TraceData.positiveChordBox1008Cell041Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell041Node10 TraceData.positiveChordBox1008Cell041Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell041Node11 TraceData.positiveChordBox1008Cell041Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell041Node12 TraceData.positiveChordBox1008Cell041Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell041Node13 TraceData.positiveChordBox1008Cell041Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell041Node14 TraceData.positiveChordBox1008Cell041Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell041Node15 TraceData.positiveChordBox1008Cell041Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell041Node16 TraceData.positiveChordBox1008Cell041Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell041Node17 TraceData.positiveChordBox1008Cell041Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell041Node18 TraceData.positiveChordBox1008Cell041Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell041Node19 TraceData.positiveChordBox1008Cell041Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell041Node20 TraceData.positiveChordBox1008Cell041Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell041Node21 TraceData.positiveChordBox1008Cell041Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell041Node22 TraceData.positiveChordBox1008Cell041Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell041Node23 TraceData.positiveChordBox1008Cell041Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell041Node24 TraceData.positiveChordBox1008Cell041Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell041Node25 TraceData.positiveChordBox1008Cell041Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell041Node26 TraceData.positiveChordBox1008Cell041Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell041Node27 TraceData.positiveChordBox1008Cell041Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell041Node28 TraceData.positiveChordBox1008Cell041Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell041Node29 TraceData.positiveChordBox1008Cell041Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell041Node30 TraceData.positiveChordBox1008Cell041Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell041.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell041Node31 TraceData.positiveChordBox1008Cell041Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell042 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell042.interpret
theorem positiveChordBox1008Cell042_valid : positiveChordBox1008Cell042.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (16381/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.disk TraceData.positiveChordBox1008Cell042.diskFunction TraceData.positiveChordBox1008Cell042Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell042Node00 TraceData.positiveChordBox1008Cell042Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell042Node01 TraceData.positiveChordBox1008Cell042Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell042Node02 TraceData.positiveChordBox1008Cell042Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell042Node03 TraceData.positiveChordBox1008Cell042Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell042Node04 TraceData.positiveChordBox1008Cell042Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell042Node05 TraceData.positiveChordBox1008Cell042Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell042Node06 TraceData.positiveChordBox1008Cell042Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell042Node07 TraceData.positiveChordBox1008Cell042Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell042Node08 TraceData.positiveChordBox1008Cell042Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell042Node09 TraceData.positiveChordBox1008Cell042Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell042Node10 TraceData.positiveChordBox1008Cell042Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell042Node11 TraceData.positiveChordBox1008Cell042Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell042Node12 TraceData.positiveChordBox1008Cell042Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell042Node13 TraceData.positiveChordBox1008Cell042Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell042Node14 TraceData.positiveChordBox1008Cell042Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell042Node15 TraceData.positiveChordBox1008Cell042Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell042Node16 TraceData.positiveChordBox1008Cell042Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell042Node17 TraceData.positiveChordBox1008Cell042Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell042Node18 TraceData.positiveChordBox1008Cell042Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell042Node19 TraceData.positiveChordBox1008Cell042Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell042Node20 TraceData.positiveChordBox1008Cell042Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell042Node21 TraceData.positiveChordBox1008Cell042Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell042Node22 TraceData.positiveChordBox1008Cell042Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell042Node23 TraceData.positiveChordBox1008Cell042Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell042Node24 TraceData.positiveChordBox1008Cell042Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell042Node25 TraceData.positiveChordBox1008Cell042Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell042Node26 TraceData.positiveChordBox1008Cell042Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell042Node27 TraceData.positiveChordBox1008Cell042Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell042Node28 TraceData.positiveChordBox1008Cell042Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell042Node29 TraceData.positiveChordBox1008Cell042Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell042Node30 TraceData.positiveChordBox1008Cell042Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell042.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell042Node31 TraceData.positiveChordBox1008Cell042Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
noncomputable def positiveChordBox1008Cell043 : JacobiChordRangeCell 32 := TraceData.positiveChordBox1008Cell043.interpret
theorem positiveChordBox1008Cell043_valid : positiveChordBox1008Cell043.Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (16383/16384) (1/16384) (1/8192) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · exact TraceData.DyadicJacobiChordTrace.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.disk TraceData.positiveChordBox1008Cell043.diskFunction TraceData.positiveChordBox1008Cell043Disk_valid
  · intro j
    fin_cases j
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 0) (TraceData.jacobiQuadratureWeights 0) TraceData.positiveChordBox1008Cell043Node00 TraceData.positiveChordBox1008Cell043Node00_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 1) (TraceData.jacobiQuadratureWeights 1) TraceData.positiveChordBox1008Cell043Node01 TraceData.positiveChordBox1008Cell043Node01_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 2) (TraceData.jacobiQuadratureWeights 2) TraceData.positiveChordBox1008Cell043Node02 TraceData.positiveChordBox1008Cell043Node02_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 3) (TraceData.jacobiQuadratureWeights 3) TraceData.positiveChordBox1008Cell043Node03 TraceData.positiveChordBox1008Cell043Node03_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 4) (TraceData.jacobiQuadratureWeights 4) TraceData.positiveChordBox1008Cell043Node04 TraceData.positiveChordBox1008Cell043Node04_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 5) (TraceData.jacobiQuadratureWeights 5) TraceData.positiveChordBox1008Cell043Node05 TraceData.positiveChordBox1008Cell043Node05_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 6) (TraceData.jacobiQuadratureWeights 6) TraceData.positiveChordBox1008Cell043Node06 TraceData.positiveChordBox1008Cell043Node06_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 7) (TraceData.jacobiQuadratureWeights 7) TraceData.positiveChordBox1008Cell043Node07 TraceData.positiveChordBox1008Cell043Node07_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 8) (TraceData.jacobiQuadratureWeights 8) TraceData.positiveChordBox1008Cell043Node08 TraceData.positiveChordBox1008Cell043Node08_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 9) (TraceData.jacobiQuadratureWeights 9) TraceData.positiveChordBox1008Cell043Node09 TraceData.positiveChordBox1008Cell043Node09_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 10) (TraceData.jacobiQuadratureWeights 10) TraceData.positiveChordBox1008Cell043Node10 TraceData.positiveChordBox1008Cell043Node10_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 11) (TraceData.jacobiQuadratureWeights 11) TraceData.positiveChordBox1008Cell043Node11 TraceData.positiveChordBox1008Cell043Node11_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 12) (TraceData.jacobiQuadratureWeights 12) TraceData.positiveChordBox1008Cell043Node12 TraceData.positiveChordBox1008Cell043Node12_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 13) (TraceData.jacobiQuadratureWeights 13) TraceData.positiveChordBox1008Cell043Node13 TraceData.positiveChordBox1008Cell043Node13_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 14) (TraceData.jacobiQuadratureWeights 14) TraceData.positiveChordBox1008Cell043Node14 TraceData.positiveChordBox1008Cell043Node14_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 15) (TraceData.jacobiQuadratureWeights 15) TraceData.positiveChordBox1008Cell043Node15 TraceData.positiveChordBox1008Cell043Node15_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 16) (TraceData.jacobiQuadratureWeights 16) TraceData.positiveChordBox1008Cell043Node16 TraceData.positiveChordBox1008Cell043Node16_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 17) (TraceData.jacobiQuadratureWeights 17) TraceData.positiveChordBox1008Cell043Node17 TraceData.positiveChordBox1008Cell043Node17_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 18) (TraceData.jacobiQuadratureWeights 18) TraceData.positiveChordBox1008Cell043Node18 TraceData.positiveChordBox1008Cell043Node18_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 19) (TraceData.jacobiQuadratureWeights 19) TraceData.positiveChordBox1008Cell043Node19 TraceData.positiveChordBox1008Cell043Node19_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 20) (TraceData.jacobiQuadratureWeights 20) TraceData.positiveChordBox1008Cell043Node20 TraceData.positiveChordBox1008Cell043Node20_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 21) (TraceData.jacobiQuadratureWeights 21) TraceData.positiveChordBox1008Cell043Node21 TraceData.positiveChordBox1008Cell043Node21_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 22) (TraceData.jacobiQuadratureWeights 22) TraceData.positiveChordBox1008Cell043Node22 TraceData.positiveChordBox1008Cell043Node22_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 23) (TraceData.jacobiQuadratureWeights 23) TraceData.positiveChordBox1008Cell043Node23 TraceData.positiveChordBox1008Cell043Node23_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 24) (TraceData.jacobiQuadratureWeights 24) TraceData.positiveChordBox1008Cell043Node24 TraceData.positiveChordBox1008Cell043Node24_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 25) (TraceData.jacobiQuadratureWeights 25) TraceData.positiveChordBox1008Cell043Node25 TraceData.positiveChordBox1008Cell043Node25_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 26) (TraceData.jacobiQuadratureWeights 26) TraceData.positiveChordBox1008Cell043Node26 TraceData.positiveChordBox1008Cell043Node26_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 27) (TraceData.jacobiQuadratureWeights 27) TraceData.positiveChordBox1008Cell043Node27 TraceData.positiveChordBox1008Cell043Node27_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 28) (TraceData.jacobiQuadratureWeights 28) TraceData.positiveChordBox1008Cell043Node28 TraceData.positiveChordBox1008Cell043Node28_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 29) (TraceData.jacobiQuadratureWeights 29) TraceData.positiveChordBox1008Cell043Node29 TraceData.positiveChordBox1008Cell043Node29_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 30) (TraceData.jacobiQuadratureWeights 30) TraceData.positiveChordBox1008Cell043Node30 TraceData.positiveChordBox1008Cell043Node30_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
    · have hn := TraceData.JacobiChordRangeNode.valid_of_valid ⟨64,12,6⟩ 18446744074 9223372037 TraceData.positiveChordBox1008Parameters TraceData.positiveChordBox1008Cell043.center (1/16384) (TraceData.jacobiQuadratureNodes 31) (TraceData.jacobiQuadratureWeights 31) TraceData.positiveChordBox1008Cell043Node31 TraceData.positiveChordBox1008Cell043Node31_valid
      rw [TraceData.jacobiQuadratureNodes_eq, TraceData.jacobiQuadratureWeights_eq] at hn
      convert hn using 1 <;> rfl
def positiveChordBox1008Boundary : ℕ → ℚ := fun i => match i with
  | 0 => (-1/1)
  | 1 => (-8191/8192)
  | 2 => (-4095/4096)
  | 3 => (-8189/8192)
  | 4 => (-2047/2048)
  | 5 => (-8187/8192)
  | 6 => (-4093/4096)
  | 7 => (-8185/8192)
  | 8 => (-1023/1024)
  | 9 => (-8183/8192)
  | 10 => (-4091/4096)
  | 11 => (-2045/2048)
  | 12 => (-511/512)
  | 13 => (-1021/1024)
  | 14 => (-255/256)
  | 15 => (-127/128)
  | 16 => (-63/64)
  | 17 => (-31/32)
  | 18 => (-15/16)
  | 19 => (-7/8)
  | 20 => (-3/4)
  | 21 => (-1/2)
  | 22 => (0/1)
  | 23 => (1/2)
  | 24 => (3/4)
  | 25 => (7/8)
  | 26 => (15/16)
  | 27 => (31/32)
  | 28 => (63/64)
  | 29 => (127/128)
  | 30 => (255/256)
  | 31 => (1021/1024)
  | 32 => (511/512)
  | 33 => (2045/2048)
  | 34 => (4091/4096)
  | 35 => (8183/8192)
  | 36 => (1023/1024)
  | 37 => (8185/8192)
  | 38 => (4093/4096)
  | 39 => (8187/8192)
  | 40 => (2047/2048)
  | 41 => (8189/8192)
  | 42 => (4095/4096)
  | 43 => (8191/8192)
  | _ => (1/1)
def positiveChordBox1008Radius : Fin 44 → ℚ := ![(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/4096),(1/2048),(1/1024),(1/1024),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(1/4),(1/2),(1/2),(1/4),(1/8),(1/16),(1/32),(1/64),(1/128),(1/256),(1/1024),(1/1024),(1/2048),(1/4096),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192),(1/8192)]
noncomputable def positiveChordBox1008Cells : Fin 44 → JacobiChordRangeCell 32 := ![positiveChordBox1008Cell000,positiveChordBox1008Cell001,positiveChordBox1008Cell002,positiveChordBox1008Cell003,positiveChordBox1008Cell004,positiveChordBox1008Cell005,positiveChordBox1008Cell006,positiveChordBox1008Cell007,positiveChordBox1008Cell008,positiveChordBox1008Cell009,positiveChordBox1008Cell010,positiveChordBox1008Cell011,positiveChordBox1008Cell012,positiveChordBox1008Cell013,positiveChordBox1008Cell014,positiveChordBox1008Cell015,positiveChordBox1008Cell016,positiveChordBox1008Cell017,positiveChordBox1008Cell018,positiveChordBox1008Cell019,positiveChordBox1008Cell020,positiveChordBox1008Cell021,positiveChordBox1008Cell022,positiveChordBox1008Cell023,positiveChordBox1008Cell024,positiveChordBox1008Cell025,positiveChordBox1008Cell026,positiveChordBox1008Cell027,positiveChordBox1008Cell028,positiveChordBox1008Cell029,positiveChordBox1008Cell030,positiveChordBox1008Cell031,positiveChordBox1008Cell032,positiveChordBox1008Cell033,positiveChordBox1008Cell034,positiveChordBox1008Cell035,positiveChordBox1008Cell036,positiveChordBox1008Cell037,positiveChordBox1008Cell038,positiveChordBox1008Cell039,positiveChordBox1008Cell040,positiveChordBox1008Cell041,positiveChordBox1008Cell042,positiveChordBox1008Cell043]
theorem positiveChordBox1008Cells_valid : ∀ i : Fin 44, (positiveChordBox1008Cells i).Valid ⟨64,12,6⟩ 18446744074 9223372037 rationalQuadrature32 32 positiveChordBox1008Parameters (jacobiCellCenter positiveChordBox1008Boundary i) (jacobiCellRadius positiveChordBox1008Boundary i) (positiveChordBox1008Radius i) := by
  intro i
  fin_cases i
  · convert positiveChordBox1008Cell000_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell001_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell002_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell003_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell004_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell005_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell006_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell007_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell008_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell009_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell010_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell011_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell012_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell013_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell014_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell015_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell016_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell017_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell018_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell019_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell020_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell021_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell022_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell023_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell024_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell025_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell026_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell027_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell028_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell029_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell030_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell031_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell032_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell033_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell034_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell035_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell036_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell037_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell038_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell039_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell040_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell041_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell042_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
  · convert positiveChordBox1008Cell043_valid using 1 <;> first | rfl | norm_num [jacobiCellCenter, jacobiCellRadius, positiveChordBox1008Boundary]
theorem positiveChordBox1008_lower : (3/10000 : ℚ) < (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).radius := by decide +kernel
theorem positiveChordBox1008_rectangle_positive {t a : ℝ}
    (htl : (((1/5) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((9/40) : ℚ) : ℝ))
    (hal : (((1/2) : ℚ) : ℝ) ≤ a) (hau : a ≤ (((184621687045551444769/368934881474191032320) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < thetaHorizontalPeriod t a := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1008Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1008Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1008Parameters positiveChordBox1008Parameters_valid hbt hba
    positiveChordBox1008Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1008Radius positiveChordBox1008Cells positiveChordBox1008Cells_valid
  have hl := (ComplexBall.re_bounds hb).1
  rw [← horizontalPeriod_eq_jacobiChordKernel ht0 ht85 ha0 ha1] at hl
  have hc : (((3/10000 : ℚ) : ℝ)) <
      (((combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).radius : ℚ) : ℝ) :=
    (Rat.cast_lt (K := ℝ)).mpr positiveChordBox1008_lower
  rw [show (((3/10000 : ℚ) : ℝ)) = (3/10000 : ℝ) by norm_num] at hc
  exact hc.trans_le hl

theorem positiveChordBox1008_vertical_enclosure {t : ℝ}
    (htl : (((1/5) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((9/40) : ℚ) : ℝ)) :
    verticalA t ∈ Set.Icc (((1/2) : ℚ) : ℝ) (((184621687045551444769/368934881474191032320) : ℚ) : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have hdomain : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper :=
    ⟨ht0, htu.trans_lt ((by norm_num : (((9/40) : ℚ) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  have hq := jacobiSmallNome_upper ⟨64,12,6⟩ (9/40) (17138478717325401/18446744073709551616) TraceData.positiveChordBox1008Nome.interpret
    (TraceData.jacobiSmallNome_valid_of_check ⟨64,12,6⟩ (9/40) TraceData.positiveChordBox1008Nome TraceData.positiveChordBox1008Nome_valid)
    (by decide +kernel)
  have hu := verticalA_small_rectangle_upper ht0 htu (by norm_num) hq
  have he : (1/2 : ℝ)+2*(((9/40) : ℚ) : ℝ)*(((17138478717325401/18446744073709551616) : ℚ) : ℝ) = (((184621687045551444769/368934881474191032320) : ℚ) : ℝ) := by norm_num
  rw [he] at hu
  exact ⟨by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (verticalA_gt_half hdomain).le, hu⟩
theorem positiveChordBox1008_positive {t : ℝ}
    (htl : (((1/5) : ℚ) : ℝ) ≤ t) (htu : t ≤ (((9/40) : ℚ) : ℝ)) :
    (3/10000 : ℝ) < actualPeriodAlong t := by
  have ha := positiveChordBox1008_vertical_enclosure htl htu
  exact positiveChordBox1008_rectangle_positive htl htu ha.1 ha.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positiveChordBox1008_positive
