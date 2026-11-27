import TwoAxisHelicoid.PdfSharedChord426Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord426Disk2Cell0_0 : chordRectangleTest 4 sharedChord426Params (-63/64) (-59/64) (-1/32) (1/32) 118139=true := by decide +kernel
theorem sharedChord426Disk2 {t a : ℝ} (ps : sharedChord426Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord426Bd (2:Fin 14)) (2*jacobiCellRadius sharedChord426Bd (2:Fin 14)) (sharedChord426M 2) t a := by
  rw [show jacobiCellCenter sharedChord426Bd (2:Fin 14)=(-61/64) by decide +kernel, show 2*jacobiCellRadius sharedChord426Bd (2:Fin 14)=(1/32) by decide +kernel, show sharedChord426M 2=118139 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-61/64):ℚ)-(1/32)=(-63/64) by decide +kernel, show ((-61/64):ℚ)+(1/32)=(-59/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord426Disk2Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord426Disk2
