import TwoAxisHelicoid.PdfSharedChord426Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord426Disk1Cell0_0 : chordRectangleTest 4 sharedChord426Params (-127/128) (-123/128) (-1/64) (1/64) 92348=true := by decide +kernel
theorem sharedChord426Disk1 {t a : ℝ} (ps : sharedChord426Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord426Bd (1:Fin 14)) (2*jacobiCellRadius sharedChord426Bd (1:Fin 14)) (sharedChord426M 1) t a := by
  rw [show jacobiCellCenter sharedChord426Bd (1:Fin 14)=(-125/128) by decide +kernel, show 2*jacobiCellRadius sharedChord426Bd (1:Fin 14)=(1/64) by decide +kernel, show sharedChord426M 1=92348 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-125/128):ℚ)-(1/64)=(-127/128) by decide +kernel, show ((-125/128):ℚ)+(1/64)=(-123/128) by decide +kernel, show -((1/64):ℚ)=(-1/64) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord426Disk1Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord426Disk1
