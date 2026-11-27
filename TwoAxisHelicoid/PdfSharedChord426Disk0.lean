import TwoAxisHelicoid.PdfSharedChord426Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord426Disk0Cell0_0 : chordRectangleTest 4 sharedChord426Params (-129/128) (-125/128) (-1/64) (1/64) 4493738=true := by decide +kernel
theorem sharedChord426Disk0 {t a : ℝ} (ps : sharedChord426Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord426Bd (0:Fin 14)) (2*jacobiCellRadius sharedChord426Bd (0:Fin 14)) (sharedChord426M 0) t a := by
  rw [show jacobiCellCenter sharedChord426Bd (0:Fin 14)=(-127/128) by decide +kernel, show 2*jacobiCellRadius sharedChord426Bd (0:Fin 14)=(1/64) by decide +kernel, show sharedChord426M 0=4493738 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-127/128):ℚ)-(1/64)=(-129/128) by decide +kernel, show ((-127/128):ℚ)+(1/64)=(-125/128) by decide +kernel, show -((1/64):ℚ)=(-1/64) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord426Disk0Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord426Disk0
