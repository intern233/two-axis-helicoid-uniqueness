import TwoAxisHelicoid.PdfSharedChord426Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord426Disk5Cell0_0 : chordRectangleTest 4 sharedChord426Params (-7/8) (-3/8) (-1/4) (1/4) 1937=true := by decide +kernel
theorem sharedChord426Disk5 {t a : ℝ} (ps : sharedChord426Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord426Bd (5:Fin 14)) (2*jacobiCellRadius sharedChord426Bd (5:Fin 14)) (sharedChord426M 5) t a := by
  rw [show jacobiCellCenter sharedChord426Bd (5:Fin 14)=(-5/8) by decide +kernel, show 2*jacobiCellRadius sharedChord426Bd (5:Fin 14)=(1/4) by decide +kernel, show sharedChord426M 5=1937 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-5/8):ℚ)-(1/4)=(-7/8) by decide +kernel, show ((-5/8):ℚ)+(1/4)=(-3/8) by decide +kernel, show -((1/4):ℚ)=(-1/4) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord426Disk5Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord426Disk5
