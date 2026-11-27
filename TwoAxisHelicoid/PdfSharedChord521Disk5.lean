import TwoAxisHelicoid.PdfSharedChord521Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord521Disk5Cell0_0 : chordRectangleTest 4 sharedChord521Params (7/16) (11/16) (-1/8) (1/8) 1973=true := by decide +kernel
theorem sharedChord521Disk5 {t a : ℝ} (ps : sharedChord521Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord521Bd (5:Fin 9)) (2*jacobiCellRadius sharedChord521Bd (5:Fin 9)) (sharedChord521M 5) t a := by
  rw [show jacobiCellCenter sharedChord521Bd (5:Fin 9)=(9/16) by decide +kernel, show 2*jacobiCellRadius sharedChord521Bd (5:Fin 9)=(1/8) by decide +kernel, show sharedChord521M 5=1973 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((9/16):ℚ)-(1/8)=(7/16) by decide +kernel, show ((9/16):ℚ)+(1/8)=(11/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord521Disk5Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord521Disk5
