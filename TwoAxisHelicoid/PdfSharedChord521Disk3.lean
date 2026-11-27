import TwoAxisHelicoid.PdfSharedChord521Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord521Disk3Cell0_0 : chordRectangleTest 4 sharedChord521Params (-3/4) (-1/4) (-1/2) 0 310594=true := by decide +kernel
theorem sharedChord521Disk3Cell0_1 : chordRectangleTest 4 sharedChord521Params (-3/4) (-1/4) 0 (1/2) 310594=true := by decide +kernel
theorem sharedChord521Disk3Cell1_0 : chordRectangleTest 4 sharedChord521Params (-1/4) (1/4) (-1/2) 0 310594=true := by decide +kernel
theorem sharedChord521Disk3Cell1_1 : chordRectangleTest 4 sharedChord521Params (-1/4) (1/4) 0 (1/2) 310594=true := by decide +kernel
theorem sharedChord521Disk3 {t a : ℝ} (ps : sharedChord521Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord521Bd (3:Fin 9)) (2*jacobiCellRadius sharedChord521Bd (3:Fin 9)) (sharedChord521M 3) t a := by
  rw [show jacobiCellCenter sharedChord521Bd (3:Fin 9)=(-1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord521Bd (3:Fin 9)=(1/2) by decide +kernel, show sharedChord521M 3=310594 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-1/4):ℚ)-(1/2)=(-3/4) by decide +kernel, show ((-1/4):ℚ)+(1/2)=(1/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord521Disk3Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord521Disk3Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord521Disk3Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord521Disk3Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord521Disk3
