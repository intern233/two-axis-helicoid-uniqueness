import TwoAxisHelicoid.PdfSharedChord521Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord521Disk4Cell0_0 : chordRectangleTest 4 sharedChord521Params (-1/4) 0 (-1/2) (-1/4) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell0_1 : chordRectangleTest 4 sharedChord521Params (-1/4) 0 (-1/4) 0 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell0_2 : chordRectangleTest 4 sharedChord521Params (-1/4) 0 0 (1/4) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell0_3 : chordRectangleTest 4 sharedChord521Params (-1/4) 0 (1/4) (1/2) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell1_0 : chordRectangleTest 4 sharedChord521Params 0 (1/4) (-1/2) (-1/4) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell1_1 : chordRectangleTest 4 sharedChord521Params 0 (1/4) (-1/4) 0 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell1_2 : chordRectangleTest 4 sharedChord521Params 0 (1/4) 0 (1/4) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell1_3 : chordRectangleTest 4 sharedChord521Params 0 (1/4) (1/4) (1/2) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell2_0 : chordRectangleTest 4 sharedChord521Params (1/4) (1/2) (-1/2) (-1/4) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell2_1 : chordRectangleTest 4 sharedChord521Params (1/4) (1/2) (-1/4) 0 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell2_2 : chordRectangleTest 4 sharedChord521Params (1/4) (1/2) 0 (1/4) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell2_3 : chordRectangleTest 4 sharedChord521Params (1/4) (1/2) (1/4) (1/2) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell3_0 : chordRectangleTest 4 sharedChord521Params (1/2) (3/4) (-1/2) (-1/4) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell3_1 : chordRectangleTest 4 sharedChord521Params (1/2) (3/4) (-1/4) 0 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell3_2 : chordRectangleTest 4 sharedChord521Params (1/2) (3/4) 0 (1/4) 124320=true := by decide +kernel
theorem sharedChord521Disk4Cell3_3 : chordRectangleTest 4 sharedChord521Params (1/2) (3/4) (1/4) (1/2) 124320=true := by decide +kernel
theorem sharedChord521Disk4 {t a : ℝ} (ps : sharedChord521Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord521Bd (4:Fin 9)) (2*jacobiCellRadius sharedChord521Bd (4:Fin 9)) (sharedChord521M 4) t a := by
  rw [show jacobiCellCenter sharedChord521Bd (4:Fin 9)=(1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord521Bd (4:Fin 9)=(1/2) by decide +kernel, show sharedChord521M 4=124320 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((1/4):ℚ)-(1/2)=(-1/4) by decide +kernel, show ((1/4):ℚ)+(1/2)=(3/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell0_1
  have piece0_2 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell0_2
  have piece0_3 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell0_3
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell1_1
  have piece1_2 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell1_2
  have piece1_3 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell1_3
  have piece2_0 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell2_0
  have piece2_1 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell2_1
  have piece2_2 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell2_2
  have piece2_3 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell2_3
  have piece3_0 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell3_0
  have piece3_1 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell3_1
  have piece3_2 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell3_2
  have piece3_3 := chordRectangleTest_sound ps ht sharedChord521Disk4Cell3_3
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece0_2 piece0_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece1_0 piece1_1) (ChordRectangleBound.joinY piece1_2 piece1_3))) (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece2_0 piece2_1) (ChordRectangleBound.joinY piece2_2 piece2_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece3_0 piece3_1) (ChordRectangleBound.joinY piece3_2 piece3_3))))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord521Disk4
