import TwoAxisHelicoid.PdfSharedChord493Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk0Cell0_0 : chordRectangleTest 4 sharedChord493Params (-33/32) (-31/32) (-1/16) 0 96466=true := by decide +kernel
theorem sharedChord493Disk0Cell0_1 : chordRectangleTest 4 sharedChord493Params (-33/32) (-31/32) 0 (1/16) 96466=true := by decide +kernel
theorem sharedChord493Disk0Cell1_0 : chordRectangleTest 4 sharedChord493Params (-31/32) (-29/32) (-1/16) 0 96466=true := by decide +kernel
theorem sharedChord493Disk0Cell1_1 : chordRectangleTest 4 sharedChord493Params (-31/32) (-29/32) 0 (1/16) 96466=true := by decide +kernel
theorem sharedChord493Disk0 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (0:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (0:Fin 13)) (sharedChord493M 0) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (0:Fin 13)=(-31/32) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (0:Fin 13)=(1/16) by decide +kernel, show sharedChord493M 0=96466 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-31/32):ℚ)-(1/16)=(-33/32) by decide +kernel, show ((-31/32):ℚ)+(1/16)=(-29/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk0Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord493Disk0Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord493Disk0Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord493Disk0Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk1Cell0_0 : chordRectangleTest 4 sharedChord493Params (-31/32) (-27/32) (-1/16) (1/16) 8386107=true := by decide +kernel
theorem sharedChord493Disk1 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (1:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (1:Fin 13)) (sharedChord493M 1) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (1:Fin 13)=(-29/32) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (1:Fin 13)=(1/16) by decide +kernel, show sharedChord493M 1=8386107 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-29/32):ℚ)-(1/16)=(-31/32) by decide +kernel, show ((-29/32):ℚ)+(1/16)=(-27/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk1Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk2Cell0_0 : chordRectangleTest 4 sharedChord493Params (-29/32) (-25/32) (-1/16) (1/16) 41309=true := by decide +kernel
theorem sharedChord493Disk2 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (2:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (2:Fin 13)) (sharedChord493M 2) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (2:Fin 13)=(-27/32) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (2:Fin 13)=(1/16) by decide +kernel, show sharedChord493M 2=41309 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-27/32):ℚ)-(1/16)=(-29/32) by decide +kernel, show ((-27/32):ℚ)+(1/16)=(-25/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk2Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk3Cell0_0 : chordRectangleTest 4 sharedChord493Params (-27/32) (-23/32) (-1/16) (1/16) 1849=true := by decide +kernel
theorem sharedChord493Disk3 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (3:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (3:Fin 13)) (sharedChord493M 3) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (3:Fin 13)=(-25/32) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (3:Fin 13)=(1/16) by decide +kernel, show sharedChord493M 3=1849 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-25/32):ℚ)-(1/16)=(-27/32) by decide +kernel, show ((-25/32):ℚ)+(1/16)=(-23/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk3Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk4Cell0_0 : chordRectangleTest 4 sharedChord493Params (-7/8) (-3/4) (-1/4) (-1/8) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell0_1 : chordRectangleTest 4 sharedChord493Params (-7/8) (-3/4) (-1/8) 0 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell0_2 : chordRectangleTest 4 sharedChord493Params (-7/8) (-3/4) 0 (1/8) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell0_3 : chordRectangleTest 4 sharedChord493Params (-7/8) (-3/4) (1/8) (1/4) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell1_0 : chordRectangleTest 4 sharedChord493Params (-3/4) (-5/8) (-1/4) (-1/8) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell1_1 : chordRectangleTest 4 sharedChord493Params (-3/4) (-5/8) (-1/8) 0 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell1_2 : chordRectangleTest 4 sharedChord493Params (-3/4) (-5/8) 0 (1/8) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell1_3 : chordRectangleTest 4 sharedChord493Params (-3/4) (-5/8) (1/8) (1/4) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell2_0 : chordRectangleTest 4 sharedChord493Params (-5/8) (-1/2) (-1/4) (-1/8) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell2_1 : chordRectangleTest 4 sharedChord493Params (-5/8) (-1/2) (-1/8) 0 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell2_2 : chordRectangleTest 4 sharedChord493Params (-5/8) (-1/2) 0 (1/8) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell2_3 : chordRectangleTest 4 sharedChord493Params (-5/8) (-1/2) (1/8) (1/4) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell3_0 : chordRectangleTest 4 sharedChord493Params (-1/2) (-3/8) (-1/4) (-1/8) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell3_1 : chordRectangleTest 4 sharedChord493Params (-1/2) (-3/8) (-1/8) 0 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell3_2 : chordRectangleTest 4 sharedChord493Params (-1/2) (-3/8) 0 (1/8) 74314=true := by decide +kernel
theorem sharedChord493Disk4Cell3_3 : chordRectangleTest 4 sharedChord493Params (-1/2) (-3/8) (1/8) (1/4) 74314=true := by decide +kernel
theorem sharedChord493Disk4 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (4:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (4:Fin 13)) (sharedChord493M 4) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (4:Fin 13)=(-5/8) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (4:Fin 13)=(1/4) by decide +kernel, show sharedChord493M 4=74314 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-5/8):ℚ)-(1/4)=(-7/8) by decide +kernel, show ((-5/8):ℚ)+(1/4)=(-3/8) by decide +kernel, show -((1/4):ℚ)=(-1/4) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell0_1
  have piece0_2 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell0_2
  have piece0_3 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell0_3
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell1_1
  have piece1_2 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell1_2
  have piece1_3 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell1_3
  have piece2_0 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell2_0
  have piece2_1 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell2_1
  have piece2_2 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell2_2
  have piece2_3 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell2_3
  have piece3_0 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell3_0
  have piece3_1 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell3_1
  have piece3_2 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell3_2
  have piece3_3 := chordRectangleTest_sound ps ht sharedChord493Disk4Cell3_3
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece0_2 piece0_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece1_0 piece1_1) (ChordRectangleBound.joinY piece1_2 piece1_3))) (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece2_0 piece2_1) (ChordRectangleBound.joinY piece2_2 piece2_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece3_0 piece3_1) (ChordRectangleBound.joinY piece3_2 piece3_3))))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk5Cell0_0 : chordRectangleTest 4 sharedChord493Params (-3/4) (-1/4) (-1/2) 0 31440=true := by decide +kernel
theorem sharedChord493Disk5Cell0_1 : chordRectangleTest 4 sharedChord493Params (-3/4) (-1/4) 0 (1/2) 31440=true := by decide +kernel
theorem sharedChord493Disk5Cell1_0 : chordRectangleTest 4 sharedChord493Params (-1/4) (1/4) (-1/2) 0 31440=true := by decide +kernel
theorem sharedChord493Disk5Cell1_1 : chordRectangleTest 4 sharedChord493Params (-1/4) (1/4) 0 (1/2) 31440=true := by decide +kernel
theorem sharedChord493Disk5 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (5:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (5:Fin 13)) (sharedChord493M 5) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (5:Fin 13)=(-1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (5:Fin 13)=(1/2) by decide +kernel, show sharedChord493M 5=31440 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-1/4):ℚ)-(1/2)=(-3/4) by decide +kernel, show ((-1/4):ℚ)+(1/2)=(1/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk5Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord493Disk5Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord493Disk5Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord493Disk5Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk6Cell0_0 : chordRectangleTest 4 sharedChord493Params (-1/4) (1/4) (-1/2) 0 1941435=true := by decide +kernel
theorem sharedChord493Disk6Cell0_1 : chordRectangleTest 4 sharedChord493Params (-1/4) (1/4) 0 (1/2) 1941435=true := by decide +kernel
theorem sharedChord493Disk6Cell1_0 : chordRectangleTest 4 sharedChord493Params (1/4) (3/4) (-1/2) 0 1941435=true := by decide +kernel
theorem sharedChord493Disk6Cell1_1 : chordRectangleTest 4 sharedChord493Params (1/4) (3/4) 0 (1/2) 1941435=true := by decide +kernel
theorem sharedChord493Disk6 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (6:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (6:Fin 13)) (sharedChord493M 6) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (6:Fin 13)=(1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (6:Fin 13)=(1/2) by decide +kernel, show sharedChord493M 6=1941435 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((1/4):ℚ)-(1/2)=(-1/4) by decide +kernel, show ((1/4):ℚ)+(1/2)=(3/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk6Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord493Disk6Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord493Disk6Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord493Disk6Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk7Cell0_0 : chordRectangleTest 4 sharedChord493Params (7/16) (11/16) (-1/8) (1/8) 1430=true := by decide +kernel
theorem sharedChord493Disk7 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (7:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (7:Fin 13)) (sharedChord493M 7) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (7:Fin 13)=(9/16) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (7:Fin 13)=(1/8) by decide +kernel, show sharedChord493M 7=1430 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((9/16):ℚ)-(1/8)=(7/16) by decide +kernel, show ((9/16):ℚ)+(1/8)=(11/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk7Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk8Cell0_0 : chordRectangleTest 4 sharedChord493Params (9/16) (13/16) (-1/8) (1/8) 282574=true := by decide +kernel
theorem sharedChord493Disk8 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (8:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (8:Fin 13)) (sharedChord493M 8) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (8:Fin 13)=(11/16) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (8:Fin 13)=(1/8) by decide +kernel, show sharedChord493M 8=282574 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((11/16):ℚ)-(1/8)=(9/16) by decide +kernel, show ((11/16):ℚ)+(1/8)=(13/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk8Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk9Cell0_0 : chordRectangleTest 4 sharedChord493Params (23/32) (27/32) (-1/16) (1/16) 9650=true := by decide +kernel
theorem sharedChord493Disk9 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (9:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (9:Fin 13)) (sharedChord493M 9) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (9:Fin 13)=(25/32) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (9:Fin 13)=(1/16) by decide +kernel, show sharedChord493M 9=9650 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((25/32):ℚ)-(1/16)=(23/32) by decide +kernel, show ((25/32):ℚ)+(1/16)=(27/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk9Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk10Cell0_0 : chordRectangleTest 4 sharedChord493Params (25/32) (29/32) (-1/16) (1/16) 215687=true := by decide +kernel
theorem sharedChord493Disk10 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (10:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (10:Fin 13)) (sharedChord493M 10) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (10:Fin 13)=(27/32) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (10:Fin 13)=(1/16) by decide +kernel, show sharedChord493M 10=215687 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((27/32):ℚ)-(1/16)=(25/32) by decide +kernel, show ((27/32):ℚ)+(1/16)=(29/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk10Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk11Cell0_0 : chordRectangleTest 4 sharedChord493Params (27/32) (31/32) (-1/16) (1/16) 8092339=true := by decide +kernel
theorem sharedChord493Disk11 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (11:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (11:Fin 13)) (sharedChord493M 11) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (11:Fin 13)=(29/32) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (11:Fin 13)=(1/16) by decide +kernel, show sharedChord493M 11=8092339 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((29/32):ℚ)-(1/16)=(27/32) by decide +kernel, show ((29/32):ℚ)+(1/16)=(31/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk11Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disk12Cell0_0 : chordRectangleTest 4 sharedChord493Params (29/32) (31/32) (-1/16) 0 101100=true := by decide +kernel
theorem sharedChord493Disk12Cell0_1 : chordRectangleTest 4 sharedChord493Params (29/32) (31/32) 0 (1/16) 101100=true := by decide +kernel
theorem sharedChord493Disk12Cell1_0 : chordRectangleTest 4 sharedChord493Params (31/32) (33/32) (-1/16) 0 101100=true := by decide +kernel
theorem sharedChord493Disk12Cell1_1 : chordRectangleTest 4 sharedChord493Params (31/32) (33/32) 0 (1/16) 101100=true := by decide +kernel
theorem sharedChord493Disk12 {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord493Bd (12:Fin 13)) (2*jacobiCellRadius sharedChord493Bd (12:Fin 13)) (sharedChord493M 12) t a := by
  rw [show jacobiCellCenter sharedChord493Bd (12:Fin 13)=(31/32) by decide +kernel, show 2*jacobiCellRadius sharedChord493Bd (12:Fin 13)=(1/16) by decide +kernel, show sharedChord493M 12=101100 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((31/32):ℚ)-(1/16)=(29/32) by decide +kernel, show ((31/32):ℚ)+(1/16)=(33/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord493Disk12Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord493Disk12Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord493Disk12Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord493Disk12Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord493Disks {t a : ℝ} (ps : sharedChord493Params.Sound t a) (ht : 0<t) :
    ∀ i : Fin 13, ChordDiskBound (jacobiCellCenter sharedChord493Bd i) (2*jacobiCellRadius sharedChord493Bd i) (sharedChord493M i) t a := by
  intro i
  fin_cases i
  · exact sharedChord493Disk0 ps ht
  · exact sharedChord493Disk1 ps ht
  · exact sharedChord493Disk2 ps ht
  · exact sharedChord493Disk3 ps ht
  · exact sharedChord493Disk4 ps ht
  · exact sharedChord493Disk5 ps ht
  · exact sharedChord493Disk6 ps ht
  · exact sharedChord493Disk7 ps ht
  · exact sharedChord493Disk8 ps ht
  · exact sharedChord493Disk9 ps ht
  · exact sharedChord493Disk10 ps ht
  · exact sharedChord493Disk11 ps ht
  · exact sharedChord493Disk12 ps ht

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord493Disks
