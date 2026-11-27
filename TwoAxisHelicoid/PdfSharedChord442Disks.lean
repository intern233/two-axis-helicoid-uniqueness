import TwoAxisHelicoid.PdfSharedChord442Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk0Cell0_0 : chordRectangleTest 4 sharedChord442Params (-257/256) (-253/256) (-1/128) (1/128) 1676777=true := by decide +kernel
theorem sharedChord442Disk0 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (0:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (0:Fin 20)) (sharedChord442M 0) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (0:Fin 20)=(-255/256) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (0:Fin 20)=(1/128) by decide +kernel, show sharedChord442M 0=1676777 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-255/256):ℚ)-(1/128)=(-257/256) by decide +kernel, show ((-255/256):ℚ)+(1/128)=(-253/256) by decide +kernel, show -((1/128):ℚ)=(-1/128) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk0Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk1Cell0_0 : chordRectangleTest 4 sharedChord442Params (-255/256) (-251/256) (-1/128) (1/128) 1787477=true := by decide +kernel
theorem sharedChord442Disk1 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (1:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (1:Fin 20)) (sharedChord442M 1) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (1:Fin 20)=(-253/256) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (1:Fin 20)=(1/128) by decide +kernel, show sharedChord442M 1=1787477 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-253/256):ℚ)-(1/128)=(-255/256) by decide +kernel, show ((-253/256):ℚ)+(1/128)=(-251/256) by decide +kernel, show -((1/128):ℚ)=(-1/128) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk1Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk2Cell0_0 : chordRectangleTest 4 sharedChord442Params (-253/256) (-249/256) (-1/128) (1/128) 797374=true := by decide +kernel
theorem sharedChord442Disk2 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (2:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (2:Fin 20)) (sharedChord442M 2) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (2:Fin 20)=(-251/256) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (2:Fin 20)=(1/128) by decide +kernel, show sharedChord442M 2=797374 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-251/256):ℚ)-(1/128)=(-253/256) by decide +kernel, show ((-251/256):ℚ)+(1/128)=(-249/256) by decide +kernel, show -((1/128):ℚ)=(-1/128) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk2Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk3Cell0_0 : chordRectangleTest 4 sharedChord442Params (-251/256) (-247/256) (-1/128) (1/128) 185299=true := by decide +kernel
theorem sharedChord442Disk3 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (3:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (3:Fin 20)) (sharedChord442M 3) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (3:Fin 20)=(-249/256) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (3:Fin 20)=(1/128) by decide +kernel, show sharedChord442M 3=185299 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-249/256):ℚ)-(1/128)=(-251/256) by decide +kernel, show ((-249/256):ℚ)+(1/128)=(-247/256) by decide +kernel, show -((1/128):ℚ)=(-1/128) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk3Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk4Cell0_0 : chordRectangleTest 4 sharedChord442Params (-125/128) (-123/128) (-1/64) 0 920547=true := by decide +kernel
theorem sharedChord442Disk4Cell0_1 : chordRectangleTest 4 sharedChord442Params (-125/128) (-123/128) 0 (1/64) 920547=true := by decide +kernel
theorem sharedChord442Disk4Cell1_0 : chordRectangleTest 4 sharedChord442Params (-123/128) (-121/128) (-1/64) 0 920547=true := by decide +kernel
theorem sharedChord442Disk4Cell1_1 : chordRectangleTest 4 sharedChord442Params (-123/128) (-121/128) 0 (1/64) 920547=true := by decide +kernel
theorem sharedChord442Disk4 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (4:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (4:Fin 20)) (sharedChord442M 4) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (4:Fin 20)=(-123/128) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (4:Fin 20)=(1/64) by decide +kernel, show sharedChord442M 4=920547 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-123/128):ℚ)-(1/64)=(-125/128) by decide +kernel, show ((-123/128):ℚ)+(1/64)=(-121/128) by decide +kernel, show -((1/64):ℚ)=(-1/64) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk4Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord442Disk4Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord442Disk4Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord442Disk4Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk5Cell0_0 : chordRectangleTest 4 sharedChord442Params (-123/128) (-119/128) (-1/64) (1/64) 50928=true := by decide +kernel
theorem sharedChord442Disk5 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (5:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (5:Fin 20)) (sharedChord442M 5) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (5:Fin 20)=(-121/128) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (5:Fin 20)=(1/64) by decide +kernel, show sharedChord442M 5=50928 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-121/128):ℚ)-(1/64)=(-123/128) by decide +kernel, show ((-121/128):ℚ)+(1/64)=(-119/128) by decide +kernel, show -((1/64):ℚ)=(-1/64) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk5Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk6Cell0_0 : chordRectangleTest 4 sharedChord442Params (-61/64) (-57/64) (-1/32) (1/32) 201580=true := by decide +kernel
theorem sharedChord442Disk6 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (6:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (6:Fin 20)) (sharedChord442M 6) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (6:Fin 20)=(-59/64) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (6:Fin 20)=(1/32) by decide +kernel, show sharedChord442M 6=201580 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-59/64):ℚ)-(1/32)=(-61/64) by decide +kernel, show ((-59/64):ℚ)+(1/32)=(-57/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk6Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk7Cell0_0 : chordRectangleTest 4 sharedChord442Params (-59/64) (-55/64) (-1/32) (1/32) 1967=true := by decide +kernel
theorem sharedChord442Disk7 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (7:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (7:Fin 20)) (sharedChord442M 7) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (7:Fin 20)=(-57/64) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (7:Fin 20)=(1/32) by decide +kernel, show sharedChord442M 7=1967 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-57/64):ℚ)-(1/32)=(-59/64) by decide +kernel, show ((-57/64):ℚ)+(1/32)=(-55/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk7Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk8Cell0_0 : chordRectangleTest 4 sharedChord442Params (-15/16) (-13/16) (-1/8) 0 49802=true := by decide +kernel
theorem sharedChord442Disk8Cell0_1 : chordRectangleTest 4 sharedChord442Params (-15/16) (-13/16) 0 (1/8) 49802=true := by decide +kernel
theorem sharedChord442Disk8Cell1_0 : chordRectangleTest 4 sharedChord442Params (-13/16) (-11/16) (-1/8) 0 49802=true := by decide +kernel
theorem sharedChord442Disk8Cell1_1 : chordRectangleTest 4 sharedChord442Params (-13/16) (-11/16) 0 (1/8) 49802=true := by decide +kernel
theorem sharedChord442Disk8 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (8:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (8:Fin 20)) (sharedChord442M 8) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (8:Fin 20)=(-13/16) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (8:Fin 20)=(1/8) by decide +kernel, show sharedChord442M 8=49802 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-13/16):ℚ)-(1/8)=(-15/16) by decide +kernel, show ((-13/16):ℚ)+(1/8)=(-11/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk8Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord442Disk8Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord442Disk8Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord442Disk8Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk9Cell0_0 : chordRectangleTest 4 sharedChord442Params (-7/8) (-3/8) (-1/4) (1/4) 98188=true := by decide +kernel
theorem sharedChord442Disk9 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (9:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (9:Fin 20)) (sharedChord442M 9) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (9:Fin 20)=(-5/8) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (9:Fin 20)=(1/4) by decide +kernel, show sharedChord442M 9=98188 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-5/8):ℚ)-(1/4)=(-7/8) by decide +kernel, show ((-5/8):ℚ)+(1/4)=(-3/8) by decide +kernel, show -((1/4):ℚ)=(-1/4) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk9Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk10Cell0_0 : chordRectangleTest 4 sharedChord442Params (-3/4) (1/4) (-1/2) (1/2) 57084=true := by decide +kernel
theorem sharedChord442Disk10 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (10:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (10:Fin 20)) (sharedChord442M 10) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (10:Fin 20)=(-1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (10:Fin 20)=(1/2) by decide +kernel, show sharedChord442M 10=57084 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-1/4):ℚ)-(1/2)=(-3/4) by decide +kernel, show ((-1/4):ℚ)+(1/2)=(1/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk10Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk11Cell0_0 : chordRectangleTest 4 sharedChord442Params (-1/4) (3/4) (-1/2) (1/2) 304253=true := by decide +kernel
theorem sharedChord442Disk11 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (11:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (11:Fin 20)) (sharedChord442M 11) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (11:Fin 20)=(1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (11:Fin 20)=(1/2) by decide +kernel, show sharedChord442M 11=304253 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((1/4):ℚ)-(1/2)=(-1/4) by decide +kernel, show ((1/4):ℚ)+(1/2)=(3/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk11Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk12Cell0_0 : chordRectangleTest 4 sharedChord442Params (3/8) (7/8) (-1/4) (1/4) 1168885=true := by decide +kernel
theorem sharedChord442Disk12 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (12:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (12:Fin 20)) (sharedChord442M 12) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (12:Fin 20)=(5/8) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (12:Fin 20)=(1/4) by decide +kernel, show sharedChord442M 12=1168885 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((5/8):ℚ)-(1/4)=(3/8) by decide +kernel, show ((5/8):ℚ)+(1/4)=(7/8) by decide +kernel, show -((1/4):ℚ)=(-1/4) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk12Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk13Cell0_0 : chordRectangleTest 4 sharedChord442Params (11/16) (13/16) (-1/8) 0 1525568=true := by decide +kernel
theorem sharedChord442Disk13Cell0_1 : chordRectangleTest 4 sharedChord442Params (11/16) (13/16) 0 (1/8) 1525568=true := by decide +kernel
theorem sharedChord442Disk13Cell1_0 : chordRectangleTest 4 sharedChord442Params (13/16) (15/16) (-1/8) 0 1525568=true := by decide +kernel
theorem sharedChord442Disk13Cell1_1 : chordRectangleTest 4 sharedChord442Params (13/16) (15/16) 0 (1/8) 1525568=true := by decide +kernel
theorem sharedChord442Disk13 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (13:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (13:Fin 20)) (sharedChord442M 13) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (13:Fin 20)=(13/16) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (13:Fin 20)=(1/8) by decide +kernel, show sharedChord442M 13=1525568 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((13/16):ℚ)-(1/8)=(11/16) by decide +kernel, show ((13/16):ℚ)+(1/8)=(15/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk13Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord442Disk13Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord442Disk13Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord442Disk13Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk14Cell0_0 : chordRectangleTest 4 sharedChord442Params (55/64) (59/64) (-1/32) (1/32) 7725=true := by decide +kernel
theorem sharedChord442Disk14 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (14:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (14:Fin 20)) (sharedChord442M 14) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (14:Fin 20)=(57/64) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (14:Fin 20)=(1/32) by decide +kernel, show sharedChord442M 14=7725 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((57/64):ℚ)-(1/32)=(55/64) by decide +kernel, show ((57/64):ℚ)+(1/32)=(59/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk14Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk15Cell0_0 : chordRectangleTest 4 sharedChord442Params (57/64) (61/64) (-1/32) (1/32) 1996916=true := by decide +kernel
theorem sharedChord442Disk15 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (15:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (15:Fin 20)) (sharedChord442M 15) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (15:Fin 20)=(59/64) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (15:Fin 20)=(1/32) by decide +kernel, show sharedChord442M 15=1996916 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((59/64):ℚ)-(1/32)=(57/64) by decide +kernel, show ((59/64):ℚ)+(1/32)=(61/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk15Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk16Cell0_0 : chordRectangleTest 4 sharedChord442Params (119/128) (123/128) (-1/64) (1/64) 228242=true := by decide +kernel
theorem sharedChord442Disk16 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (16:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (16:Fin 20)) (sharedChord442M 16) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (16:Fin 20)=(121/128) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (16:Fin 20)=(1/64) by decide +kernel, show sharedChord442M 16=228242 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((121/128):ℚ)-(1/64)=(119/128) by decide +kernel, show ((121/128):ℚ)+(1/64)=(123/128) by decide +kernel, show -((1/64):ℚ)=(-1/64) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk16Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk17Cell0_0 : chordRectangleTest 4 sharedChord442Params (121/128) (123/128) (-1/64) 0 1579338=true := by decide +kernel
theorem sharedChord442Disk17Cell0_1 : chordRectangleTest 4 sharedChord442Params (121/128) (123/128) 0 (1/64) 1579338=true := by decide +kernel
theorem sharedChord442Disk17Cell1_0 : chordRectangleTest 4 sharedChord442Params (123/128) (125/128) (-1/64) 0 1579338=true := by decide +kernel
theorem sharedChord442Disk17Cell1_1 : chordRectangleTest 4 sharedChord442Params (123/128) (125/128) 0 (1/64) 1579338=true := by decide +kernel
theorem sharedChord442Disk17 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (17:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (17:Fin 20)) (sharedChord442M 17) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (17:Fin 20)=(123/128) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (17:Fin 20)=(1/64) by decide +kernel, show sharedChord442M 17=1579338 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((123/128):ℚ)-(1/64)=(121/128) by decide +kernel, show ((123/128):ℚ)+(1/64)=(125/128) by decide +kernel, show -((1/64):ℚ)=(-1/64) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk17Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord442Disk17Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord442Disk17Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord442Disk17Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk18Cell0_0 : chordRectangleTest 4 sharedChord442Params (123/128) (31/32) (-1/64) (-1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell0_1 : chordRectangleTest 4 sharedChord442Params (123/128) (31/32) (-1/128) 0 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell0_2 : chordRectangleTest 4 sharedChord442Params (123/128) (31/32) 0 (1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell0_3 : chordRectangleTest 4 sharedChord442Params (123/128) (31/32) (1/128) (1/64) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell1_0 : chordRectangleTest 4 sharedChord442Params (31/32) (125/128) (-1/64) (-1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell1_1 : chordRectangleTest 4 sharedChord442Params (31/32) (125/128) (-1/128) 0 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell1_2 : chordRectangleTest 4 sharedChord442Params (31/32) (125/128) 0 (1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell1_3 : chordRectangleTest 4 sharedChord442Params (31/32) (125/128) (1/128) (1/64) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell2_0 : chordRectangleTest 4 sharedChord442Params (125/128) (63/64) (-1/64) (-1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell2_1 : chordRectangleTest 4 sharedChord442Params (125/128) (63/64) (-1/128) 0 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell2_2 : chordRectangleTest 4 sharedChord442Params (125/128) (63/64) 0 (1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell2_3 : chordRectangleTest 4 sharedChord442Params (125/128) (63/64) (1/128) (1/64) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell3_0 : chordRectangleTest 4 sharedChord442Params (63/64) (127/128) (-1/64) (-1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell3_1 : chordRectangleTest 4 sharedChord442Params (63/64) (127/128) (-1/128) 0 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell3_2 : chordRectangleTest 4 sharedChord442Params (63/64) (127/128) 0 (1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk18Cell3_3 : chordRectangleTest 4 sharedChord442Params (63/64) (127/128) (1/128) (1/64) 5620714=true := by decide +kernel
theorem sharedChord442Disk18 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (18:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (18:Fin 20)) (sharedChord442M 18) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (18:Fin 20)=(125/128) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (18:Fin 20)=(1/64) by decide +kernel, show sharedChord442M 18=5620714 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((125/128):ℚ)-(1/64)=(123/128) by decide +kernel, show ((125/128):ℚ)+(1/64)=(127/128) by decide +kernel, show -((1/64):ℚ)=(-1/64) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell0_1
  have piece0_2 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell0_2
  have piece0_3 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell0_3
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell1_1
  have piece1_2 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell1_2
  have piece1_3 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell1_3
  have piece2_0 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell2_0
  have piece2_1 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell2_1
  have piece2_2 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell2_2
  have piece2_3 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell2_3
  have piece3_0 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell3_0
  have piece3_1 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell3_1
  have piece3_2 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell3_2
  have piece3_3 := chordRectangleTest_sound ps ht sharedChord442Disk18Cell3_3
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece0_2 piece0_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece1_0 piece1_1) (ChordRectangleBound.joinY piece1_2 piece1_3))) (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece2_0 piece2_1) (ChordRectangleBound.joinY piece2_2 piece2_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece3_0 piece3_1) (ChordRectangleBound.joinY piece3_2 piece3_3))))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disk19Cell0_0 : chordRectangleTest 4 sharedChord442Params (125/128) (63/64) (-1/64) (-1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell0_1 : chordRectangleTest 4 sharedChord442Params (125/128) (63/64) (-1/128) 0 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell0_2 : chordRectangleTest 4 sharedChord442Params (125/128) (63/64) 0 (1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell0_3 : chordRectangleTest 4 sharedChord442Params (125/128) (63/64) (1/128) (1/64) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell1_0 : chordRectangleTest 4 sharedChord442Params (63/64) (127/128) (-1/64) (-1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell1_1 : chordRectangleTest 4 sharedChord442Params (63/64) (127/128) (-1/128) 0 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell1_2 : chordRectangleTest 4 sharedChord442Params (63/64) (127/128) 0 (1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell1_3 : chordRectangleTest 4 sharedChord442Params (63/64) (127/128) (1/128) (1/64) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell2_0 : chordRectangleTest 4 sharedChord442Params (127/128) 1 (-1/64) (-1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell2_1 : chordRectangleTest 4 sharedChord442Params (127/128) 1 (-1/128) 0 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell2_2 : chordRectangleTest 4 sharedChord442Params (127/128) 1 0 (1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell2_3 : chordRectangleTest 4 sharedChord442Params (127/128) 1 (1/128) (1/64) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell3_0 : chordRectangleTest 4 sharedChord442Params 1 (129/128) (-1/64) (-1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell3_1 : chordRectangleTest 4 sharedChord442Params 1 (129/128) (-1/128) 0 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell3_2 : chordRectangleTest 4 sharedChord442Params 1 (129/128) 0 (1/128) 5620714=true := by decide +kernel
theorem sharedChord442Disk19Cell3_3 : chordRectangleTest 4 sharedChord442Params 1 (129/128) (1/128) (1/64) 5620714=true := by decide +kernel
theorem sharedChord442Disk19 {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord442Bd (19:Fin 20)) (2*jacobiCellRadius sharedChord442Bd (19:Fin 20)) (sharedChord442M 19) t a := by
  rw [show jacobiCellCenter sharedChord442Bd (19:Fin 20)=(127/128) by decide +kernel, show 2*jacobiCellRadius sharedChord442Bd (19:Fin 20)=(1/64) by decide +kernel, show sharedChord442M 19=5620714 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((127/128):ℚ)-(1/64)=(125/128) by decide +kernel, show ((127/128):ℚ)+(1/64)=(129/128) by decide +kernel, show -((1/64):ℚ)=(-1/64) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell0_1
  have piece0_2 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell0_2
  have piece0_3 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell0_3
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell1_1
  have piece1_2 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell1_2
  have piece1_3 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell1_3
  have piece2_0 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell2_0
  have piece2_1 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell2_1
  have piece2_2 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell2_2
  have piece2_3 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell2_3
  have piece3_0 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell3_0
  have piece3_1 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell3_1
  have piece3_2 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell3_2
  have piece3_3 := chordRectangleTest_sound ps ht sharedChord442Disk19Cell3_3
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece0_2 piece0_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece1_0 piece1_1) (ChordRectangleBound.joinY piece1_2 piece1_3))) (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece2_0 piece2_1) (ChordRectangleBound.joinY piece2_2 piece2_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece3_0 piece3_1) (ChordRectangleBound.joinY piece3_2 piece3_3))))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord442Disks {t a : ℝ} (ps : sharedChord442Params.Sound t a) (ht : 0<t) :
    ∀ i : Fin 20, ChordDiskBound (jacobiCellCenter sharedChord442Bd i) (2*jacobiCellRadius sharedChord442Bd i) (sharedChord442M i) t a := by
  intro i
  fin_cases i
  · exact sharedChord442Disk0 ps ht
  · exact sharedChord442Disk1 ps ht
  · exact sharedChord442Disk2 ps ht
  · exact sharedChord442Disk3 ps ht
  · exact sharedChord442Disk4 ps ht
  · exact sharedChord442Disk5 ps ht
  · exact sharedChord442Disk6 ps ht
  · exact sharedChord442Disk7 ps ht
  · exact sharedChord442Disk8 ps ht
  · exact sharedChord442Disk9 ps ht
  · exact sharedChord442Disk10 ps ht
  · exact sharedChord442Disk11 ps ht
  · exact sharedChord442Disk12 ps ht
  · exact sharedChord442Disk13 ps ht
  · exact sharedChord442Disk14 ps ht
  · exact sharedChord442Disk15 ps ht
  · exact sharedChord442Disk16 ps ht
  · exact sharedChord442Disk17 ps ht
  · exact sharedChord442Disk18 ps ht
  · exact sharedChord442Disk19 ps ht

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord442Disks
