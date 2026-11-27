import TwoAxisHelicoid.PdfSharedChord521Disk0
import TwoAxisHelicoid.PdfSharedChord521Disk1
import TwoAxisHelicoid.PdfSharedChord521Disk2
import TwoAxisHelicoid.PdfSharedChord521Disk3
import TwoAxisHelicoid.PdfSharedChord521Disk4
import TwoAxisHelicoid.PdfSharedChord521Disk5
import TwoAxisHelicoid.PdfSharedChord521Disk6
import TwoAxisHelicoid.PdfSharedChord521Disk7
import TwoAxisHelicoid.PdfSharedChord521Disk8

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord521Disks {t a : ℝ} (ps : sharedChord521Params.Sound t a) (ht : 0<t) :
    ∀ i : Fin 9, ChordDiskBound (jacobiCellCenter sharedChord521Bd i) (2*jacobiCellRadius sharedChord521Bd i) (sharedChord521M i) t a := by
  intro i
  fin_cases i
  · exact sharedChord521Disk0 ps ht
  · exact sharedChord521Disk1 ps ht
  · exact sharedChord521Disk2 ps ht
  · exact sharedChord521Disk3 ps ht
  · exact sharedChord521Disk4 ps ht
  · exact sharedChord521Disk5 ps ht
  · exact sharedChord521Disk6 ps ht
  · exact sharedChord521Disk7 ps ht
  · exact sharedChord521Disk8 ps ht

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord521Disks
