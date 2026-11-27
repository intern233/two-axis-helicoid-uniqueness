import TwoAxisHelicoid.PdfSharedChord490Disk0
import TwoAxisHelicoid.PdfSharedChord490Disk1
import TwoAxisHelicoid.PdfSharedChord490Disk2
import TwoAxisHelicoid.PdfSharedChord490Disk3
import TwoAxisHelicoid.PdfSharedChord490Disk4
import TwoAxisHelicoid.PdfSharedChord490Disk5
import TwoAxisHelicoid.PdfSharedChord490Disk6
import TwoAxisHelicoid.PdfSharedChord490Disk7
import TwoAxisHelicoid.PdfSharedChord490Disk8
import TwoAxisHelicoid.PdfSharedChord490Disk9

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord490Disks {t a : ℝ} (ps : sharedChord490Params.Sound t a) (ht : 0<t) :
    ∀ i : Fin 10, ChordDiskBound (jacobiCellCenter sharedChord490Bd i) (2*jacobiCellRadius sharedChord490Bd i) (sharedChord490M i) t a := by
  intro i
  fin_cases i
  · exact sharedChord490Disk0 ps ht
  · exact sharedChord490Disk1 ps ht
  · exact sharedChord490Disk2 ps ht
  · exact sharedChord490Disk3 ps ht
  · exact sharedChord490Disk4 ps ht
  · exact sharedChord490Disk5 ps ht
  · exact sharedChord490Disk6 ps ht
  · exact sharedChord490Disk7 ps ht
  · exact sharedChord490Disk8 ps ht
  · exact sharedChord490Disk9 ps ht

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord490Disks
