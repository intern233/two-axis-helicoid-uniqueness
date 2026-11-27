import TwoAxisHelicoid.PdfComplexChordDisk

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sharedChord521Params : ChordParams := ⟨⟨(-30008963931755923068592),(-20440066785308027432873),true⟩,⟨1837228791705133868146624,2150329669639536046045618,true⟩,⟨109410849838673073649763,150324915184004054045926,true⟩,⟨204133966858414508584374,264480481492953711785504,true⟩,⟨306776567947593966040189,374605214427470077121577,true⟩,⟨1150361621080888320861762,1168725380079466345314754,true⟩,⟨(-2384194200078954774935550),(-2125863304564331866723650),true⟩,⟨⟨886635246067586247046948,1516164390967421644189246,true⟩,⟨(-149973597),149973597,true⟩⟩⟩
theorem sharedChord521Params_ok : chordParams (Grid.ofRats (77/100) (17/20)) (Grid.ofRats (930253465593763/1649267441664000) (971120623722397/1649267441664000))=sharedChord521Params := by decide +kernel
theorem sharedChord521ParamSound {t a : ℝ} (tl : (((77/100):ℚ):ℝ)≤t) (tu : t≤(((17/20):ℚ):ℝ)) (al : (((930253465593763/1649267441664000):ℚ):ℝ)≤a) (au : a≤(((971120623722397/1649267441664000):ℚ):ℝ)) (ht : 0<t) : sharedChord521Params.Sound t a := by
  rw [← sharedChord521Params_ok]
  exact chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
def sharedChord521Bd (i : ℕ) : ℚ := match i with
  | 0 => (-1)
  | 1 => (-7/8)
  | 2 => (-3/4)
  | 3 => (-1/2)
  | 4 => 0
  | 5 => (1/2)
  | 6 => (5/8)
  | 7 => (3/4)
  | 8 => (7/8)
  | _ => 1
def sharedChord521M (i : Fin 9) : ℚ := match i.val with
  | 0 => 124381
  | 1 => 958430
  | 2 => 7213645
  | 3 => 310594
  | 4 => 124320
  | 5 => 1973
  | 6 => 149576
  | 7 => 3362141
  | _ => 92513

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord521ParamSound
