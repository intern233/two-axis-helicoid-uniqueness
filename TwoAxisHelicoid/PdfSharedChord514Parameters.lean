import TwoAxisHelicoid.PdfComplexChordDisk

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sharedChord514Params : ChordParams := ⟨⟨(-20440066785308027433318),(-18332900498891248935331),true⟩,⟨2137651319031893418670380,2235925974106776473668729,true⟩,⟨112626118534067358201006,123837758399665602362219,true⟩,⟨190180358094918304144331,206286043109864412071146,true⟩,⟨292795170011884810558260,309695221209834628882329,true⟩,⟨1168725380079466345313892,1172807735630698749478162,true⟩,⟨(-2456322777553789056744789),(-2384194200078954774926196),true⟩,⟨⟨1089179779498290805396579,1255970972104807774699213,true⟩,⟨(-2011546),2011546,true⟩⟩⟩
theorem sharedChord514Params_ok : chordParams (Grid.ofRats (3/4) (77/100)) (Grid.ofRats (921051395650439/1649267441664000) (311497591431881/549755813888000))=sharedChord514Params := by decide +kernel
theorem sharedChord514ParamSound {t a : ℝ} (tl : (((3/4):ℚ):ℝ)≤t) (tu : t≤(((77/100):ℚ):ℝ)) (al : (((921051395650439/1649267441664000):ℚ):ℝ)≤a) (au : a≤(((311497591431881/549755813888000):ℚ):ℝ)) (ht : 0<t) : sharedChord514Params.Sound t a := by
  rw [← sharedChord514Params_ok]
  exact chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
def sharedChord514Bd (i : ℕ) : ℚ := match i with
  | 0 => (-1)
  | 1 => (-7/8)
  | 2 => (-3/4)
  | 3 => (-1/2)
  | 4 => 0
  | 5 => (1/2)
  | 6 => (3/4)
  | 7 => (7/8)
  | _ => 1
def sharedChord514M (i : Fin 8) : ℚ := match i.val with
  | 0 => 231159
  | 1 => 11194
  | 2 => 6846043
  | 3 => 7815
  | 4 => 363502
  | 5 => 914206
  | 6 => 112516
  | _ => 112516

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord514ParamSound
