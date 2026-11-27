import TwoAxisHelicoid.PdfComplexChordDisk

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sharedChord490Params : ChordParams := ⟨⟨(-9270165264322248947552),(-8255110690802907805332),true⟩,⟨2710046822240459639347395,2833264197946857373122177,true⟩,⟨81933213273781702719538,91461635766597394293732,true⟩,⟨116032030401088281343712,128482062281660397166641,true⟩,⟨198277649592620448774696,210289735156063185606732,true⟩,⟨1190526576341392739902660,1192527573126518129999062,true⟩,⟨(-2973361795982170076186840),(-2899340733439943857673502),true⟩,⟨⟨1126341143940947658780743,1259983290581186804086220,true⟩,⟨(-470),470,true⟩⟩⟩
theorem sharedChord490Params_ok : chordParams (Grid.ofRats (63/100) (129/200)) (Grid.ofRats (291382337698939/549755813888000) (296734670424149/549755813888000))=sharedChord490Params := by decide +kernel
theorem sharedChord490ParamSound {t a : ℝ} (tl : (((63/100):ℚ):ℝ)≤t) (tu : t≤(((129/200):ℚ):ℝ)) (al : (((291382337698939/549755813888000):ℚ):ℝ)≤a) (au : a≤(((296734670424149/549755813888000):ℚ):ℝ)) (ht : 0<t) : sharedChord490Params.Sound t a := by
  rw [← sharedChord490Params_ok]
  exact chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
def sharedChord490Bd (i : ℕ) : ℚ := match i with
  | 0 => (-1)
  | 1 => (-15/16)
  | 2 => (-7/8)
  | 3 => (-3/4)
  | 4 => (-1/2)
  | 5 => 0
  | 6 => (1/2)
  | 7 => (3/4)
  | 8 => (7/8)
  | 9 => (15/16)
  | _ => 1
def sharedChord490M (i : Fin 10) : ℚ := match i.val with
  | 0 => 11141
  | 1 => 4439
  | 2 => 297201
  | 3 => 9204457
  | 4 => 236540
  | 5 => 2951134
  | 6 => 619095
  | 7 => 166035
  | 8 => 32581
  | _ => 22003

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord490ParamSound
