import TwoAxisHelicoid.PdfComplexChordDisk

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sharedChord469Params : ChordParams := ⟨⟨(-8255110690802907805538),(-3045001778040279689665),true⟩,⟨2791835980130812229077681,3496532072468663274695087,true⟩,⟨48653541453931612759580,91932269437444016678389,true⟩,⟨67035608637071013071376,120077203177636163149250,true⟩,⟨120522494268457066804135,199296082349088505989300,true⟩,⟨1192527573126518129998654,1202851116816066216313190,true⟩,⟨(-3598922125668220793443082),(-2973361795982170076176350),true⟩,⟨⟨934435474829499701695753,1533805258456606011441182,true⟩,⟨(-196),196,true⟩⟩⟩
theorem sharedChord469Params_ok : chordParams (Grid.ofRats (21/40) (63/100)) (Grid.ofRats (3408482035145/6597069766656) (885480886574489/1649267441664000))=sharedChord469Params := by decide +kernel
theorem sharedChord469ParamSound {t a : ℝ} (tl : (((21/40):ℚ):ℝ)≤t) (tu : t≤(((63/100):ℚ):ℝ)) (al : (((3408482035145/6597069766656):ℚ):ℝ)≤a) (au : a≤(((885480886574489/1649267441664000):ℚ):ℝ)) (ht : 0<t) : sharedChord469Params.Sound t a := by
  rw [← sharedChord469Params_ok]
  exact chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
def sharedChord469Bd (i : ℕ) : ℚ := match i with
  | 0 => (-1)
  | 1 => (-31/32)
  | 2 => (-15/16)
  | 3 => (-29/32)
  | 4 => (-7/8)
  | 5 => (-3/4)
  | 6 => (-1/2)
  | 7 => 0
  | 8 => (1/2)
  | 9 => (3/4)
  | 10 => (13/16)
  | 11 => (7/8)
  | 12 => (29/32)
  | 13 => (15/16)
  | 14 => (31/32)
  | _ => 1
def sharedChord469M (i : Fin 15) : ℚ := match i.val with
  | 0 => 693405
  | 1 => 445802
  | 2 => 36386
  | 3 => 3480
  | 4 => 477114
  | 5 => 32300
  | 6 => 611288
  | 7 => 8967982
  | 8 => 3543046
  | 9 => 3330
  | 10 => 573705
  | 11 => 18391
  | 12 => 145212
  | 13 => 618041
  | _ => 250656

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord469ParamSound
