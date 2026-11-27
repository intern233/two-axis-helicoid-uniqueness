import TwoAxisHelicoid.PdfRefinedChordOriginal
import TwoAxisHelicoid.PositiveChordBox1001
import TwoAxisHelicoid.PositiveChordBox1002
import TwoAxisHelicoid.PositiveChordBox1005

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open ComplexBall CertificateData CertificateSemantics

def originalNodeP079R079Box : HorizontalRectangle := ⟨(879/6400), (11/80), (1099513700575/2199023255552), (1099513733343/2199023255552), (1047665477892462179409537596207791/633825300114114700748351602688), (4575501459194462364506792278700719/633825300114114700748351602688), (-3540562873874641534476262500665225/1267650600228229401496703205376), (442424946374420105963501871439631/158456325028528675187087900672), true, []⟩
def originalNodeP079R079Block1001Params : ChordParams := ⟨⟨(-144431703734041),(-140725846136461),true⟩,⟨13810709820180505305717897,13826422075039610435638989,true⟩,⟨13042992634280896011,13213617791145066688,true⟩,⟨13043559531485128183,13214191451713461864,true⟩,⟨26086556602268066936,26427804734738106343,true⟩,⟨1208925819325765767272604,1208925819333177482466018,true⟩,⟨(-13826448137436658064581756),(-13810736264468536080365647),true⟩,⟨⟨1208924795551334773966509,1208926843108620319050662,true⟩,⟨(-47),47,true⟩⟩⟩
theorem originalNodeP079R079Block1001Params_ok : chordParams (Grid.ofRats (879/6400) (11/80)) (Grid.ofRats (1099513700575/2199023255552) (1099513733343/2199023255552))=originalNodeP079R079Block1001Params := by decide +kernel
def originalNodeP079R079Block1001Nodes (i : Fin 38) (j : Fin 32) : Bool :=
  match i.val,j.val with
  | 12, 9 => true
  | _, _ => false
noncomputable def originalNodeP079R079Block1001Grid : CGrid := refinedChordQuadrature ⟨64,12,6⟩ rationalQuadrature32 32 4 originalNodeP079R079Block1001Params positiveChordBox1001Boundary positiveChordBox1001Radius positiveChordBox1001Cells originalNodeP079R079Block1001Nodes
theorem originalNodeP079R079Block1001Columns : containedInReported originalNodeP079R079Block1001Grid.re originalNodeP079R079Box.reLo originalNodeP079R079Box.reHi=true ∧ containedInReported originalNodeP079R079Block1001Grid.im originalNodeP079R079Box.imLo originalNodeP079R079Box.imHi=true := by decide +kernel
theorem originalNodeP079R079Block1001Sound {t a : ℝ} (tl : (((879/6400):ℚ):ℝ)≤t) (tu : t≤(((11/80):ℚ):ℝ)) (al : (((1099513700575/2199023255552):ℚ):ℝ)≤a) (au : a≤(((1099513733343/2199023255552):ℚ):ℝ)) : originalNodeP079R079Box.Encloses (sourceHorizontalIntegral true t a) := by
  have tp : 0<t := lt_of_lt_of_le (by norm_num) tl
  have up : t≤7/5 := tu.trans (by norm_num)
  have bt : (positiveChordBox1001Parameters.base.base.height.toBall 64).Contains (t:ℂ) := coarsen_contains (realInterval_contains tl tu) (by decide +kernel)
  have ba : (positiveChordBox1001Parameters.base.base.abscissa.toBall 64).Contains (a:ℂ) := coarsen_contains (realInterval_contains al au) (by decide +kernel)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) tp
  rw [originalNodeP079R079Block1001Params_ok] at ps
  have result := refinedChordQuadrature_sound ⟨64,12,6⟩ rationalQuadrature32 rationalQuadrature32_exact rationalQuadrature32_nodes tp up positiveChordBox1001Parameters_valid bt ba ps 4 positiveChordBox1001Boundary (by decide +kernel) (by decide +kernel) positiveChordBox1001Radius positiveChordBox1001Cells positiveChordBox1001Cells_valid originalNodeP079R079Block1001Nodes
  exact refined_dual_output_encloses tp up (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result originalNodeP079R079Block1001Columns.1 originalNodeP079R079Block1001Columns.2

theorem originalNodeP079R079Sound : originalNodeP079R079Box.Sound := by
  intro t a t0 t1 a0 a1
  change (((879/6400):ℚ):ℝ)≤t at t0
  change t≤(((11/80):ℚ):ℝ) at t1
  change (((1099513700575/2199023255552):ℚ):ℝ)≤a at a0
  change a≤(((1099513733343/2199023255552):ℚ):ℝ) at a1
  exact originalNodeP079R079Block1001Sound t0 t1 a0 a1

def originalNodeP079R119Box : HorizontalRectangle := ⟨(919/6400), (23/160), (3298545558743/6597069766656), (3298545755351/6597069766656), (406898273014242147815382838202185/316912650057057350374175801344), (1389332824389687712948504975429449/316912650057057350374175801344), (-3945059438121977861463201833332709/2535301200456458802993406410752), (985930026620103135583352867312647/633825300114114700748351602688), true, []⟩
def originalNodeP079R119Block1002Params : ChordParams := ⟨⟨(-390019110294067),(-380853556872848),true⟩,⟨13210225932261162091735963,13224601286270092418006709,true⟩,⟨21456712185677667870,21713378919682233163,true⟩,⟨21458245522591666783,21714928911815062652,true⟩,⟨42914971657852695022,43428293647369670861,true⟩,⟨1208925818834590954369694,1208925818852922061200446,true⟩,⟨(-13224644078322925297306538),(-13210269464994004306978935),true⟩,⟨⟨1208924278776199195823570,1208927358913598994101427,true⟩,⟨(-47),47,true⟩⟩⟩
theorem originalNodeP079R119Block1002Params_ok : chordParams (Grid.ofRats (919/6400) (23/160)) (Grid.ofRats (3298545558743/6597069766656) (3298545755351/6597069766656))=originalNodeP079R119Block1002Params := by decide +kernel
def originalNodeP079R119Block1002Nodes (i : Fin 34) (j : Fin 32) : Bool :=
  match i.val,j.val with
  | 14, 26 => true
  | _, _ => false
noncomputable def originalNodeP079R119Block1002Grid : CGrid := refinedChordQuadrature ⟨64,12,6⟩ rationalQuadrature32 32 4 originalNodeP079R119Block1002Params positiveChordBox1002Boundary positiveChordBox1002Radius positiveChordBox1002Cells originalNodeP079R119Block1002Nodes
theorem originalNodeP079R119Block1002Columns : containedInReported originalNodeP079R119Block1002Grid.re originalNodeP079R119Box.reLo originalNodeP079R119Box.reHi=true ∧ containedInReported originalNodeP079R119Block1002Grid.im originalNodeP079R119Box.imLo originalNodeP079R119Box.imHi=true := by decide +kernel
theorem originalNodeP079R119Block1002Sound {t a : ℝ} (tl : (((919/6400):ℚ):ℝ)≤t) (tu : t≤(((23/160):ℚ):ℝ)) (al : (((3298545558743/6597069766656):ℚ):ℝ)≤a) (au : a≤(((3298545755351/6597069766656):ℚ):ℝ)) : originalNodeP079R119Box.Encloses (sourceHorizontalIntegral true t a) := by
  have tp : 0<t := lt_of_lt_of_le (by norm_num) tl
  have up : t≤7/5 := tu.trans (by norm_num)
  have bt : (positiveChordBox1002Parameters.base.base.height.toBall 64).Contains (t:ℂ) := coarsen_contains (realInterval_contains tl tu) (by decide +kernel)
  have ba : (positiveChordBox1002Parameters.base.base.abscissa.toBall 64).Contains (a:ℂ) := coarsen_contains (realInterval_contains al au) (by decide +kernel)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) tp
  rw [originalNodeP079R119Block1002Params_ok] at ps
  have result := refinedChordQuadrature_sound ⟨64,12,6⟩ rationalQuadrature32 rationalQuadrature32_exact rationalQuadrature32_nodes tp up positiveChordBox1002Parameters_valid bt ba ps 4 positiveChordBox1002Boundary (by decide +kernel) (by decide +kernel) positiveChordBox1002Radius positiveChordBox1002Cells positiveChordBox1002Cells_valid originalNodeP079R119Block1002Nodes
  exact refined_dual_output_encloses tp up (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result originalNodeP079R119Block1002Columns.1 originalNodeP079R119Block1002Columns.2

theorem originalNodeP079R119Sound : originalNodeP079R119Box.Sound := by
  intro t a t0 t1 a0 a1
  change (((919/6400):ℚ):ℝ)≤t at t0
  change t≤(((23/160):ℚ):ℝ) at t1
  change (((3298545558743/6597069766656):ℚ):ℝ)≤a at a0
  change a≤(((3298545755351/6597069766656):ℚ):ℝ) at a1
  exact originalNodeP079R119Block1002Sound t0 t1 a0 a1

def originalNodeP079R233Box : HorizontalRectangle := ⟨(559/3200), (7/40), (3298625393473/6597069766656), (3298628539201/6597069766656), (503329257827965284623638977517923/2535301200456458802993406410752), (2042431108958917664681077273467235/2535301200456458802993406410752), (-3094826173637071692579111258110021/10141204801825835211973625643008), (773341913215389267344914744586735/2535301200456458802993406410752), true, []⟩
def originalNodeP079R233Block1005Params : ChordParams := ⟨⟨(-19318052653497133),(-18707520603253237),true⟩,⟨10850984679180240168920619,10870406467900717274263304,true⟩,⟨150347794567530169064,152782824342388262004,true⟩,⟨150423295540653906071,152859411086619937376,true⟩,⟨300772365455736400455,305640912933474030758,true⟩,⟨1208925780978524485098264,1208925782199588547178688,true⟩,⟨(-10870704418156770838190732),(-10851292435021245498818336),true⟩,⟨⟨1208911167035360055788874,1208940396348596790775938,true⟩,⟨(-47),47,true⟩⟩⟩
theorem originalNodeP079R233Block1005Params_ok : chordParams (Grid.ofRats (559/3200) (7/40)) (Grid.ofRats (3298625393473/6597069766656) (3298628539201/6597069766656))=originalNodeP079R233Block1005Params := by decide +kernel
def originalNodeP079R233Block1005Nodes (i : Fin 32) (j : Fin 32) : Bool :=
  match i.val,j.val with
  | 13, 10 => true
  | 13, 12 => true
  | 13, 13 => true
  | 13, 14 => true
  | 13, 15 => true
  | 13, 24 => true
  | 13, 25 => true
  | 13, 26 => true
  | 13, 27 => true
  | 13, 28 => true
  | 13, 29 => true
  | 13, 30 => true
  | 13, 31 => true
  | 14, 24 => true
  | 14, 25 => true
  | 14, 26 => true
  | 14, 27 => true
  | _, _ => false
noncomputable def originalNodeP079R233Block1005Grid : CGrid := refinedChordQuadrature ⟨64,12,6⟩ rationalQuadrature32 32 4 originalNodeP079R233Block1005Params positiveChordBox1005Boundary positiveChordBox1005Radius positiveChordBox1005Cells originalNodeP079R233Block1005Nodes
theorem originalNodeP079R233Block1005Columns : containedInReported originalNodeP079R233Block1005Grid.re originalNodeP079R233Box.reLo originalNodeP079R233Box.reHi=true ∧ containedInReported originalNodeP079R233Block1005Grid.im originalNodeP079R233Box.imLo originalNodeP079R233Box.imHi=true := by decide +kernel
theorem originalNodeP079R233Block1005Sound {t a : ℝ} (tl : (((559/3200):ℚ):ℝ)≤t) (tu : t≤(((7/40):ℚ):ℝ)) (al : (((3298625393473/6597069766656):ℚ):ℝ)≤a) (au : a≤(((3298628539201/6597069766656):ℚ):ℝ)) : originalNodeP079R233Box.Encloses (sourceHorizontalIntegral true t a) := by
  have tp : 0<t := lt_of_lt_of_le (by norm_num) tl
  have up : t≤7/5 := tu.trans (by norm_num)
  have bt : (positiveChordBox1005Parameters.base.base.height.toBall 64).Contains (t:ℂ) := coarsen_contains (realInterval_contains tl tu) (by decide +kernel)
  have ba : (positiveChordBox1005Parameters.base.base.abscissa.toBall 64).Contains (a:ℂ) := coarsen_contains (realInterval_contains al au) (by decide +kernel)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) tp
  rw [originalNodeP079R233Block1005Params_ok] at ps
  have result := refinedChordQuadrature_sound ⟨64,12,6⟩ rationalQuadrature32 rationalQuadrature32_exact rationalQuadrature32_nodes tp up positiveChordBox1005Parameters_valid bt ba ps 4 positiveChordBox1005Boundary (by decide +kernel) (by decide +kernel) positiveChordBox1005Radius positiveChordBox1005Cells positiveChordBox1005Cells_valid originalNodeP079R233Block1005Nodes
  exact refined_dual_output_encloses tp up (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result originalNodeP079R233Block1005Columns.1 originalNodeP079R233Block1005Columns.2

theorem originalNodeP079R233Sound : originalNodeP079R233Box.Sound := by
  intro t a t0 t1 a0 a1
  change (((559/3200):ℚ):ℝ)≤t at t0
  change t≤(((7/40):ℚ):ℝ) at t1
  change (((3298625393473/6597069766656):ℚ):ℝ)≤a at a0
  change a≤(((3298628539201/6597069766656):ℚ):ℝ) at a1
  exact originalNodeP079R233Block1005Sound t0 t1 a0 a1

def originalNodeP079Boxes : List HorizontalRectangle := [originalNodeP079R079Box, originalNodeP079R119Box, originalNodeP079R233Box]
def originalNodeP079Rows : List SignRow := [positive_079.toSignRow, positive_119.toSignRow, positive_233.toSignRow]
theorem originalNodeP079Rows_actual : ∀ r∈originalNodeP079Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have checked : ∀ b∈originalNodeP079Boxes, b.Sound := by
    intro b h
    simp only [originalNodeP079Boxes,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl
    · exact originalNodeP079R079Sound
    · exact originalNodeP079R119Sound
    · exact originalNodeP079R233Sound
  have cover : originalNodeP079Rows.all (fun r => originalNodeP079Boxes.any (fun b => b.coversRow true r))=true := by decide +kernel
  intro r hr t a ht ha
  exact actual_rows_covered_by_rectangles originalNodeP079Boxes checked (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.originalNodeP079Rows_actual
