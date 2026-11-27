import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR038Q00T := Grid.ofRats (111/125) (889/1000)
def factoredHeatR038Q00P : HeatGridParameters := ⟨⟨⟨⟨74040454249645191797674,74273424954770215858202,true⟩,⟨0,0,true⟩⟩, ⟨⟨1140399559841395639612922,1142254028822732102540946,true⟩,⟨0,0,true⟩⟩, ⟨(-1517153353953512941825413),(-1513444415990908735448545),true⟩, ⟨6056718064018549157123983,6093319978397786852277792,true⟩⟩, ⟨394321514616086006446255,418511939782595020392235,true⟩, ⟨596380750555194047770466,603080888725493320958202,true⟩, ⟨(-1441513772494900526147256),(-1428312949127709685790560),true⟩, ⟨(-2688685726981819838094682),(-2681752409040272450099618),true⟩, ⟨(-595784728893704810633539),(-594328232361670868476230),true⟩⟩
theorem factoredHeatR038Q00P_ok : factoredHeatR038Q00P.encloses (heatGridParameters factoredHeatR038Q00T (Grid.ofRats (990440969227631/1649267441664000) (992051581963631/1649267441664000))) := by decide +kernel
def factoredHeatR038Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨601404964039743823281873,601877491931006528868311,true⟩,⟨2428237734297095498443547,2430145616879638534557676,true⟩,⟨⟨708090273886708444362597,709944742868044907338248,true⟩,⟨978253959234599101110061,980108428215935564089561,true⟩⟩⟩
  | 1 => ⟨⟨9115303652724150824370,9165555662879212286843,true⟩,⟨601404964039743823281873,601877491931006528868311,true⟩,⟨⟨(-1154324591300067750173202),(-1148761184356195800274043),true⟩,⟨365254456196308631635297,370817863140180581523658,true⟩⟩⟩
  | 2 => ⟨⟨8461448051206872684,8575180996234200914,true⟩,⟨9115303652724150824370,9165555662879212286843,true⟩,⟨⟨5068984504128321041741,14341329410535757852273,true⟩,⟨(-1213523035339609837255510),(-1204250690433202400428475),true⟩⟩⟩
  | 3 => ⟨⟨481012816020333,492937501074402,true⟩,⟨8461448051206872684,8575180996234200914,true⟩,⟨⟨1138994880793477435966732,1151976163662420359678687,true⟩,⟨379986467456942842737680,392967750325885766439203,true⟩⟩⟩
  | 4 => ⟨⟨(-32684795239),36100397273,true⟩,⟨481012816020333,492937501074402,true⟩,⟨⟨(-732992295447033848277760),(-716302074615555437631834),true⟩,⟨959326370282707101509589,976016591114185512158854,true⟩⟩⟩
  | _ => ⟨⟨(-34359738011),34359738746,true⟩,⟨(-32684795239),36100397273,true⟩,⟨⟨(-703404633604108182197187),(-683005474810094284648736),true⟩,⟨(-1000638063177111667887659),(-980238904383097770335116),true⟩⟩⟩
theorem factoredHeatR038Q00F_ok : ∀ n : Fin 6, (factoredHeatR038Q00F n).encloses (FactoredFrequency.build factoredHeatR038Q00T (Grid.ofRats (990440969227631/1649267441664000) (992051581963631/1649267441664000)) n) := by decide +kernel
def factoredHeatR038Q00U : ℕ → ℚ
  | 0 => (-413373/10000)
  | 1 => (-31650847/1000000)
  | 2 => (-5186081/250000)
  | 3 => (-2604941/200000)
  | 4 => (-334341/40000)
  | 5 => (-5768667/1000000)
  | 6 => (-4275749/1000000)
  | 7 => (-350369/100000)
  | 8 => (-817893/250000)
  | 9 => (-1877799/500000)
  | 10 => (-2840951/500000)
  | 11 => (-4791237/500000)
  | 12 => (-14957061/1000000)
  | 13 => (-20619797/1000000)
  | 14 => (-11933403/500000)
  | 15 => (-22765769/1000000)
  | 16 => (-9483099/500000)
  | 17 => (-14830603/1000000)
  | 18 => (-12186743/1000000)
  | 19 => (-10943357/1000000)
  | 20 => (-32804/3125)
  | 21 => (-404447/40000)
  | 22 => (-8868153/1000000)
  | 23 => (-1151369/200000)
  | 24 => (587509/1000000)
  | 25 => (10747733/1000000)
  | 26 => (5883399/250000)
  | 27 => (33767041/1000000)
  | 28 => (32398251/1000000)
  | 29 => (6230839/500000)
  | 30 => (-8980769/500000)
  | 31 => (-39035967/1000000)
  | _ => 0
theorem factoredHeatR038Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR038Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR038Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR038Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR038Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR038Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR038Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR038Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR038Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR038Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR038Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR038Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR038Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR038Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR038Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR038Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR038Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR038Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR038Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR038Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR038Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR038Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR038Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR038Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR038Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR038Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR038Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR038Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR038Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR038Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR038Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR038Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR038Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR038Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR038Q00P factoredHeatR038Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR038Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR038Q00Point00
  · exact factoredHeatR038Q00Point01
  · exact factoredHeatR038Q00Point02
  · exact factoredHeatR038Q00Point03
  · exact factoredHeatR038Q00Point04
  · exact factoredHeatR038Q00Point05
  · exact factoredHeatR038Q00Point06
  · exact factoredHeatR038Q00Point07
  · exact factoredHeatR038Q00Point08
  · exact factoredHeatR038Q00Point09
  · exact factoredHeatR038Q00Point10
  · exact factoredHeatR038Q00Point11
  · exact factoredHeatR038Q00Point12
  · exact factoredHeatR038Q00Point13
  · exact factoredHeatR038Q00Point14
  · exact factoredHeatR038Q00Point15
  · exact factoredHeatR038Q00Point16
  · exact factoredHeatR038Q00Point17
  · exact factoredHeatR038Q00Point18
  · exact factoredHeatR038Q00Point19
  · exact factoredHeatR038Q00Point20
  · exact factoredHeatR038Q00Point21
  · exact factoredHeatR038Q00Point22
  · exact factoredHeatR038Q00Point23
  · exact factoredHeatR038Q00Point24
  · exact factoredHeatR038Q00Point25
  · exact factoredHeatR038Q00Point26
  · exact factoredHeatR038Q00Point27
  · exact factoredHeatR038Q00Point28
  · exact factoredHeatR038Q00Point29
  · exact factoredHeatR038Q00Point30
  · exact factoredHeatR038Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR038Q00Bound {t a : ℝ} (tl : ((111/125):ℝ)≤t) (tu : t≤((889/1000):ℝ)) (al : ((990440969227631/1649267441664000):ℝ)≤a) (au : a≤((992051581963631/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-326910773593293006194005652968589/40564819207303340847894502572032):ℚ):ℝ) := by
  have ts : factoredHeatR038Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (990440969227631/1649267441664000) (992051581963631/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR038Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR038Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR038Q00U (-326910773593293006194005652968589/40564819207303340847894502572032) factoredHeatR038Q00Samples (by decide +kernel)

theorem factored_original_heat_038 {t a : ℝ} (tb : RealMem derivative_038.t t) (ab : RealMem derivative_038.a a) : reportedHeatPeriod t a≤(derivative_038.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((111/125):ℝ) ((889/1000):ℝ) := by simpa [derivative_038,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((111/125):ℝ)<((889/1000):ℝ)) tB
  have aB : a∈Icc ((990440969227631/1649267441664000):ℝ) ((992051581963631/1649267441664000):ℝ) := by simpa [derivative_038,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((990440969227631/1649267441664000):ℝ)<((992051581963631/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR038Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_038] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR039Q00T := Grid.ofRats (889/1000) (89/100)
def factoredHeatR039Q00P : HeatGridParameters := ⟨⟨⟨⟨73808214295183026484226,74040454249713911275397,true⟩,⟨0,0,true⟩⟩, ⟨⟨1141038326220592880743256,1142892795201929343671282,true⟩,⟨0,0,true⟩⟩, ⟨(-1515875821195118459564742),(-1512166883232514253187879),true⟩, ⟨6048658546914535344832931,6085159059523820034397387,true⟩⟩, ⟨395062546550184760470806,419233735879849908600824,true⟩, ⟨596317900802529321011120,603006140123084861494861,true⟩, ⟨(-1439614879629419933724600),(-1426452981024434843909717),true⟩, ⟨(-2684926116782652889557354),(-2678014992278024932450498),true⟩, ⟨(-595283042952643259417453),(-593826546420609317260147),true⟩⟩
theorem factoredHeatR039Q00P_ok : factoredHeatR039Q00P.encloses (heatGridParameters factoredHeatR039Q00T (Grid.ofRats (990995740041301/1649267441664000) (992606352777301/1649267441664000))) := by decide +kernel
def factoredHeatR039Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨600932807125386402205854,601404964039812542780568,true⟩,⟨2430145616879569814992576,2432054998498182135523572,true⟩,⟨⟨707572799914292808705364,709427268895629271681010,true⟩,⟨978628449775964943637521,980482918757301406617014,true⟩⟩⟩
  | 1 => ⟨⟨9065327159432492077309,9115303652792870301564,true⟩,⟨600932807125386402205854,601404964039812542780568,true⟩,⟨⟨(-1154906527859166439499174),(-1149343120915294489600314),true⟩,⟨363428654603305092397134,368992061547177042285178,true⟩⟩⟩
  | 2 => ⟨⟨8349223617369304585,8461448119926349421,true⟩,⟨9065327159432492077309,9115303652792870301564,true⟩,⟨⟨8262675897577939380310,17535020803985376190452,true⟩,⟨(-1213493176834667545943401),(-1204220831928260109116797),true⟩⟩⟩
  | 3 => ⟨⟨469442025983555,481081535497070,true⟩,⟨8349223617369304585,8461448119926349421,true⟩,⟨⟨1137557614691990281572655,1150538897560933205284985,true⟩,⟨384220537039992854501004,397201819908935778202972,true⟩⟩⟩
  | 4 => ⟨⟨(-32748030021),36034681498,true⟩,⟨469442025983555,481081535497070,true⟩,⟨⟨(-737585726879396723150234),(-720895506047918312504459),true⟩,⟨955869471837924740040957,972559692669403150689967,true⟩⟩⟩
  | _ => ⟨⟨(-34359738031),34359738726,true⟩,⟨(-32748030021),36034681498,true⟩,⟨⟨(-697636403462025894059069),(-677237244668011996511233),true⟩,⟨(-1004650307311820789457467),(-984251148517806891905407),true⟩⟩⟩
theorem factoredHeatR039Q00F_ok : ∀ n : Fin 6, (factoredHeatR039Q00F n).encloses (FactoredFrequency.build factoredHeatR039Q00T (Grid.ofRats (990995740041301/1649267441664000) (992606352777301/1649267441664000)) n) := by decide +kernel
def factoredHeatR039Q00U : ℕ → ℚ
  | 0 => (-8231899/200000)
  | 1 => (-31609981/1000000)
  | 2 => (-20780101/1000000)
  | 3 => (-6541571/500000)
  | 4 => (-525833/62500)
  | 5 => (-290619/50000)
  | 6 => (-538419/125000)
  | 7 => (-1761649/500000)
  | 8 => (-3278097/1000000)
  | 9 => (-3748361/1000000)
  | 10 => (-1131331/200000)
  | 11 => (-2383311/250000)
  | 12 => (-744053/50000)
  | 13 => (-20526273/1000000)
  | 14 => (-23782809/1000000)
  | 15 => (-909017/40000)
  | 16 => (-18968001/1000000)
  | 17 => (-14856041/1000000)
  | 18 => (-12215619/1000000)
  | 19 => (-2192907/200000)
  | 20 => (-2626767/250000)
  | 21 => (-2527157/250000)
  | 22 => (-1106773/125000)
  | 23 => (-5734483/1000000)
  | 24 => (37741/62500)
  | 25 => (2147171/200000)
  | 26 => (23467309/1000000)
  | 27 => (105153/3125)
  | 28 => (16149513/500000)
  | 29 => (12508831/1000000)
  | 30 => (-17725621/1000000)
  | 31 => (-38751879/1000000)
  | _ => 0
theorem factoredHeatR039Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR039Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR039Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR039Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR039Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR039Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR039Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR039Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR039Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR039Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR039Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR039Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR039Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR039Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR039Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR039Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR039Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR039Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR039Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR039Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR039Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR039Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR039Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR039Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR039Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR039Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR039Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR039Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR039Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR039Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR039Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR039Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR039Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR039Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR039Q00P factoredHeatR039Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR039Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR039Q00Point00
  · exact factoredHeatR039Q00Point01
  · exact factoredHeatR039Q00Point02
  · exact factoredHeatR039Q00Point03
  · exact factoredHeatR039Q00Point04
  · exact factoredHeatR039Q00Point05
  · exact factoredHeatR039Q00Point06
  · exact factoredHeatR039Q00Point07
  · exact factoredHeatR039Q00Point08
  · exact factoredHeatR039Q00Point09
  · exact factoredHeatR039Q00Point10
  · exact factoredHeatR039Q00Point11
  · exact factoredHeatR039Q00Point12
  · exact factoredHeatR039Q00Point13
  · exact factoredHeatR039Q00Point14
  · exact factoredHeatR039Q00Point15
  · exact factoredHeatR039Q00Point16
  · exact factoredHeatR039Q00Point17
  · exact factoredHeatR039Q00Point18
  · exact factoredHeatR039Q00Point19
  · exact factoredHeatR039Q00Point20
  · exact factoredHeatR039Q00Point21
  · exact factoredHeatR039Q00Point22
  · exact factoredHeatR039Q00Point23
  · exact factoredHeatR039Q00Point24
  · exact factoredHeatR039Q00Point25
  · exact factoredHeatR039Q00Point26
  · exact factoredHeatR039Q00Point27
  · exact factoredHeatR039Q00Point28
  · exact factoredHeatR039Q00Point29
  · exact factoredHeatR039Q00Point30
  · exact factoredHeatR039Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR039Q00Bound {t a : ℝ} (tl : ((889/1000):ℝ)≤t) (tu : t≤((89/100):ℝ)) (al : ((990995740041301/1649267441664000):ℝ)≤a) (au : a≤((992606352777301/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2615461434307564949674700234503219/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR039Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (990995740041301/1649267441664000) (992606352777301/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR039Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR039Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR039Q00U (-2615461434307564949674700234503219/324518553658426726783156020576256) factoredHeatR039Q00Samples (by decide +kernel)

theorem factored_original_heat_039 {t a : ℝ} (tb : RealMem derivative_039.t t) (ab : RealMem derivative_039.a a) : reportedHeatPeriod t a≤(derivative_039.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((889/1000):ℝ) ((89/100):ℝ) := by simpa [derivative_039,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((889/1000):ℝ)<((89/100):ℝ)) tB
  have aB : a∈Icc ((990995740041301/1649267441664000):ℝ) ((992606352777301/1649267441664000):ℝ) := by simpa [derivative_039,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((990995740041301/1649267441664000):ℝ)<((992606352777301/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR039Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_039] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR040Q00T := Grid.ofRats (89/100) (891/1000)
def factoredHeatR040Q00P : HeatGridParameters := ⟨⟨⟨⟨73576702799196638580699,73808214295251745961947,true⟩,⟨0,0,true⟩⟩, ⟨⟨1141678242444119158549250,1143532711425455621477279,true⟩,⟨0,0,true⟩⟩, ⟨(-1514595988748065903952749),(-1510887050785461697575889),true⟩, ⟨6040611703380288467246173,6077011153006981785040060,true⟩⟩, ⟨395804235045998498678974,419956290543821173811595,true⟩, ⟨596251829505940161480898,602928189348756551724110,true⟩, ⟨(-1437723608747338940199856),(-1424600496177163244779392),true⟩, ⟨(-2681173145484737392646326),(-2674284138198526338738120),true⟩, ⟨(-594780453925957489825058),(-593323957393923547667755),true⟩⟩
theorem factoredHeatR040Q00P_ok : factoredHeatR040Q00P.encloses (heatGridParameters factoredHeatR040Q00T (Grid.ofRats (198310301899751/329853488332800) (198632424446951/329853488332800))) := by decide +kernel
def factoredHeatR040Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨600461020896615408674108,600932807125455121704323,true⟩,⟨2432054998498113415959487,2433965880330597658058788,true⟩,⟨⟨707054196102614060085682,708908665083950523061102,true⟩,⟨979003340226741189279288,980857809208077652258504,true⟩⟩⟩
  | 1 => ⟨⟨9015624672359043665204,9065327159501211554499,true⟩,⟨600461020896615408674108,600932807125455121704323,true⟩,⟨⟨(-1155486609286499689493667),(-1149923202342627739594296),true⟩,⟨361598643750496857185667,367162050694368807074176,true⟩⟩⟩
  | 2 => ⟨⟨8238487619485346587,8349223686088781323,true⟩,⟨9015624672359043665204,9065327159501211554499,true⟩,⟨⟨11462025975547860284199,20734370881955297094345,true⟩,⟨(-1213454804564014400554772),(-1204182459657606963728211),true⟩⟩⟩
  | 3 => ⟨⟨458149552063827,469510745460292,true⟩,⟨8238487619485346587,8349223686088781323,true⟩,⟨⟨1136102068719767111634342,1149083351588710035347286,true⟩,⟨388456869044193384786756,401438151913136308489412,true⟩⟩⟩
  | 4 => ⟨⟨(-32808877475),35971446716,true⟩,⟨458149552063827,469510745460292,true⟩,⟨⟨(-742170891609592744571206),(-725480670778114333925775),true⟩,⟨952384487434838888068974,969074708266317298717526,true⟩⟩⟩
  | _ => ⟨⟨(-34359738049),34359738706,true⟩,⟨(-32808877475),35971446716,true⟩,⟨⟨(-691834505183901145644164),(-671435346389887248095818),true⟩,⟨(-1008636089786324672494662),(-988236930992310774941949),true⟩⟩⟩
theorem factoredHeatR040Q00F_ok : ∀ n : Fin 6, (factoredHeatR040Q00F n).encloses (FactoredFrequency.build factoredHeatR040Q00T (Grid.ofRats (198310301899751/329853488332800) (198632424446951/329853488332800)) n) := by decide +kernel
def factoredHeatR040Q00U : ℕ → ℚ
  | 0 => (-40981679/1000000)
  | 1 => (-631363/20000)
  | 2 => (-20814859/1000000)
  | 3 => (-6570421/500000)
  | 4 => (-8467657/1000000)
  | 5 => (-5855779/1000000)
  | 6 => (-4338733/1000000)
  | 7 => (-3542749/1000000)
  | 8 => (-328453/100000)
  | 9 => (-3741107/1000000)
  | 10 => (-5631487/1000000)
  | 11 => (-9484219/1000000)
  | 12 => (-3701347/250000)
  | 13 => (-10216549/500000)
  | 14 => (-23698953/1000000)
  | 15 => (-22684807/1000000)
  | 16 => (-9484649/500000)
  | 17 => (-14880981/1000000)
  | 18 => (-12244109/1000000)
  | 19 => (-2746359/250000)
  | 20 => (-10516651/1000000)
  | 21 => (-2526483/250000)
  | 22 => (-4420067/500000)
  | 23 => (-5712131/1000000)
  | 24 => (124023/200000)
  | 25 => (10723907/1000000)
  | 26 => (2925147/125000)
  | 27 => (33531371/1000000)
  | 28 => (32200221/1000000)
  | 29 => (6277673/500000)
  | 30 => (-8745769/500000)
  | 31 => (-38469247/1000000)
  | _ => 0
theorem factoredHeatR040Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR040Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR040Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR040Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR040Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR040Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR040Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR040Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR040Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR040Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR040Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR040Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR040Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR040Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR040Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR040Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR040Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR040Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR040Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR040Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR040Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR040Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR040Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR040Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR040Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR040Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR040Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR040Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR040Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR040Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR040Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR040Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR040Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR040Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR040Q00P factoredHeatR040Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR040Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR040Q00Point00
  · exact factoredHeatR040Q00Point01
  · exact factoredHeatR040Q00Point02
  · exact factoredHeatR040Q00Point03
  · exact factoredHeatR040Q00Point04
  · exact factoredHeatR040Q00Point05
  · exact factoredHeatR040Q00Point06
  · exact factoredHeatR040Q00Point07
  · exact factoredHeatR040Q00Point08
  · exact factoredHeatR040Q00Point09
  · exact factoredHeatR040Q00Point10
  · exact factoredHeatR040Q00Point11
  · exact factoredHeatR040Q00Point12
  · exact factoredHeatR040Q00Point13
  · exact factoredHeatR040Q00Point14
  · exact factoredHeatR040Q00Point15
  · exact factoredHeatR040Q00Point16
  · exact factoredHeatR040Q00Point17
  · exact factoredHeatR040Q00Point18
  · exact factoredHeatR040Q00Point19
  · exact factoredHeatR040Q00Point20
  · exact factoredHeatR040Q00Point21
  · exact factoredHeatR040Q00Point22
  · exact factoredHeatR040Q00Point23
  · exact factoredHeatR040Q00Point24
  · exact factoredHeatR040Q00Point25
  · exact factoredHeatR040Q00Point26
  · exact factoredHeatR040Q00Point27
  · exact factoredHeatR040Q00Point28
  · exact factoredHeatR040Q00Point29
  · exact factoredHeatR040Q00Point30
  · exact factoredHeatR040Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR040Q00Bound {t a : ℝ} (tl : ((89/100):ℝ)≤t) (tu : t≤((891/1000):ℝ)) (al : ((198310301899751/329853488332800):ℝ)≤a) (au : a≤((198632424446951/329853488332800):ℝ)) : reportedHeatPeriod t a≤(((-2615271174875487743074392738984435/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR040Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (198310301899751/329853488332800) (198632424446951/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR040Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR040Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR040Q00U (-2615271174875487743074392738984435/324518553658426726783156020576256) factoredHeatR040Q00Samples (by decide +kernel)

theorem factored_original_heat_040 {t a : ℝ} (tb : RealMem derivative_040.t t) (ab : RealMem derivative_040.a a) : reportedHeatPeriod t a≤(derivative_040.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((89/100):ℝ) ((891/1000):ℝ) := by simpa [derivative_040,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((89/100):ℝ)<((891/1000):ℝ)) tB
  have aB : a∈Icc ((198310301899751/329853488332800):ℝ) ((198632424446951/329853488332800):ℝ) := by simpa [derivative_040,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((198310301899751/329853488332800):ℝ)<((198632424446951/329853488332800):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR040Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_040] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR041Q00T := Grid.ofRats (891/1000) (223/250)
def factoredHeatR041Q00P : HeatGridParameters := ⟨⟨⟨⟨73345917476757269119390,73576702799265358058419,true⟩,⟨0,0,true⟩⟩, ⟨⟨1142319309615666097312222,1144173778597002560240252,true⟩,⟨0,0,true⟩⟩, ⟨(-1513313854404972026426802),(-1509604916442367820049946),true⟩, ⟨6032577528041327140973312,6068876252333301210688206,true⟩⟩, ⟨396546586946557790279970,420679610414450343850539,true⟩, ⟨596182541168327668744448,602847040886399029884643,true⟩, ⟨(-1435839939309582494028771),(-1422755474545620444511718),true⟩, ⟨(-2677426821515974911335522),(-2670559855545027142286490),true⟩, ⟨(-594276960946810127188663),(-592820464414776185031363),true⟩⟩
theorem factoredHeatR041Q00P_ok : factoredHeatR041Q00P.encloses (heatGridParameters factoredHeatR041Q00T (Grid.ofRats (992108278558553/1649267441664000) (993718891294553/1649267441664000))) := by decide +kernel
def factoredHeatR041Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨599989605062409362734922,600461020896684128172389,true⟩,⟨2433965880330528938494606,2435878263555613146703258,true⟩,⟨⟨706534460632298721186516,708388929613635184162093,true⟩,⟨979378629647989808626468,981233098629326271605836,true⟩⟩⟩
  | 1 => ⟨⟨8966194689209373288206,9015624672427763142388,true⟩,⟨599989605062409362734922,600461020896684128172389,true⟩,⟨⟨(-1156064819447071426135582),(-1150501412503199476236182),true⟩,⟨359764420128338078340277,365327827072210028228782,true⟩⟩⟩
  | 2 => ⟨⟨8129220316385342127,8238487688204823325,true⟩,⟨8966194689209373288206,9015624672427763142388,true⟩,⟨⟨14667017297890319085196,23939362204297755895340,true⟩,⟨(-1213407873063511759188121),(-1204135528157104322361606),true⟩⟩⟩
  | 3 => ⟨⟨447128699829674,458218271540564,true⟩,⟨8129220316385342127,8238487688204823325,true⟩,⟨⟨1134628175694327222201478,1147609458563270145914022,true⟩,⟨392695383528169515147738,405676666397112438850085,true⟩⟩⟩
  | 4 => ⟨⟨(-32867427731),35910599262,true⟩,⟨447128699829674,458218271540564,true⟩,⟨⟨(-746747603946215123242182),(-730057383114736712596134),true⟩,⟨948871372350243250774011,965561593181721661423062,true⟩⟩⟩
  | _ => ⟨⟨(-34359738066),34359738688,true⟩,⟨(-32867427731),35910599262,true⟩,⟨⟨(-685999000301361250670187),(-665599841507347353122008),true⟩,⟨(-1012595100155276444743401),(-992195941361262547190723),true⟩⟩⟩
theorem factoredHeatR041Q00F_ok : ∀ n : Fin 6, (factoredHeatR041Q00F n).encloses (FactoredFrequency.build factoredHeatR041Q00T (Grid.ofRats (992108278558553/1649267441664000) (993718891294553/1649267441664000)) n) := by decide +kernel
def factoredHeatR041Q00U : ℕ → ℚ
  | 0 => (-40803861/1000000)
  | 1 => (-6305073/200000)
  | 2 => (-10424301/500000)
  | 3 => (-824863/62500)
  | 4 => (-8521509/1000000)
  | 5 => (-2949431/500000)
  | 6 => (-4369893/1000000)
  | 7 => (-3562043/1000000)
  | 8 => (-411359/125000)
  | 9 => (-933459/250000)
  | 10 => (-5606399/1000000)
  | 11 => (-47177/5000)
  | 12 => (-3682511/250000)
  | 13 => (-2034027/100000)
  | 14 => (-23615239/1000000)
  | 15 => (-22643921/1000000)
  | 16 => (-4742523/250000)
  | 17 => (-14905423/1000000)
  | 18 => (-1534027/125000)
  | 19 => (-11006061/1000000)
  | 20 => (-2631507/250000)
  | 21 => (-1010309/100000)
  | 22 => (-4413003/500000)
  | 23 => (-5689789/1000000)
  | 24 => (636287/1000000)
  | 25 => (10711889/1000000)
  | 26 => (5833799/250000)
  | 27 => (33414273/1000000)
  | 28 => (4012729/125000)
  | 29 => (12601229/1000000)
  | 30 => (-8629637/500000)
  | 31 => (-7637613/200000)
  | _ => 0
theorem factoredHeatR041Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR041Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR041Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR041Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR041Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR041Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR041Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR041Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR041Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR041Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR041Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR041Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR041Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR041Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR041Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR041Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR041Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR041Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR041Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR041Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR041Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR041Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR041Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR041Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR041Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR041Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR041Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR041Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR041Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR041Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR041Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR041Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR041Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR041Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR041Q00P factoredHeatR041Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR041Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR041Q00Point00
  · exact factoredHeatR041Q00Point01
  · exact factoredHeatR041Q00Point02
  · exact factoredHeatR041Q00Point03
  · exact factoredHeatR041Q00Point04
  · exact factoredHeatR041Q00Point05
  · exact factoredHeatR041Q00Point06
  · exact factoredHeatR041Q00Point07
  · exact factoredHeatR041Q00Point08
  · exact factoredHeatR041Q00Point09
  · exact factoredHeatR041Q00Point10
  · exact factoredHeatR041Q00Point11
  · exact factoredHeatR041Q00Point12
  · exact factoredHeatR041Q00Point13
  · exact factoredHeatR041Q00Point14
  · exact factoredHeatR041Q00Point15
  · exact factoredHeatR041Q00Point16
  · exact factoredHeatR041Q00Point17
  · exact factoredHeatR041Q00Point18
  · exact factoredHeatR041Q00Point19
  · exact factoredHeatR041Q00Point20
  · exact factoredHeatR041Q00Point21
  · exact factoredHeatR041Q00Point22
  · exact factoredHeatR041Q00Point23
  · exact factoredHeatR041Q00Point24
  · exact factoredHeatR041Q00Point25
  · exact factoredHeatR041Q00Point26
  · exact factoredHeatR041Q00Point27
  · exact factoredHeatR041Q00Point28
  · exact factoredHeatR041Q00Point29
  · exact factoredHeatR041Q00Point30
  · exact factoredHeatR041Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR041Q00Bound {t a : ℝ} (tl : ((891/1000):ℝ)≤t) (tu : t≤((223/250):ℝ)) (al : ((992108278558553/1649267441664000):ℝ)≤a) (au : a≤((993718891294553/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2614742336270732427836362345811445/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR041Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (992108278558553/1649267441664000) (993718891294553/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR041Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR041Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR041Q00U (-2614742336270732427836362345811445/324518553658426726783156020576256) factoredHeatR041Q00Samples (by decide +kernel)

theorem factored_original_heat_041 {t a : ℝ} (tb : RealMem derivative_041.t t) (ab : RealMem derivative_041.a a) : reportedHeatPeriod t a≤(derivative_041.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((891/1000):ℝ) ((223/250):ℝ) := by simpa [derivative_041,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((891/1000):ℝ)<((223/250):ℝ)) tB
  have aB : a∈Icc ((992108278558553/1649267441664000):ℝ) ((993718891294553/1649267441664000):ℝ) := by simpa [derivative_041,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((992108278558553/1649267441664000):ℝ)<((993718891294553/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR041Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_041] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR042Q00T := Grid.ofRats (223/250) (893/1000)
def factoredHeatR042Q00P : HeatGridParameters := ⟨⟨⟨⟨73115856050103210662890,73345917476825988597103,true⟩,⟨0,0,true⟩⟩, ⟨⟨1142961528871116327021684,1144815997852452789949716,true⟩,⟨0,0,true⟩⟩, ⟨(-1512029415894071567007874),(-1508320477931467360631023),true⟩, ⟨6024556015273723800856610,6060754350741631908632577,true⟩⟩, ⟨397289609167291538111139,421403702209104347632030,true⟩, ⟨596110040253292314085609,602762699180384814601807,true⟩, ⟨(-1433963850765332475297703),(-1420917896076146010226632),true⟩, ⟨(-2673687153117644081681080),(-2666842152872370818281888),true⟩, ⟨(-593772563123081040079439),(-592316066591047097922143),true⟩⟩
theorem factoredHeatR042Q00P_ok : factoredHeatR042Q00P.encloses (heatGridParameters factoredHeatR042Q00T (Grid.ofRats (992666048207213/1649267441664000) (994276660943213/1649267441664000))) := by decide +kernel
def factoredHeatR042Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨599518559331975262440594,599989605062478082233561,true⟩,⟨2435878263555544427137494,2437792149352882780482341,true⟩,⟨⟨706013591656192061939597,707868060637528524915228,true⟩,⟨979754317113978590571664,981608786095315053551067,true⟩⟩⟩
  | 1 => ⟨⟨8917035715925681289558,8966194689278092765392,true⟩,⟨599518559331975262440594,599989605062478082233561,true⟩,⟨⟨(-1156641142178001079916867),(-1151077735234129130017589),true⟩,⟨357925980172074169237726,363489387115946119126078,true⟩⟩⟩
  | 2 => ⟨⟨8021402228727346114,8129220385104818865,true⟩,⟨8917035715925681289558,8966194689278092765392,true⟩,⟨⟨17877632342030597818904,27149977248438034629341,true⟩,⟨(-1213352336788133510251805),(-1204079991881726073425041),true⟩⟩⟩
  | 3 => ⟨⟨436372935873042,447197419306411,true⟩,⟨8021402228727346114,8129220385104818865,true⟩,⟨⟨1133135868530787491539613,1146117151399730415252335,true⟩,⟨396936000119239581103143,409917282988182504805736,true⟩⟩⟩
  | 4 => ⟨⟨(-32923767517),35852049006,true⟩,⟨436372935873042,447197419306411,true⟩,⟨⟨(-751315677406167261717497),(-734625456574688851071358),true⟩,⟨945330082675087066661710,962020303506565477310746,true⟩⟩⟩
  | _ => ⟨⟨(-34359738083),34359738671,true⟩,⟨(-32923767517),35852049006,true⟩,⟨⟨(-680129952584464180368415),(-659730793790450282819996),true⟩,⟨(-1016527027304405131457281),(-996127868510391233904229),true⟩⟩⟩
theorem factoredHeatR042Q00F_ok : ∀ n : Fin 6, (factoredHeatR042Q00F n).encloses (FactoredFrequency.build factoredHeatR042Q00T (Grid.ofRats (992666048207213/1649267441664000) (994276660943213/1649267441664000)) n) := by decide +kernel
def factoredHeatR042Q00U : ℕ → ℚ
  | 0 => (-40626049/1000000)
  | 1 => (-15740819/500000)
  | 2 => (-10440669/500000)
  | 3 => (-331351/25000)
  | 4 => (-4287443/500000)
  | 5 => (-594163/100000)
  | 6 => (-68763/15625)
  | 7 => (-3581179/1000000)
  | 8 => (-1648561/500000)
  | 9 => (-931637/250000)
  | 10 => (-5581391/1000000)
  | 11 => (-293337/31250)
  | 12 => (-7327513/500000)
  | 13 => (-2024779/100000)
  | 14 => (-23531667/1000000)
  | 15 => (-1412673/62500)
  | 16 => (-9485193/500000)
  | 17 => (-14929371/1000000)
  | 18 => (-614997/50000)
  | 19 => (-1102641/100000)
  | 20 => (-10535201/1000000)
  | 21 => (-10100101/1000000)
  | 22 => (-8811799/1000000)
  | 23 => (-2833729/500000)
  | 24 => (65237/100000)
  | 25 => (5349901/500000)
  | 26 => (23269371/1000000)
  | 27 => (33297661/1000000)
  | 28 => (2000241/62500)
  | 29 => (3161621/250000)
  | 30 => (-8514409/500000)
  | 31 => (-37908329/1000000)
  | _ => 0
theorem factoredHeatR042Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR042Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR042Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR042Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR042Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR042Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR042Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR042Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR042Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR042Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR042Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR042Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR042Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR042Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR042Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR042Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR042Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR042Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR042Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR042Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR042Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR042Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR042Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR042Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR042Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR042Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR042Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR042Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR042Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR042Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR042Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR042Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR042Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR042Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR042Q00P factoredHeatR042Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR042Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR042Q00Point00
  · exact factoredHeatR042Q00Point01
  · exact factoredHeatR042Q00Point02
  · exact factoredHeatR042Q00Point03
  · exact factoredHeatR042Q00Point04
  · exact factoredHeatR042Q00Point05
  · exact factoredHeatR042Q00Point06
  · exact factoredHeatR042Q00Point07
  · exact factoredHeatR042Q00Point08
  · exact factoredHeatR042Q00Point09
  · exact factoredHeatR042Q00Point10
  · exact factoredHeatR042Q00Point11
  · exact factoredHeatR042Q00Point12
  · exact factoredHeatR042Q00Point13
  · exact factoredHeatR042Q00Point14
  · exact factoredHeatR042Q00Point15
  · exact factoredHeatR042Q00Point16
  · exact factoredHeatR042Q00Point17
  · exact factoredHeatR042Q00Point18
  · exact factoredHeatR042Q00Point19
  · exact factoredHeatR042Q00Point20
  · exact factoredHeatR042Q00Point21
  · exact factoredHeatR042Q00Point22
  · exact factoredHeatR042Q00Point23
  · exact factoredHeatR042Q00Point24
  · exact factoredHeatR042Q00Point25
  · exact factoredHeatR042Q00Point26
  · exact factoredHeatR042Q00Point27
  · exact factoredHeatR042Q00Point28
  · exact factoredHeatR042Q00Point29
  · exact factoredHeatR042Q00Point30
  · exact factoredHeatR042Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR042Q00Bound {t a : ℝ} (tl : ((223/250):ℝ)≤t) (tu : t≤((893/1000):ℝ)) (al : ((992666048207213/1649267441664000):ℝ)≤a) (au : a≤((994276660943213/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-163368509475243979813724145593153/20282409603651670423947251286016):ℚ):ℝ) := by
  have ts : factoredHeatR042Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (992666048207213/1649267441664000) (994276660943213/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR042Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR042Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR042Q00U (-163368509475243979813724145593153/20282409603651670423947251286016) factoredHeatR042Q00Samples (by decide +kernel)

theorem factored_original_heat_042 {t a : ℝ} (tb : RealMem derivative_042.t t) (ab : RealMem derivative_042.a a) : reportedHeatPeriod t a≤(derivative_042.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((223/250):ℝ) ((893/1000):ℝ) := by simpa [derivative_042,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((223/250):ℝ)<((893/1000):ℝ)) tB
  have aB : a∈Icc ((992666048207213/1649267441664000):ℝ) ((994276660943213/1649267441664000):ℝ) := by simpa [derivative_042,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((992666048207213/1649267441664000):ℝ)<((994276660943213/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR042Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_042] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_038
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_039
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_040
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_041
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_042
