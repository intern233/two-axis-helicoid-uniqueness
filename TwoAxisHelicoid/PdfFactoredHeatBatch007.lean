import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR007Q00T := Grid.ofRats (857/1000) (429/500)
def factoredHeatR007Q00P : HeatGridParameters := ⟨⟨⟨⟨81614014630037440433225,81870815790006197613298,true⟩,⟨0,0,true⟩⟩, ⟨⟨1121162511120787622651790,1123016980102124085579753,true⟩,⟨0,0,true⟩⟩, ⟨(-1555627451394728975747800),(-1551918513432124769370810),true⟩, ⟨6312871696196453328143262,6352791481033872462745828,true⟩⟩, ⟨371632265408994429189702,396486149640857391096868,true⟩, ⟨596705029636460735346141,603786795173491022746230,true⟩, ⟨(-1504273363417052496131981),(-1489794240200478388104901),true⟩, ⟨(-2808471415248752034177575),(-2800810488497071185827858),true⟩, ⟨(-610893471628057579893968),(-609436975096023637736563),true⟩⟩
theorem factoredHeatR007Q00P_ok : factoredHeatR007Q00P.encloses (heatGridParameters factoredHeatR007Q00T (Grid.ofRats (324577841919019/549755813888000) (325114712831019/549755813888000))) := by decide +kernel
def factoredHeatR007Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨616227286903288874835525,616711460792479931561890,true⟩,⟨2369830512721330056658406,2371692504360345944111368,true⟩,⟨⟨723581087957606399993763,725435556938942862969145,true⟩,⟨966848218821767169166338,968702687803103632145105,true⟩⟩⟩
  | 1 => ⟨⟨10809075686162185322773,10868665339093692756794,true⟩,⟨616227286903288874835525,616711460792479931561890,true⟩,⟨⟨(-1135450261416848084586548),(-1129886854472976134687799),true⟩,⟨419786131524879887628547,425349538468751837517523,true⟩⟩⟩
  | 2 => ⟨⟨12799743823077386787,12971789110320779548,true⟩,⟨10809075686162185322773,10868665339093692756794,true⟩,⟨⟨(-91042417911965003043423),(-81770073005557566232731),true⟩,⟨(-1210470156912351068530057),(-1201197812005943631703957),true⟩⟩⟩
  | 3 => ⟨⟨1023209361055327,1048497108815136,true⟩,⟨12799743823077386787,12971789110320779548,true⟩,⟨⟨1174855885281939686652796,1187837168150882610360750,true⟩,⟨250262199145675963984043,263243482014618887679273,true⟩⟩⟩
  | 4 => ⟨⟨(-28837413065),40098730065,true⟩,⟨1023209361055327,1048497108815136,true⟩,⟨⟨(-587464244870235795126262),(-570774024038757384482451),true⟩,⟨1052844158960641936665733,1069534379792120347316176,true⟩⟩⟩
  | _ => ⟨⟨(-34359736356),34359740496,true⟩,⟨(-28837413065),40098730065,true⟩,⟨⟨(-865292569783016901943258),(-844893410989003004395875),true⟩,⟨(-864785803907801417035033),(-844386645113787519487660),true⟩⟩⟩
theorem factoredHeatR007Q00F_ok : ∀ n : Fin 6, (factoredHeatR007Q00F n).encloses (FactoredFrequency.build factoredHeatR007Q00T (Grid.ofRats (324577841919019/549755813888000) (325114712831019/549755813888000)) n) := by decide +kernel
def factoredHeatR007Q00U : ℕ → ℚ
  | 0 => (-9334871/200000)
  | 1 => (-505318/15625)
  | 2 => (-9548047/500000)
  | 3 => (-10839881/1000000)
  | 4 => (-6425167/1000000)
  | 5 => (-4257963/1000000)
  | 6 => (-1592639/500000)
  | 7 => (-704223/250000)
  | 8 => (-3008889/1000000)
  | 9 => (-3966139/1000000)
  | 10 => (-6501983/1000000)
  | 11 => (-224259/20000)
  | 12 => (-17483887/1000000)
  | 13 => (-23698181/1000000)
  | 14 => (-26503413/1000000)
  | 15 => (-2385963/100000)
  | 16 => (-9318597/500000)
  | 17 => (-13783207/1000000)
  | 18 => (-5548873/500000)
  | 19 => (-2537157/250000)
  | 20 => (-10087823/1000000)
  | 21 => (-10109187/1000000)
  | 22 => (-9256657/1000000)
  | 23 => (-6433057/1000000)
  | 24 => (2331/62500)
  | 25 => (1384691/125000)
  | 26 => (25665203/1000000)
  | 27 => (1507511/40000)
  | 28 => (17850961/500000)
  | 29 => (10654999/1000000)
  | 30 => (-410333/15625)
  | 31 => (-48539449/1000000)
  | _ => 0
theorem factoredHeatR007Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR007Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR007Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR007Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR007Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR007Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR007Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR007Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR007Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR007Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR007Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR007Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR007Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR007Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR007Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR007Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR007Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR007Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR007Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR007Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR007Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR007Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR007Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR007Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR007Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR007Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR007Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR007Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR007Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR007Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR007Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR007Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR007Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR007Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR007Q00P factoredHeatR007Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR007Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR007Q00Point00
  · exact factoredHeatR007Q00Point01
  · exact factoredHeatR007Q00Point02
  · exact factoredHeatR007Q00Point03
  · exact factoredHeatR007Q00Point04
  · exact factoredHeatR007Q00Point05
  · exact factoredHeatR007Q00Point06
  · exact factoredHeatR007Q00Point07
  · exact factoredHeatR007Q00Point08
  · exact factoredHeatR007Q00Point09
  · exact factoredHeatR007Q00Point10
  · exact factoredHeatR007Q00Point11
  · exact factoredHeatR007Q00Point12
  · exact factoredHeatR007Q00Point13
  · exact factoredHeatR007Q00Point14
  · exact factoredHeatR007Q00Point15
  · exact factoredHeatR007Q00Point16
  · exact factoredHeatR007Q00Point17
  · exact factoredHeatR007Q00Point18
  · exact factoredHeatR007Q00Point19
  · exact factoredHeatR007Q00Point20
  · exact factoredHeatR007Q00Point21
  · exact factoredHeatR007Q00Point22
  · exact factoredHeatR007Q00Point23
  · exact factoredHeatR007Q00Point24
  · exact factoredHeatR007Q00Point25
  · exact factoredHeatR007Q00Point26
  · exact factoredHeatR007Q00Point27
  · exact factoredHeatR007Q00Point28
  · exact factoredHeatR007Q00Point29
  · exact factoredHeatR007Q00Point30
  · exact factoredHeatR007Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR007Q00Bound {t a : ℝ} (tl : ((857/1000):ℝ)≤t) (tu : t≤((429/500):ℝ)) (al : ((324577841919019/549755813888000):ℝ)≤a) (au : a≤((325114712831019/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-689869959197832365639239739664175/81129638414606681695789005144064):ℚ):ℝ) := by
  have ts : factoredHeatR007Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (324577841919019/549755813888000) (325114712831019/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR007Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR007Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR007Q00U (-689869959197832365639239739664175/81129638414606681695789005144064) factoredHeatR007Q00Samples (by decide +kernel)

theorem factored_original_heat_007 {t a : ℝ} (tb : RealMem derivative_007.t t) (ab : RealMem derivative_007.a a) : reportedHeatPeriod t a≤(derivative_007.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((857/1000):ℝ) ((429/500):ℝ) := by simpa [derivative_007,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((857/1000):ℝ)<((429/500):ℝ)) tB
  have aB : a∈Icc ((324577841919019/549755813888000):ℝ) ((325114712831019/549755813888000):ℝ) := by simpa [derivative_007,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((324577841919019/549755813888000):ℝ)<((325114712831019/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR007Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_007] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR008Q00T := Grid.ofRats (429/500) (859/1000)
def factoredHeatR008Q00P : HeatGridParameters := ⟨⟨⟨⟨81358018968837882058582,81614014630106159911020,true⟩,⟨0,0,true⟩⟩, ⟨⟨1121766130444808340498597,1123620599426144803426562,true⟩,⟨0,0,true⟩⟩, ⟨(-1554420212746687540054182),(-1550711274784083333677195),true⟩, ⟨6304417456473149974536566,6344224753226112831778493,true⟩⟩, ⟨372356437570309101712694,397187170459042729798078,true⟩, ⟨596744377179231495005909,603813499824387322321625,true⟩, ⟨(-1502127846745115687178423),(-1487692208035698804591547),true⟩, ⟨(-2804511267377929807486678),(-2796875063647817065610551),true⟩, ⟨(-610419390119580498843159),(-608962893587546556685756),true⟩⟩
theorem factoredHeatR008Q00P_ok : factoredHeatR008Q00P.encloses (heatGridParameters factoredHeatR008Q00T (Grid.ofRats (324752590410507/549755813888000) (325289461322507/549755813888000))) := by decide +kernel
def factoredHeatR008Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨615743493134157508141935,616227286903357594334488,true⟩,⟨2371692504360277224549432,2373555958978542006838641,true⟩,⟨⟨723097785251682880215219,724952254233019343190496,true⟩,⟨967209846773132448237027,969064315754468911215724,true⟩⟩⟩
  | 1 => ⟨⟨10749812745606523652100,10809075686230904800047,true⟩,⟨615743493134157508141935,616227286903357594334488,true⟩,⟨⟨(-1136081957634225545219945),(-1130518550690353595320623),true⟩,⟨418089026380583918441268,423652433324455868330773,true⟩⟩⟩
  | 2 => ⟨⟨12629980445326829859,12799743891796863524,true⟩,⟨10749812745606523652100,10809075686230904800047,true⟩,⟨⟨(-88031773953206855593248),(-78759429046799418782073),true⟩,⟨(-1210682113112744097225132),(-1201409768206336660398504),true⟩⟩⟩
  | 3 => ⟨⟨998596934569125,1023278080532064,true⟩,⟨12629980445326829859,12799743891796863524,true⟩,⟨⟨1173951290740066298749172,1186932573609009222457228,true⟩,⟨254389564972505515433660,267370847841448439129063,true⟩⟩⟩
  | 4 => ⟨⟨(-29045899567),39882063672,true⟩,⟨998596934569125,1023278080532064,true⟩,⟨⟨(-592227068856665122966145),(-575536848025186712321126),true⟩,⟨1050231054032569057146637,1066921274864047467798191,true⟩⟩⟩
  | _ => ⟨⟨(-34359736466),34359740381,true⟩,⟨(-29045899567),39882063672,true⟩,⟨⟨(-860586031583406803275033),(-840186872789392905726843),true⟩,⟨(-869469338709372597398884),(-849070179915358699850572),true⟩⟩⟩
theorem factoredHeatR008Q00F_ok : ∀ n : Fin 6, (factoredHeatR008Q00F n).encloses (FactoredFrequency.build factoredHeatR008Q00T (Grid.ofRats (324752590410507/549755813888000) (325289461322507/549755813888000)) n) := by decide +kernel
def factoredHeatR008Q00U : ℕ → ℚ
  | 0 => (-5813309/125000)
  | 1 => (-8084613/250000)
  | 2 => (-3833323/200000)
  | 3 => (-5460939/500000)
  | 4 => (-6494529/1000000)
  | 5 => (-4311441/1000000)
  | 6 => (-3223793/1000000)
  | 7 => (-568289/200000)
  | 8 => (-1509609/500000)
  | 9 => (-1979853/500000)
  | 10 => (-3237147/500000)
  | 11 => (-697317/62500)
  | 12 => (-17396951/1000000)
  | 13 => (-23593249/1000000)
  | 14 => (-26420911/1000000)
  | 15 => (-23829691/1000000)
  | 16 => (-18656663/1000000)
  | 17 => (-216017/15625)
  | 18 => (-2784693/250000)
  | 19 => (-2544607/250000)
  | 20 => (-2020893/200000)
  | 21 => (-2022359/200000)
  | 22 => (-1155699/125000)
  | 23 => (-6411857/1000000)
  | 24 => (56373/1000000)
  | 25 => (553409/50000)
  | 26 => (25594143/1000000)
  | 27 => (3755299/100000)
  | 28 => (35587903/1000000)
  | 29 => (1072463/100000)
  | 30 => (-6490433/250000)
  | 31 => (-48212769/1000000)
  | _ => 0
theorem factoredHeatR008Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR008Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR008Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR008Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR008Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR008Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR008Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR008Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR008Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR008Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR008Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR008Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR008Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR008Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR008Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR008Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR008Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR008Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR008Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR008Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR008Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR008Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR008Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR008Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR008Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR008Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR008Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR008Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR008Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR008Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR008Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR008Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR008Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR008Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR008Q00P factoredHeatR008Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR008Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR008Q00Point00
  · exact factoredHeatR008Q00Point01
  · exact factoredHeatR008Q00Point02
  · exact factoredHeatR008Q00Point03
  · exact factoredHeatR008Q00Point04
  · exact factoredHeatR008Q00Point05
  · exact factoredHeatR008Q00Point06
  · exact factoredHeatR008Q00Point07
  · exact factoredHeatR008Q00Point08
  · exact factoredHeatR008Q00Point09
  · exact factoredHeatR008Q00Point10
  · exact factoredHeatR008Q00Point11
  · exact factoredHeatR008Q00Point12
  · exact factoredHeatR008Q00Point13
  · exact factoredHeatR008Q00Point14
  · exact factoredHeatR008Q00Point15
  · exact factoredHeatR008Q00Point16
  · exact factoredHeatR008Q00Point17
  · exact factoredHeatR008Q00Point18
  · exact factoredHeatR008Q00Point19
  · exact factoredHeatR008Q00Point20
  · exact factoredHeatR008Q00Point21
  · exact factoredHeatR008Q00Point22
  · exact factoredHeatR008Q00Point23
  · exact factoredHeatR008Q00Point24
  · exact factoredHeatR008Q00Point25
  · exact factoredHeatR008Q00Point26
  · exact factoredHeatR008Q00Point27
  · exact factoredHeatR008Q00Point28
  · exact factoredHeatR008Q00Point29
  · exact factoredHeatR008Q00Point30
  · exact factoredHeatR008Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR008Q00Bound {t a : ℝ} (tl : ((429/500):ℝ)≤t) (tu : t≤((859/1000):ℝ)) (al : ((324752590410507/549755813888000):ℝ)≤a) (au : a≤((325289461322507/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-1382211605484565413908864434879197/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR008Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (324752590410507/549755813888000) (325289461322507/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR008Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR008Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR008Q00U (-1382211605484565413908864434879197/162259276829213363391578010288128) factoredHeatR008Q00Samples (by decide +kernel)

theorem factored_original_heat_008 {t a : ℝ} (tb : RealMem derivative_008.t t) (ab : RealMem derivative_008.a a) : reportedHeatPeriod t a≤(derivative_008.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((429/500):ℝ) ((859/1000):ℝ) := by simpa [derivative_008,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((429/500):ℝ)<((859/1000):ℝ)) tB
  have aB : a∈Icc ((324752590410507/549755813888000):ℝ) ((325289461322507/549755813888000):ℝ) := by simpa [derivative_008,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((324752590410507/549755813888000):ℝ)<((325289461322507/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR008Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_008] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR009Q00T := Grid.ofRats (859/1000) (43/50)
def factoredHeatR009Q00P : HeatGridParameters := ⟨⟨⟨⟨81102826279760820550544,81358018968906601536382,true⟩,⟨0,0,true⟩⟩, ⟨⟨1122370869979037983067838,1124225338960374445995805,true⟩,⟨0,0,true⟩⟩, ⟨(-1553210733678228254915696),(-1549501795715624048538713),true⟩, ⟨6295975979115875123430157,6335671163592533876790441,true⟩⟩, ⟨373081069423607417929252,397888768153054387604382,true⟩, ⟨596780359778737383275070,603836861525034038659035,true⟩, ⟨(-1499990602518972048293132),(-1485598293055802232187119),true⟩, ⟨(-2800557396283112504025628),(-2792945828616140382325096),true⟩, ⟨(-609944428800062709243490),(-608487932268028767086091),true⟩⟩
theorem factoredHeatR009Q00P_ok : factoredHeatR009Q00P.encloses (heatGridParameters factoredHeatR009Q00T (Grid.ofRats (974782989612433/1649267441664000) (976393602348433/1649267441664000))) := by decide +kernel
def factoredHeatR009Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨615260079186588777076894,615743493134226227640906,true⟩,⟨2373555958978473287276660,2375420877725459517297209,true⟩,⟨⟨722613404617730237461979,724467873599066700437382,true⟩,⟨967571903810194275897146,969426372791530738875941,true⟩⟩⟩
  | 1 => ⟨⟨10690874726091778451426,10749812745675243129367,true⟩,⟨615260079186588777076894,615743493134226227640906,true⟩,⟨⟨(-1136712276271035773029527),(-1131148869327163823130162),true⟩,⟨416387824765039227205701,421951231708911177095218,true⟩⟩⟩
  | 2 => ⟨⟨12462468644228608285,12629980514046306597,true⟩,⟨10690874726091778451426,10749812745675243129367,true⟩,⟨⟨(-85015021569645993937214),(-75742676663238557126157),true⟩,⟨(-1210886924969287799063634),(-1201614580062880362237082),true⟩⟩⟩
  | 3 => ⟨⟨974576519082091,998665654045862,true⟩,⟨12462468644228608285,12629980514046306597,true⟩,⟨⟨1173030557206571788599959,1186011840075514712307964,true⟩,⟨258521394683323588578959,271502677552266512274379,true⟩⟩⟩
  | 4 => ⟨⟨(-29246514996),39673577170,true⟩,⟨974576519082091,998665654045862,true⟩,⟨⟨(-596986908285448424196616),(-580296687453970013551889),true⟩,⟨1047591663795491357174178,1064281884626969767825334,true⟩⟩⟩
  | _ => ⟨⟨(-34359736569),34359740271,true⟩,⟨(-29246514996),39673577170,true⟩,⟨⟨(-855845035145419724764663),(-835445876351405827216531),true⟩,⟨(-874135572687575997099137),(-853736413893562099550747),true⟩⟩⟩
theorem factoredHeatR009Q00F_ok : ∀ n : Fin 6, (factoredHeatR009Q00F n).encloses (FactoredFrequency.build factoredHeatR009Q00T (Grid.ofRats (974782989612433/1649267441664000) (976393602348433/1649267441664000)) n) := by decide +kernel
def factoredHeatR009Q00U : ℕ → ℚ
  | 0 => (-46338199/1000000)
  | 1 => (-16167589/500000)
  | 2 => (-19235939/1000000)
  | 3 => (-11003107/1000000)
  | 4 => (-3281717/500000)
  | 5 => (-218231/50000)
  | 6 => (-1631047/500000)
  | 7 => (-2865837/1000000)
  | 8 => (-3029443/1000000)
  | 9 => (-123539/31250)
  | 10 => (-201459/31250)
  | 11 => (-11101423/1000000)
  | 12 => (-17310393/1000000)
  | 13 => (-2348871/100000)
  | 14 => (-26338463/1000000)
  | 15 => (-4759871/200000)
  | 16 => (-18675503/1000000)
  | 17 => (-2773283/200000)
  | 18 => (-2235881/200000)
  | 19 => (-10207953/1000000)
  | 20 => (-1012089/100000)
  | 21 => (-5057117/500000)
  | 22 => (-4617211/500000)
  | 23 => (-3195321/500000)
  | 24 => (75361/1000000)
  | 25 => (11058739/1000000)
  | 26 => (12761617/500000)
  | 27 => (9354697/250000)
  | 28 => (35474421/1000000)
  | 29 => (2158689/200000)
  | 30 => (-25664469/1000000)
  | 31 => (-23943823/500000)
  | _ => 0
theorem factoredHeatR009Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR009Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR009Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR009Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR009Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR009Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR009Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR009Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR009Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR009Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR009Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR009Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR009Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR009Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR009Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR009Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR009Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR009Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR009Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR009Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR009Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR009Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR009Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR009Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR009Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR009Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR009Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR009Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR009Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR009Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR009Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR009Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR009Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR009Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR009Q00P factoredHeatR009Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR009Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR009Q00Point00
  · exact factoredHeatR009Q00Point01
  · exact factoredHeatR009Q00Point02
  · exact factoredHeatR009Q00Point03
  · exact factoredHeatR009Q00Point04
  · exact factoredHeatR009Q00Point05
  · exact factoredHeatR009Q00Point06
  · exact factoredHeatR009Q00Point07
  · exact factoredHeatR009Q00Point08
  · exact factoredHeatR009Q00Point09
  · exact factoredHeatR009Q00Point10
  · exact factoredHeatR009Q00Point11
  · exact factoredHeatR009Q00Point12
  · exact factoredHeatR009Q00Point13
  · exact factoredHeatR009Q00Point14
  · exact factoredHeatR009Q00Point15
  · exact factoredHeatR009Q00Point16
  · exact factoredHeatR009Q00Point17
  · exact factoredHeatR009Q00Point18
  · exact factoredHeatR009Q00Point19
  · exact factoredHeatR009Q00Point20
  · exact factoredHeatR009Q00Point21
  · exact factoredHeatR009Q00Point22
  · exact factoredHeatR009Q00Point23
  · exact factoredHeatR009Q00Point24
  · exact factoredHeatR009Q00Point25
  · exact factoredHeatR009Q00Point26
  · exact factoredHeatR009Q00Point27
  · exact factoredHeatR009Q00Point28
  · exact factoredHeatR009Q00Point29
  · exact factoredHeatR009Q00Point30
  · exact factoredHeatR009Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR009Q00Bound {t a : ℝ} (tl : ((859/1000):ℝ)≤t) (tu : t≤((43/50):ℝ)) (al : ((974782989612433/1649267441664000):ℝ)≤a) (au : a≤((976393602348433/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2768512312347568892733742665671629/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR009Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (974782989612433/1649267441664000) (976393602348433/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR009Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR009Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR009Q00U (-2768512312347568892733742665671629/324518553658426726783156020576256) factoredHeatR009Q00Samples (by decide +kernel)

theorem factored_original_heat_009 {t a : ℝ} (tb : RealMem derivative_009.t t) (ab : RealMem derivative_009.a a) : reportedHeatPeriod t a≤(derivative_009.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((859/1000):ℝ) ((43/50):ℝ) := by simpa [derivative_009,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((859/1000):ℝ)<((43/50):ℝ)) tB
  have aB : a∈Icc ((974782989612433/1649267441664000):ℝ) ((976393602348433/1649267441664000):ℝ) := by simpa [derivative_009,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((974782989612433/1649267441664000):ℝ)<((976393602348433/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR009Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_009] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR010Q00T := Grid.ofRats (43/50) (861/1000)
def factoredHeatR010Q00P : HeatGridParameters := ⟨⟨⟨⟨80848434044153297160318,81102826279829540028345,true⟩,⟨0,0,true⟩⟩, ⟨⟨1122976730532850408165805,1124831199514186871093774,true⟩,⟨0,0,true⟩⟩, ⟨(-1551999012570603404719758),(-1548290074607999198342779),true⟩, ⟨6287547263965319351098747,6327130710728464408482855,true⟩⟩, ⟨373806166705006513586879,398590948058544262790857,true⟩, ⟨596812982121581858138049,603856884921190680109202,true⟩, ⟨(-1497861609373829206017389),(-1483512474463175748091439),true⟩, ⟨(-2796609816944230379599339),(-2789022798759993744019722),true⟩, ⟨(-609468587033823469671994),(-608012090501789527514597),true⟩⟩
theorem factoredHeatR010Q00P_ok : factoredHeatR010Q00P.encloses (heatGridParameters factoredHeatR010Q00T (Grid.ofRats (975309181602737/1649267441664000) (976919794338737/1649267441664000))) := by decide +kernel
def factoredHeatR010Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨614777044762388639783236,615260079186657496576104,true⟩,⟨2375420877725390797734217,2377287261751474176637319,true⟩,⟨⟨722127944521840213295372,723982413503176676270811,true⟩,⟨967934388979934656875093,969788857961271119853939,true⟩⟩⟩
  | 1 => ⟨⟨10632259846172718681594,10690874726160497928693,true⟩,⟨614777044762388639783236,615260079186657496576104,true⟩,⟨⟨(-1137341202558993664149125),(-1131777795615121714249704),true⟩,⟨414682522974148457345218,420245929918020407234757,true⟩⟩⟩
  | 2 => ⟨⟨12297178557055622050,12462468712948085023,true⟩,⟨10632259846172718681594,10690874726160497928693,true⟩,⟨⟨(-81992172748033472620306),(-72719827841626035809008),true⟩,⟨(-1211084549529193330432251),(-1201812204622785893605412),true⟩⟩⟩
  | 3 => ⟨⟨951133874753901,974645238558828,true⟩,⟨12297178557055622050,12462468712948085023,true⟩,⟨⟨1172093614308758200714317,1185074897177701124422530,true⟩,⟨262657625223666866849884,275638908092609790545586,true⟩⟩⟩
  | 4 => ⟨⟨(-29439556513),39472961741,true⟩,⟨951133874753901,974645238558828,true⟩,⟨⟨(-601743606994233536735602),(-585053386162755126090470),true⟩,⟨1044925919086774724641681,1061616139918253135293138,true⟩⟩⟩
  | _ => ⟨⟨(-34359736666),34359740168,true⟩,⟨(-29439556513),39472961741,true⟩,⟨⟨(-851069574934973956203799),(-830670416140960058655802),true⟩,⟨(-878784225781504274479817),(-858385066987490376931435),true⟩⟩⟩
theorem factoredHeatR010Q00F_ok : ∀ n : Fin 6, (factoredHeatR010Q00F n).encloses (FactoredFrequency.build factoredHeatR010Q00T (Grid.ofRats (975309181602737/1649267441664000) (976919794338737/1649267441664000)) n) := by decide +kernel
def factoredHeatR010Q00U : ℕ → ℚ
  | 0 => (-11542387/250000)
  | 1 => (-2020659/62500)
  | 2 => (-2413009/125000)
  | 3 => (-11083569/1000000)
  | 4 => (-3315939/500000)
  | 5 => (-2208749/500000)
  | 6 => (-165009/50000)
  | 7 => (-2890069/1000000)
  | 8 => (-607913/200000)
  | 9 => (-1973383/500000)
  | 10 => (-6419167/1000000)
  | 11 => (-11046003/1000000)
  | 12 => (-17224211/1000000)
  | 13 => (-23384561/1000000)
  | 14 => (-26256073/1000000)
  | 15 => (-23768627/1000000)
  | 16 => (-18693719/1000000)
  | 17 => (-13907187/1000000)
  | 18 => (-11219643/1000000)
  | 19 => (-10237203/1000000)
  | 20 => (-5068549/500000)
  | 21 => (-10116503/1000000)
  | 22 => (-4611573/500000)
  | 23 => (-1273883/200000)
  | 24 => (94261/1000000)
  | 25 => (2762301/250000)
  | 26 => (12726239/500000)
  | 27 => (37285167/1000000)
  | 28 => (3536147/100000)
  | 29 => (217229/20000)
  | 30 => (-5073901/200000)
  | 31 => (-1902563/40000)
  | _ => 0
theorem factoredHeatR010Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR010Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR010Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR010Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR010Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR010Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR010Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR010Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR010Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR010Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR010Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR010Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR010Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR010Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR010Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR010Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR010Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR010Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR010Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR010Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR010Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR010Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR010Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR010Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR010Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR010Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR010Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR010Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR010Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR010Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR010Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR010Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR010Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR010Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR010Q00P factoredHeatR010Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR010Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR010Q00Point00
  · exact factoredHeatR010Q00Point01
  · exact factoredHeatR010Q00Point02
  · exact factoredHeatR010Q00Point03
  · exact factoredHeatR010Q00Point04
  · exact factoredHeatR010Q00Point05
  · exact factoredHeatR010Q00Point06
  · exact factoredHeatR010Q00Point07
  · exact factoredHeatR010Q00Point08
  · exact factoredHeatR010Q00Point09
  · exact factoredHeatR010Q00Point10
  · exact factoredHeatR010Q00Point11
  · exact factoredHeatR010Q00Point12
  · exact factoredHeatR010Q00Point13
  · exact factoredHeatR010Q00Point14
  · exact factoredHeatR010Q00Point15
  · exact factoredHeatR010Q00Point16
  · exact factoredHeatR010Q00Point17
  · exact factoredHeatR010Q00Point18
  · exact factoredHeatR010Q00Point19
  · exact factoredHeatR010Q00Point20
  · exact factoredHeatR010Q00Point21
  · exact factoredHeatR010Q00Point22
  · exact factoredHeatR010Q00Point23
  · exact factoredHeatR010Q00Point24
  · exact factoredHeatR010Q00Point25
  · exact factoredHeatR010Q00Point26
  · exact factoredHeatR010Q00Point27
  · exact factoredHeatR010Q00Point28
  · exact factoredHeatR010Q00Point29
  · exact factoredHeatR010Q00Point30
  · exact factoredHeatR010Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR010Q00Bound {t a : ℝ} (tl : ((43/50):ℝ)≤t) (tu : t≤((861/1000):ℝ)) (al : ((975309181602737/1649267441664000):ℝ)≤a) (au : a≤((976919794338737/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2771814660770940099568853781833669/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR010Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (975309181602737/1649267441664000) (976919794338737/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR010Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR010Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR010Q00U (-2771814660770940099568853781833669/324518553658426726783156020576256) factoredHeatR010Q00Samples (by decide +kernel)

theorem factored_original_heat_010 {t a : ℝ} (tb : RealMem derivative_010.t t) (ab : RealMem derivative_010.a a) : reportedHeatPeriod t a≤(derivative_010.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((43/50):ℝ) ((861/1000):ℝ) := by simpa [derivative_010,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((43/50):ℝ)<((861/1000):ℝ)) tB
  have aB : a∈Icc ((975309181602737/1649267441664000):ℝ) ((976919794338737/1649267441664000):ℝ) := by simpa [derivative_010,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((975309181602737/1649267441664000):ℝ)<((976919794338737/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR010Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_010] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR011Q00T := Grid.ofRats (861/1000) (431/500)
def factoredHeatR011Q00P : HeatGridParameters := ⟨⟨⟨⟨80594839751262518722537,80848434044222016638112,true⟩,⟨0,0,true⟩⟩, ⟨⟨1123583712934014334003485,1125438181915350796931456,true⟩,⟨0,0,true⟩⟩, ⟨(-1550785047768275553044394),(-1547076109805671346667420),true⟩, ⟨6279131310616858353763188,6318603392986884602769047,true⟩⟩, ⟨374531735196147752719931,399293715562359165509711,true⟩, ⟨596842248877009661957124,603873574641365121340188,true⟩, ⟨(-1495740845952393557997579),(-1481434731465473747114250),true⟩, ⟨(-2792668544105063104013807),(-2785105989198913264175611),true⟩, ⟨(-608991864170734749127900),(-607535367638700806970507),true⟩⟩
theorem factoredHeatR011Q00P_ok : factoredHeatR011Q00P.encloses (heatGridParameters factoredHeatR011Q00T (Grid.ofRats (325278782640451/549755813888000) (325815653552451/549755813888000))) := by decide +kernel
def factoredHeatR011Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨614294389563597163508046,614777044762457359282008,true⟩,⟨2377287261751405457075132,2379155112207865543871134,true⟩,⟨⟨721641403413916688919551,723495872395253151894825,true⟩,⟨968297301335584859969957,970151770316921322948696,true⟩⟩⟩
  | 1 => ⟨⟨10573966334171246580578,10632259846241438158855,true⟩,⟨614294389563597163508046,614777044762457359282008,true⟩,⟨⟨(-1137968721698769843327895),(-1132405314754897893428579),true⟩,⟨412973117282042617934370,418536524225914567823770,true⟩⟩⟩
  | 2 => ⟨⟨12134080717150995496,12297178625775098788,true⟩,⟨10573966334171246580578,10632259846241438158855,true⟩,⟨⟨(-78963239588906877930692),(-69690894682499441119821),true⟩,⟨(-1211274943760469310342108),(-1202002598854061873515650),true⟩⟩⟩
  | 3 => ⟨⟨928255104259915,951202594230638,true⟩,⟨12134080717150995496,12297178625775098788,true⟩,⟨⟨1171140391723005848175054,1184121674591948771883734,true⟩,⟨266798193089289304640930,279779475958232228337167,true⟩⟩⟩
  | 4 => ⟨⟨(-29625310059),39279920224,true⟩,⟨928255104259915,951202594230638,true⟩,⟨⟨(-606497007946669650814141),(-589806787115191240169846),true⟩,⟨1042233751360496135768122,1058923972191974546418640,true⟩⟩⟩
  | _ => ⟨⟨(-34359736759),34359740071,true⟩,⟨(-29625310059),39279920224,true⟩,⟨⟨(-846259647252661456941293),(-825860488458647559393818),true⟩,⟨(-883415016885431850714220),(-863015858091417953166232),true⟩⟩⟩
theorem factoredHeatR011Q00F_ok : ∀ n : Fin 6, (factoredHeatR011Q00F n).encloses (FactoredFrequency.build factoredHeatR011Q00T (Grid.ofRats (325278782640451/549755813888000) (325815653552451/549755813888000)) n) := by decide +kernel
def factoredHeatR011Q00U : ℕ → ℚ
  | 0 => (-23000267/500000)
  | 1 => (-8081141/250000)
  | 2 => (-19371001/1000000)
  | 3 => (-5581633/500000)
  | 4 => (-3349931/500000)
  | 5 => (-1117519/250000)
  | 6 => (-3338051/1000000)
  | 7 => (-145707/50000)
  | 8 => (-3049579/1000000)
  | 9 => (-197013/50000)
  | 10 => (-639173/100000)
  | 11 => (-10990811/1000000)
  | 12 => (-4284601/250000)
  | 13 => (-23280801/1000000)
  | 14 => (-1308687/50000)
  | 15 => (-23737511/1000000)
  | 16 => (-3742263/200000)
  | 17 => (-13947407/1000000)
  | 18 => (-351859/31250)
  | 19 => (-410647/40000)
  | 20 => (-1015309/100000)
  | 21 => (-10118603/1000000)
  | 22 => (-9211767/1000000)
  | 23 => (-396761/62500)
  | 24 => (113071/1000000)
  | 25 => (5519789/500000)
  | 26 => (12690937/500000)
  | 27 => (37152123/1000000)
  | 28 => (35249047/1000000)
  | 29 => (2732163/250000)
  | 30 => (-15673/625)
  | 31 => (-944841/20000)
  | _ => 0
theorem factoredHeatR011Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR011Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR011Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR011Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR011Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR011Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR011Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR011Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR011Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR011Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR011Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR011Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR011Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR011Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR011Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR011Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR011Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR011Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR011Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR011Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR011Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR011Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR011Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR011Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR011Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR011Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR011Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR011Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR011Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR011Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR011Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR011Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR011Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR011Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR011Q00P factoredHeatR011Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR011Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR011Q00Point00
  · exact factoredHeatR011Q00Point01
  · exact factoredHeatR011Q00Point02
  · exact factoredHeatR011Q00Point03
  · exact factoredHeatR011Q00Point04
  · exact factoredHeatR011Q00Point05
  · exact factoredHeatR011Q00Point06
  · exact factoredHeatR011Q00Point07
  · exact factoredHeatR011Q00Point08
  · exact factoredHeatR011Q00Point09
  · exact factoredHeatR011Q00Point10
  · exact factoredHeatR011Q00Point11
  · exact factoredHeatR011Q00Point12
  · exact factoredHeatR011Q00Point13
  · exact factoredHeatR011Q00Point14
  · exact factoredHeatR011Q00Point15
  · exact factoredHeatR011Q00Point16
  · exact factoredHeatR011Q00Point17
  · exact factoredHeatR011Q00Point18
  · exact factoredHeatR011Q00Point19
  · exact factoredHeatR011Q00Point20
  · exact factoredHeatR011Q00Point21
  · exact factoredHeatR011Q00Point22
  · exact factoredHeatR011Q00Point23
  · exact factoredHeatR011Q00Point24
  · exact factoredHeatR011Q00Point25
  · exact factoredHeatR011Q00Point26
  · exact factoredHeatR011Q00Point27
  · exact factoredHeatR011Q00Point28
  · exact factoredHeatR011Q00Point29
  · exact factoredHeatR011Q00Point30
  · exact factoredHeatR011Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR011Q00Bound {t a : ℝ} (tl : ((861/1000):ℝ)≤t) (tu : t≤((431/500):ℝ)) (al : ((325278782640451/549755813888000):ℝ)≤a) (au : a≤((325815653552451/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-346801411374721812105983291216281/40564819207303340847894502572032):ℚ):ℝ) := by
  have ts : factoredHeatR011Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (325278782640451/549755813888000) (325815653552451/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR011Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR011Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR011Q00U (-346801411374721812105983291216281/40564819207303340847894502572032) factoredHeatR011Q00Samples (by decide +kernel)

theorem factored_original_heat_011 {t a : ℝ} (tb : RealMem derivative_011.t t) (ab : RealMem derivative_011.a a) : reportedHeatPeriod t a≤(derivative_011.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((861/1000):ℝ) ((431/500):ℝ) := by simpa [derivative_011,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((861/1000):ℝ)<((431/500):ℝ)) tB
  have aB : a∈Icc ((325278782640451/549755813888000):ℝ) ((325815653552451/549755813888000):ℝ) := by simpa [derivative_011,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((325278782640451/549755813888000):ℝ)<((325815653552451/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR011Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_011] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_007
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_008
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_009
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_010
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_011
