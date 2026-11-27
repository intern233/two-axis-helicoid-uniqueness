import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR018Q00T := Grid.ofRats (217/250) (869/1000)
def factoredHeatR018Q00P : HeatGridParameters := ⟨⟨⟨⟨78841812841483471880457,79089891178074351663640,true⟩,⟨0,0,true⟩⟩, ⟨⟨1127864072619323880914434,1129718541600660343842418,true⟩,⟨0,0,true⟩⟩, ⟨(-1542224328397656459222471),(-1538515390435052252845523),true⟩, ⟨6220576894740208823269827,6259279775710359253248915,true⟩⟩, ⟨379624400749486641419172,404230001036787899010473,true⟩, ⟨596953551559624435024205,603897448211055374905273,true⟩, ⟨(-1481124146274098516973698),(-1467114906100210039469469),true⟩, ⟨(-2765257405916033158664124),(-2757863711322137679196961),true⟩, ⟨(-605630077535212151176187),(-604173581003178209018815),true⟩⟩
theorem factoredHeatR018Q00P_ok : factoredHeatR018Q00P.encloses (heatGridParameters factoredHeatR018Q00T (Grid.ofRats (979553855139569/1649267441664000) (981164467875569/1649267441664000))) := by decide +kernel
def factoredHeatR018Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨610926396503943051883201,611406405448194133597248,true⟩,⟨2390393074569776367830888,2392271222350774398262261,true⟩,⟨⟨718205215507082255822642,720059684488418718798065,true⟩,⟨970849569457201175230883,972704038438537638209819,true⟩⟩⟩
  | 1 => ⟨⟨10174763257386056595898,10230855991752585252015,true⟩,⟨610926396503943051883201,611406405448194133597248,true⟩,⟨⟨(-1142320703414671900881052),(-1136757296470799950981626),true⟩,⟨400892057058039777404981,406455464001911727294270,true⟩⟩⟩
  | 2 => ⟨⟨11051384341859694980,11199929401883330988,true⟩,⟨10174763257386056595898,10230855991752585252015,true⟩,⟨⟨(-57591398081252707689224),(-48319053174845270876742),true⟩,⟨(-1212401622120309132640881),(-1203129277213901695812504),true⟩⟩⟩
  | 3 => ⟨⟨782793014928507,802155422997023,true⟩,⟨11051384341859694980,11199929401883330988,true⟩,⟨⟨1164006110043348147423210,1176987392912291071132500,true⟩,⟨295898168065440946083973,308879450934383869781324,true⟩⟩⟩
  | 4 => ⟨⟨(-30743373244),38117990243,true⟩,⟨782793014928507,802155422997023,true⟩,⟨⟨(-639665084734713137653078),(-622974863903234727007289),true⟩,⟨1022643118109103367608278,1039333338940581778259565,true⟩⟩⟩
  | _ => ⟨⟨(-34359737279),34359739521,true⟩,⟨(-30743373244),38117990243,true⟩,⟨⟨(-811625164199443088391405),(-791226005405429190843483),true⟩,⟨(-915306572716015703150134),(-894907413922001805600785),true⟩⟩⟩
theorem factoredHeatR018Q00F_ok : ∀ n : Fin 6, (factoredHeatR018Q00F n).encloses (FactoredFrequency.build factoredHeatR018Q00T (Grid.ofRats (979553855139569/1649267441664000) (981164467875569/1649267441664000)) n) := by decide +kernel
def factoredHeatR018Q00U : ℕ → ℚ
  | 0 => (-2800519/62500)
  | 1 => (-6449041/200000)
  | 2 => (-19805323/1000000)
  | 3 => (-11698951/1000000)
  | 4 => (-286511/40000)
  | 5 => (-3018/625)
  | 6 => (-112409/31250)
  | 7 => (-615631/200000)
  | 8 => (-3116563/1000000)
  | 9 => (-3894069/1000000)
  | 10 => (-6202011/1000000)
  | 11 => (-2652627/250000)
  | 12 => (-1654809/100000)
  | 13 => (-22565243/1000000)
  | 14 => (-25574829/1000000)
  | 15 => (-11754597/500000)
  | 16 => (-18817441/1000000)
  | 17 => (-14213609/1000000)
  | 18 => (-11527361/1000000)
  | 19 => (-418449/40000)
  | 20 => (-128221/12500)
  | 21 => (-1012863/100000)
  | 22 => (-1825853/200000)
  | 23 => (-6199221/1000000)
  | 24 => (242261/1000000)
  | 25 => (438787/40000)
  | 26 => (995677/40000)
  | 27 => (18118357/500000)
  | 28 => (34476483/1000000)
  | 29 => (11377101/1000000)
  | 30 => (-2885831/125000)
  | 31 => (-11257039/250000)
  | _ => 0
theorem factoredHeatR018Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR018Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR018Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR018Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR018Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR018Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR018Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR018Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR018Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR018Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR018Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR018Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR018Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR018Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR018Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR018Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR018Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR018Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR018Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR018Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR018Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR018Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR018Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR018Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR018Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR018Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR018Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR018Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR018Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR018Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR018Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR018Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR018Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR018Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR018Q00P factoredHeatR018Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR018Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR018Q00Point00
  · exact factoredHeatR018Q00Point01
  · exact factoredHeatR018Q00Point02
  · exact factoredHeatR018Q00Point03
  · exact factoredHeatR018Q00Point04
  · exact factoredHeatR018Q00Point05
  · exact factoredHeatR018Q00Point06
  · exact factoredHeatR018Q00Point07
  · exact factoredHeatR018Q00Point08
  · exact factoredHeatR018Q00Point09
  · exact factoredHeatR018Q00Point10
  · exact factoredHeatR018Q00Point11
  · exact factoredHeatR018Q00Point12
  · exact factoredHeatR018Q00Point13
  · exact factoredHeatR018Q00Point14
  · exact factoredHeatR018Q00Point15
  · exact factoredHeatR018Q00Point16
  · exact factoredHeatR018Q00Point17
  · exact factoredHeatR018Q00Point18
  · exact factoredHeatR018Q00Point19
  · exact factoredHeatR018Q00Point20
  · exact factoredHeatR018Q00Point21
  · exact factoredHeatR018Q00Point22
  · exact factoredHeatR018Q00Point23
  · exact factoredHeatR018Q00Point24
  · exact factoredHeatR018Q00Point25
  · exact factoredHeatR018Q00Point26
  · exact factoredHeatR018Q00Point27
  · exact factoredHeatR018Q00Point28
  · exact factoredHeatR018Q00Point29
  · exact factoredHeatR018Q00Point30
  · exact factoredHeatR018Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR018Q00Bound {t a : ℝ} (tl : ((217/250):ℝ)≤t) (tu : t≤((869/1000):ℝ)) (al : ((979553855139569/1649267441664000):ℝ)≤a) (au : a≤((981164467875569/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-679773687736372987449301610987815/81129638414606681695789005144064):ℚ):ℝ) := by
  have ts : factoredHeatR018Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (979553855139569/1649267441664000) (981164467875569/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR018Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR018Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR018Q00U (-679773687736372987449301610987815/81129638414606681695789005144064) factoredHeatR018Q00Samples (by decide +kernel)

theorem factored_original_heat_018 {t a : ℝ} (tb : RealMem derivative_018.t t) (ab : RealMem derivative_018.a a) : reportedHeatPeriod t a≤(derivative_018.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((217/250):ℝ) ((869/1000):ℝ) := by simpa [derivative_018,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((217/250):ℝ)<((869/1000):ℝ)) tB
  have aB : a∈Icc ((979553855139569/1649267441664000):ℝ) ((981164467875569/1649267441664000):ℝ) := by simpa [derivative_018,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((979553855139569/1649267441664000):ℝ)<((981164467875569/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR018Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_018] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR019Q00T := Grid.ofRats (869/1000) (87/100)
def factoredHeatR019Q00P : HeatGridParameters := ⟨⟨⟨⟨78594512643104314737202,78841812841552191358231,true⟩,⟨0,0,true⟩⟩, ⟨⟨1128480060564703839511383,1130334529546040302439369,true⟩,⟨0,0,true⟩⟩, ⟨(-1540992352506896542028567),(-1537283414544292335651624),true⟩, ⟨6212262998941511270246734,6250857457777249768570212,true⟩⟩, ⟨380353950887817314347556,404937667719938810710139,true⟩, ⟨596956141427526396807303,603887634888581044355146,true⟩, ⟨(-1479068455146919980451161),(-1465101022418924625921344),true⟩, ⟨(-2761367088087694601866870),(-2753997180395791418656042),true⟩, ⟨(-605146281734235763989489),(-603689785202201821832120),true⟩⟩
theorem factoredHeatR019Q00P_ok : factoredHeatR019Q00P.encloses (heatGridParameters factoredHeatR019Q00T (Grid.ofRats (326696280934847/549755813888000) (327233151846847/549755813888000))) := by decide +kernel
def factoredHeatR019Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨610446764409895791175816,610926396504011771381970,true⟩,⟨2392271222350705678699548,2394150845804941109435524,true⟩,⟨⟨717709969548268075212497,719564438529604538188046,true⟩,⟨971215865213281292480941,973070334194617755459983,true⟩⟩⟩
  | 1 => ⟨⟨10118978062833069511382,10174763257454776073140,true⟩,⟨610446764409895791175816,610926396504011771381970,true⟩,⟨⟨(-1142936427494233946110964),(-1137373020550361996211612),true⟩,⟨399149686967452906451665,404713093911324856340830,true⟩⟩⟩
  | 2 => ⟨⟨10904809507126838416,11051384410579171718,true⟩,⟨10118978062833069511382,10174763257454776073140,true⟩,⟨⟨(-54514246062880787883413),(-45241901156473351072886),true⟩,⟨(-1212532614663333979742742),(-1203260269756926542916277),true⟩⟩⟩
  | 3 => ⟨⟨763963403938635,782861734405244,true⟩,⟨10904809507126838416,11051384410579171718,true⟩,⟨⟨1162920126905230810974122,1175901409774173734683875,true⟩,⟨300071085175440008632528,313052368044382932330404,true⟩⟩⟩
  | 4 => ⟨⟨(-30879903287),37976103493,true⟩,⟨763963403938635,782861734405244,true⟩,⟨⟨(-644386335364506386184721),(-627696114533027975539353),true⟩,⟨1019737180792787867848174,1036427401624266278498933,true⟩⟩⟩
  | _ => ⟨⟨(-34359737338),34359739458,true⟩,⟨(-30879903287),37976103493,true⟩,⟨⟨(-806539599046306317379507),(-786140440252292419830727),true⟩,⟨(-919784215610623088655393),(-899385056816609191105051),true⟩⟩⟩
theorem factoredHeatR019Q00F_ok : ∀ n : Fin 6, (factoredHeatR019Q00F n).encloses (FactoredFrequency.build factoredHeatR019Q00T (Grid.ofRats (326696280934847/549755813888000) (327233151846847/549755813888000)) n) := by decide +kernel
def factoredHeatR019Q00U : ℕ → ℚ
  | 0 => (-44636829/1000000)
  | 1 => (-16113189/500000)
  | 2 => (-19862741/1000000)
  | 3 => (-5886207/500000)
  | 4 => (-3613521/500000)
  | 5 => (-195149/40000)
  | 6 => (-454153/125000)
  | 7 => (-1550473/500000)
  | 8 => (-1562863/500000)
  | 9 => (-194369/50000)
  | 10 => (-6175241/1000000)
  | 11 => (-10557067/1000000)
  | 12 => (-16465217/1000000)
  | 13 => (-22464483/1000000)
  | 14 => (-6372049/250000)
  | 15 => (-23475127/1000000)
  | 16 => (-9415107/500000)
  | 17 => (-7124733/500000)
  | 18 => (-11564053/1000000)
  | 19 => (-5243989/500000)
  | 20 => (-2054331/200000)
  | 21 => (-10129401/1000000)
  | 22 => (-4558541/500000)
  | 23 => (-617791/100000)
  | 24 => (130181/500000)
  | 25 => (547967/50000)
  | 26 => (4964509/200000)
  | 27 => (1444327/40000)
  | 28 => (54989/1600)
  | 29 => (11438101/1000000)
  | 30 => (-22811017/1000000)
  | 31 => (-22357087/500000)
  | _ => 0
theorem factoredHeatR019Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR019Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR019Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR019Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR019Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR019Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR019Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR019Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR019Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR019Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR019Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR019Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR019Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR019Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR019Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR019Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR019Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR019Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR019Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR019Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR019Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR019Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR019Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR019Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR019Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR019Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR019Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR019Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR019Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR019Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR019Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR019Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR019Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR019Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR019Q00P factoredHeatR019Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR019Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR019Q00Point00
  · exact factoredHeatR019Q00Point01
  · exact factoredHeatR019Q00Point02
  · exact factoredHeatR019Q00Point03
  · exact factoredHeatR019Q00Point04
  · exact factoredHeatR019Q00Point05
  · exact factoredHeatR019Q00Point06
  · exact factoredHeatR019Q00Point07
  · exact factoredHeatR019Q00Point08
  · exact factoredHeatR019Q00Point09
  · exact factoredHeatR019Q00Point10
  · exact factoredHeatR019Q00Point11
  · exact factoredHeatR019Q00Point12
  · exact factoredHeatR019Q00Point13
  · exact factoredHeatR019Q00Point14
  · exact factoredHeatR019Q00Point15
  · exact factoredHeatR019Q00Point16
  · exact factoredHeatR019Q00Point17
  · exact factoredHeatR019Q00Point18
  · exact factoredHeatR019Q00Point19
  · exact factoredHeatR019Q00Point20
  · exact factoredHeatR019Q00Point21
  · exact factoredHeatR019Q00Point22
  · exact factoredHeatR019Q00Point23
  · exact factoredHeatR019Q00Point24
  · exact factoredHeatR019Q00Point25
  · exact factoredHeatR019Q00Point26
  · exact factoredHeatR019Q00Point27
  · exact factoredHeatR019Q00Point28
  · exact factoredHeatR019Q00Point29
  · exact factoredHeatR019Q00Point30
  · exact factoredHeatR019Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR019Q00Bound {t a : ℝ} (tl : ((869/1000):ℝ)≤t) (tu : t≤((87/100):ℝ)) (al : ((326696280934847/549755813888000):ℝ)≤a) (au : a≤((327233151846847/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-2719453654104413134524882070159545/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR019Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (326696280934847/549755813888000) (327233151846847/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR019Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR019Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR019Q00U (-2719453654104413134524882070159545/324518553658426726783156020576256) factoredHeatR019Q00Samples (by decide +kernel)

theorem factored_original_heat_019 {t a : ℝ} (tb : RealMem derivative_019.t t) (ab : RealMem derivative_019.a a) : reportedHeatPeriod t a≤(derivative_019.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((869/1000):ℝ) ((87/100):ℝ) := by simpa [derivative_019,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((869/1000):ℝ)<((87/100):ℝ)) tB
  have aB : a∈Icc ((326696280934847/549755813888000):ℝ) ((327233151846847/549755813888000):ℝ) := by simpa [derivative_019,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((326696280934847/549755813888000):ℝ)<((327233151846847/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR019Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_019] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR020Q00T := Grid.ofRats (87/100) (871/1000)
def factoredHeatR020Q00P : HeatGridParameters := ⟨⟨⟨⟨78347988142111027001615,78594512643173034214968,true⟩,⟨0,0,true⟩⟩, ⟨⟨1129097178184448401043018,1130951647165784863971006,true⟩,⟨0,0,true⟩⟩, ⟨(-1539758117267407418965293),(-1536049179304803212588354),true⟩, ⟨6203961852952125668254575,6242448251949589553164601,true⟩⟩, ⟨381084025734881853013673,405645972184929499189120,true⟩, ⟨596955417599453556631488,603874529422222913180519,true⟩, ⟨(-1477020802765379150143354),(-1463095028332704546381016),true⟩, ⟨(-2757483199112748207470902),(-2750136995400901471199502),true⟩, ⟨(-604661598689088180478498),(-603205102157054238321133),true⟩⟩
theorem factoredHeatR020Q00P_ok : factoredHeatR020Q00P.encloses (heatGridParameters factoredHeatR020Q00T (Grid.ofRats (980624811595613/1649267441664000) (982235424331613/1649267441664000))) := by decide +kernel
def factoredHeatR020Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨609967508870122427622623,610446764409964510674578,true⟩,⟨2394150845804872389873171,2396031946091791525238698,true⟩,⟨⟨717213628257510671073422,719068097238847134048753,true⟩,⟨971582579640893213912694,973437048622229676891586,true⟩⟩⟩
  | 1 => ⟨⟨10063498721876139815119,10118978062901788988621,true⟩,⟨609967508870122427622623,610446764409964510674578,true⟩,⟨⟨(-1143550609325255977726877),(-1137987202381384027827654),true⟩,⟨397403179762203745238935,402966586706075695127950,true⟩⟩⟩
  | 2 => ⟨⟨10760178698720963497,10904809575846315153,true⟩,⟨10063498721876139815119,10118978062901788988621,true⟩,⟨⟨(-51431126167599315344419),(-42158781261191878533778),true⟩,⟨(-1212655985882507737926439),(-1203383640976100301099816),true⟩⟩⟩
  | 3 => ⟨⟨745586707935520,764032123415372,true⟩,⟨10760178698720963497,10904809575846315153,true⟩,⟨⟨1161817234475264281524253,1174798517344207205233916,true⟩,⟨304247744379358153047499,317229027248301076745360,true⟩⟩⟩
  | 4 => ⟨⟨(-31011278859),37839573450,true⟩,⟨745586707935520,764032123415372,true⟩,⟨⟨(-649102831883393382018135),(-632412611051914971372623),true⟩,⟨1016804234660617475675127,1033494455492095886325926,true⟩⟩⟩
  | _ => ⟨⟨(-34359737394),34359739399,true⟩,⟨(-31011278859),37839573450,true⟩,⟨⟨(-801419622019998756633750),(-781020463225984859085840),true⟩,⟨(-924241417324885360096564),(-903842258530871462546961),true⟩⟩⟩
theorem factoredHeatR020Q00F_ok : ∀ n : Fin 6, (factoredHeatR020Q00F n).encloses (FactoredFrequency.build factoredHeatR020Q00T (Grid.ofRats (980624811595613/1649267441664000) (982235424331613/1649267441664000)) n) := by decide +kernel
def factoredHeatR020Q00U : ℕ → ℚ
  | 0 => (-444651/10000)
  | 1 => (-2012891/62500)
  | 2 => (-1244939/62500)
  | 3 => (-2369023/200000)
  | 4 => (-7290841/1000000)
  | 5 => (-616043/125000)
  | 6 => (-3669087/1000000)
  | 7 => (-3123577/1000000)
  | 8 => (-783697/250000)
  | 9 => (-3880669/1000000)
  | 10 => (-6148553/1000000)
  | 11 => (-10503847/1000000)
  | 12 => (-16382703/1000000)
  | 13 => (-11182049/500000)
  | 14 => (-3175211/125000)
  | 15 => (-23440709/1000000)
  | 16 => (-18842403/1000000)
  | 17 => (-7142393/500000)
  | 18 => (-11600351/1000000)
  | 19 => (-10514453/1000000)
  | 20 => (-5142709/500000)
  | 21 => (-10130009/1000000)
  | 22 => (-9104803/1000000)
  | 23 => (-6156593/1000000)
  | 24 => (139187/500000)
  | 25 => (10948919/1000000)
  | 26 => (12376659/500000)
  | 27 => (7196037/200000)
  | 28 => (34260257/1000000)
  | 29 => (5749177/500000)
  | 30 => (-22537521/1000000)
  | 31 => (-1776067/40000)
  | _ => 0
theorem factoredHeatR020Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR020Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR020Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR020Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR020Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR020Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR020Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR020Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR020Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR020Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR020Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR020Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR020Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR020Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR020Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR020Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR020Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR020Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR020Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR020Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR020Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR020Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR020Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR020Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR020Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR020Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR020Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR020Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR020Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR020Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR020Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR020Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR020Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR020Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR020Q00P factoredHeatR020Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR020Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR020Q00Point00
  · exact factoredHeatR020Q00Point01
  · exact factoredHeatR020Q00Point02
  · exact factoredHeatR020Q00Point03
  · exact factoredHeatR020Q00Point04
  · exact factoredHeatR020Q00Point05
  · exact factoredHeatR020Q00Point06
  · exact factoredHeatR020Q00Point07
  · exact factoredHeatR020Q00Point08
  · exact factoredHeatR020Q00Point09
  · exact factoredHeatR020Q00Point10
  · exact factoredHeatR020Q00Point11
  · exact factoredHeatR020Q00Point12
  · exact factoredHeatR020Q00Point13
  · exact factoredHeatR020Q00Point14
  · exact factoredHeatR020Q00Point15
  · exact factoredHeatR020Q00Point16
  · exact factoredHeatR020Q00Point17
  · exact factoredHeatR020Q00Point18
  · exact factoredHeatR020Q00Point19
  · exact factoredHeatR020Q00Point20
  · exact factoredHeatR020Q00Point21
  · exact factoredHeatR020Q00Point22
  · exact factoredHeatR020Q00Point23
  · exact factoredHeatR020Q00Point24
  · exact factoredHeatR020Q00Point25
  · exact factoredHeatR020Q00Point26
  · exact factoredHeatR020Q00Point27
  · exact factoredHeatR020Q00Point28
  · exact factoredHeatR020Q00Point29
  · exact factoredHeatR020Q00Point30
  · exact factoredHeatR020Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR020Q00Bound {t a : ℝ} (tl : ((87/100):ℝ)≤t) (tu : t≤((871/1000):ℝ)) (al : ((980624811595613/1649267441664000):ℝ)≤a) (au : a≤((982235424331613/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2719483618978032507377052311052393/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR020Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (980624811595613/1649267441664000) (982235424331613/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR020Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR020Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR020Q00U (-2719483618978032507377052311052393/324518553658426726783156020576256) factoredHeatR020Q00Samples (by decide +kernel)

theorem factored_original_heat_020 {t a : ℝ} (tb : RealMem derivative_020.t t) (ab : RealMem derivative_020.a a) : reportedHeatPeriod t a≤(derivative_020.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((87/100):ℝ) ((871/1000):ℝ) := by simpa [derivative_020,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((87/100):ℝ)<((871/1000):ℝ)) tB
  have aB : a∈Icc ((980624811595613/1649267441664000):ℝ) ((982235424331613/1649267441664000):ℝ) := by simpa [derivative_020,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((980624811595613/1649267441664000):ℝ)<((982235424331613/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR020Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_020] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR021Q00T := Grid.ofRats (871/1000) (109/125)
def factoredHeatR021Q00P : HeatGridParameters := ⟨⟨⟨⟨78102236905402307549343,78347988142179746479379,true⟩,⟨0,0,true⟩⟩, ⟨⟨1129715426393701870642590,1131569895375038333570580,true⟩,⟨0,0,true⟩⟩, ⟨(-1538521620848900479766146),(-1534812682886296273389210),true⟩, ⟨6195673454532254288080931,6234052154779918661959580,true⟩⟩, ⟨381814631405976153197243,406354920204622498738061,true⟩, ⟨596951384708202681785538,603858136405598327458071,true⟩, ⟨(-1474981168042081432732394),(-1461096903295781877243181),true⟩, ⟨(-2753605751468328684155914),(-2746283169168648381030218),true⟩, ⟨(-604176027681016744147925),(-602719531148982801990562),true⟩⟩
theorem factoredHeatR021Q00P_ok : factoredHeatR021Q00P.encloses (heatGridParameters factoredHeatR021Q00T (Grid.ofRats (327053920769197/549755813888000) (327590791681197/549755813888000))) := by decide +kernel
def factoredHeatR021Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨609488629588994034490773,609967508870191147121382,true⟩,⟨2396031946091722805675445,2397914524371682934689991,true⟩,⟨⟨716716189999665202992484,718570658981001665967991,true⟩,⟨971949711796317239043134,973804180777653702022198,true⟩⟩⟩
  | 1 => ⟨⟨10008323557611153954511,10063498721944859292352,true⟩,⟨609488629588994034490773,609967508870191147121382,true⟩,⟨⟨(-1144163233684067529608451),(-1138599826740195579709167),true⟩,⟨395652531780904642854718,401215938724776592743764,true⟩⟩⟩
  | 2 => ⟨⟨10617466132963945083,10760178767440440235,true⟩,⟨10008323557611153954511,10063498721944859292352,true⟩,⟨⟨(-48342052178294790759934),(-39069707271887353949266),true⟩,⟨(-1212771691924574443054237),(-1203499347018167006227541),true⟩⟩⟩
  | 3 => ⟨⟨727652032802159,745655427412257,true⟩,⟨10617466132963945083,10760178767440440235,true⟩,⟨⟨1160697363207168773899765,1173678646076111697609634,true⟩,⟨308428076890701025315398,321409359759643949013544,true⟩⟩⟩
  | 4 => ⟨⟨(-31137694557),37708197878,true⟩,⟨727652032802159,745655427412257,true⟩,⟨⟨(-653814407707428424305573),(-637124186875950013660360),true⟩,⟨1013844218223860631346148,1030534439055339041996542,true⟩⟩⟩
  | _ => ⟨⟨(-34359737447),34359739343,true⟩,⟨(-31137694557),37708197878,true⟩,⟨⟨(-796265249461129305610248),(-775866090667115408061546),true⟩,⟨(-928677885987611869973389),(-908278727193597972422861),true⟩⟩⟩
theorem factoredHeatR021Q00F_ok : ∀ n : Fin 6, (factoredHeatR021Q00F n).encloses (FactoredFrequency.build factoredHeatR021Q00T (Grid.ofRats (327053920769197/549755813888000) (327590791681197/549755813888000)) n) := by decide +kernel
def factoredHeatR021Q00U : ℕ → ℚ
  | 0 => (-44293129/1000000)
  | 1 => (-16092471/500000)
  | 2 => (-624193/31250)
  | 3 => (-186204/15625)
  | 4 => (-7354171/1000000)
  | 5 => (-2488829/500000)
  | 6 => (-231541/62500)
  | 7 => (-3146047/1000000)
  | 8 => (-503/160)
  | 9 => (-3873937/1000000)
  | 10 => (-6121949/1000000)
  | 11 => (-10450847/1000000)
  | 12 => (-16300547/1000000)
  | 13 => (-22264087/1000000)
  | 14 => (-12657653/500000)
  | 15 => (-11702973/500000)
  | 16 => (-1885401/100000)
  | 17 => (-14319569/1000000)
  | 18 => (-363633/31250)
  | 19 => (-10540649/1000000)
  | 20 => (-1029897/100000)
  | 21 => (-5065227/500000)
  | 22 => (-2273107/250000)
  | 23 => (-6135271/1000000)
  | 24 => (296297/1000000)
  | 25 => (5469207/500000)
  | 26 => (4936849/200000)
  | 27 => (17926371/500000)
  | 28 => (273223/8000)
  | 29 => (2311573/200000)
  | 30 => (-22266143/1000000)
  | 31 => (-44090733/1000000)
  | _ => 0
theorem factoredHeatR021Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR021Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR021Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR021Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR021Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR021Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR021Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR021Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR021Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR021Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR021Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR021Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR021Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR021Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR021Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR021Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR021Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR021Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR021Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR021Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR021Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR021Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR021Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR021Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR021Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR021Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR021Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR021Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR021Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR021Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR021Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR021Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR021Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR021Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR021Q00P factoredHeatR021Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR021Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR021Q00Point00
  · exact factoredHeatR021Q00Point01
  · exact factoredHeatR021Q00Point02
  · exact factoredHeatR021Q00Point03
  · exact factoredHeatR021Q00Point04
  · exact factoredHeatR021Q00Point05
  · exact factoredHeatR021Q00Point06
  · exact factoredHeatR021Q00Point07
  · exact factoredHeatR021Q00Point08
  · exact factoredHeatR021Q00Point09
  · exact factoredHeatR021Q00Point10
  · exact factoredHeatR021Q00Point11
  · exact factoredHeatR021Q00Point12
  · exact factoredHeatR021Q00Point13
  · exact factoredHeatR021Q00Point14
  · exact factoredHeatR021Q00Point15
  · exact factoredHeatR021Q00Point16
  · exact factoredHeatR021Q00Point17
  · exact factoredHeatR021Q00Point18
  · exact factoredHeatR021Q00Point19
  · exact factoredHeatR021Q00Point20
  · exact factoredHeatR021Q00Point21
  · exact factoredHeatR021Q00Point22
  · exact factoredHeatR021Q00Point23
  · exact factoredHeatR021Q00Point24
  · exact factoredHeatR021Q00Point25
  · exact factoredHeatR021Q00Point26
  · exact factoredHeatR021Q00Point27
  · exact factoredHeatR021Q00Point28
  · exact factoredHeatR021Q00Point29
  · exact factoredHeatR021Q00Point30
  · exact factoredHeatR021Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR021Q00Bound {t a : ℝ} (tl : ((871/1000):ℝ)≤t) (tu : t≤((109/125):ℝ)) (al : ((327053920769197/549755813888000):ℝ)≤a) (au : a≤((327590791681197/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-2719205558144049070504693753909589/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR021Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (327053920769197/549755813888000) (327590791681197/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR021Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR021Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR021Q00U (-2719205558144049070504693753909589/324518553658426726783156020576256) factoredHeatR021Q00Samples (by decide +kernel)

theorem factored_original_heat_021 {t a : ℝ} (tb : RealMem derivative_021.t t) (ab : RealMem derivative_021.a a) : reportedHeatPeriod t a≤(derivative_021.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((871/1000):ℝ) ((109/125):ℝ) := by simpa [derivative_021,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((871/1000):ℝ)<((109/125):ℝ)) tB
  have aB : a∈Icc ((327053920769197/549755813888000):ℝ) ((327590791681197/549755813888000):ℝ) := by simpa [derivative_021,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((327053920769197/549755813888000):ℝ)<((327590791681197/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR021Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_021] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR022Q00T := Grid.ofRats (109/125) (873/1000)
def factoredHeatR022Q00P : HeatGridParameters := ⟨⟨⟨⟨77857256507508674119164,78102236905471027027108,true⟩,⟨0,0,true⟩⟩, ⟨⟨1130334806121404698746873,1132189275102741161674865,true⟩,⟨0,0,true⟩⟩, ⟨(-1537282861393494823557576),(-1533573923430890617180644),true⟩, ⟨6187397801244450368052709,6225669162626330287263556,true⟩⟩, ⟨382545774057823760420163,407064517598524626461056,true⟩, ⟨596944047374997361195748,603838460420864173336199,true⟩, ⟨(-1472949529907649051187664),(-1459106626778232674763072),true⟩, ⟨(-2749734757414147462071173),(-2742435714310709868753330),true⟩, ⟨(-603689567980433331319128),(-602233071448399389161768),true⟩⟩
theorem factoredHeatR022Q00P_ok : factoredHeatR022Q00P.encloses (heatGridParameters factoredHeatR022Q00T (Grid.ofRats (981699695747263/1649267441664000) (983310308483263/1649267441664000))) := by decide +kernel
def factoredHeatR022Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨609010126271113780306086,609488629589062753989364,true⟩,⟨2397914524371614215127087,2399798581805884327278105,true⟩,⟨⟨716217653126958477944713,718072122108294940920286,true⟩,⟨972317260738975733915373,974171729720312196894513,true⟩⟩⟩
  | 1 => ⟨⟨9953450902327963863368,10008323557679873431745,true⟩,⟨609010126271113780306086,609488629589062753989364,true⟩,⟨⟨(-1144774285308226266284856),(-1139210878364354316385341),true⟩,⟨393897739355376088388348,399461146299248038277592,true⟩⟩⟩
  | 2 => ⟨⟨10476646368147336341,10617466201683421821,true⟩,⟨9953450902327963863368,10008323557679873431745,true⟩,⟨⟨(-45247038027219424047641),(-35974693120811987237527),true⟩,⟨(-1212879688855519094071750),(-1203607343949111657245565),true⟩⟩⟩
  | 3 => ⟨⟨710148746461422,727720752278896,true⟩,⟨10476646368147336341,10617466201683421821,true⟩,⟨⟨1159560443637700509837497,1172541726506643433547789,true⟩,⟨312612013416460922870192,325593296285403846568822,true⟩⟩⟩
  | 4 => ⟨⟨(-31259337634),37581782180,true⟩,⟨710148746461422,727720752278896,true⟩,⟨⟨(-658520895332664958244415),(-641830674501186547598666),true⟩,⟨1010857070723293885986262,1027547291554772296637086,true⟩⟩⟩
  | _ => ⟨⟨(-34359737497),34359739290,true⟩,⟨(-31259337634),37581782180,true⟩,⟨⟨(-791076499766709527012133),(-770677340972695629462768),true⟩,⟨(-933093328733750531884668),(-912694169939736634333351),true⟩⟩⟩
theorem factoredHeatR022Q00F_ok : ∀ n : Fin 6, (factoredHeatR022Q00F n).encloses (FactoredFrequency.build factoredHeatR022Q00T (Grid.ofRats (981699695747263/1649267441664000) (983310308483263/1649267441664000)) n) := by decide +kernel
def factoredHeatR022Q00U : ℕ → ℚ
  | 0 => (-1378779/31250)
  | 1 => (-2010153/62500)
  | 2 => (-5007051/250000)
  | 3 => (-5994119/500000)
  | 4 => (-7417031/1000000)
  | 5 => (-2513333/500000)
  | 6 => (-3740007/1000000)
  | 7 => (-3168359/1000000)
  | 8 => (-315261/100000)
  | 9 => (-241699/62500)
  | 10 => (-6095427/1000000)
  | 11 => (-2079613/200000)
  | 12 => (-16218747/1000000)
  | 13 => (-443289/20000)
  | 14 => (-504581/20000)
  | 15 => (-584271/25000)
  | 16 => (-18865041/1000000)
  | 17 => (-7176909/500000)
  | 18 => (-1458971/125000)
  | 19 => (-10566567/1000000)
  | 20 => (-10312311/1000000)
  | 21 => (-633171/62500)
  | 22 => (-4539979/500000)
  | 23 => (-1222789/200000)
  | 24 => (78533/250000)
  | 25 => (5463913/500000)
  | 26 => (984613/40000)
  | 27 => (35725843/1000000)
  | 28 => (1361839/40000)
  | 29 => (36302/3125)
  | 30 => (-21996867/1000000)
  | 31 => (-1368167/31250)
  | _ => 0
theorem factoredHeatR022Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR022Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR022Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR022Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR022Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR022Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR022Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR022Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR022Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR022Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR022Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR022Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR022Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR022Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR022Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR022Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR022Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR022Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR022Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR022Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR022Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR022Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR022Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR022Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR022Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR022Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR022Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR022Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR022Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR022Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR022Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR022Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR022Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR022Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR022Q00P factoredHeatR022Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR022Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR022Q00Point00
  · exact factoredHeatR022Q00Point01
  · exact factoredHeatR022Q00Point02
  · exact factoredHeatR022Q00Point03
  · exact factoredHeatR022Q00Point04
  · exact factoredHeatR022Q00Point05
  · exact factoredHeatR022Q00Point06
  · exact factoredHeatR022Q00Point07
  · exact factoredHeatR022Q00Point08
  · exact factoredHeatR022Q00Point09
  · exact factoredHeatR022Q00Point10
  · exact factoredHeatR022Q00Point11
  · exact factoredHeatR022Q00Point12
  · exact factoredHeatR022Q00Point13
  · exact factoredHeatR022Q00Point14
  · exact factoredHeatR022Q00Point15
  · exact factoredHeatR022Q00Point16
  · exact factoredHeatR022Q00Point17
  · exact factoredHeatR022Q00Point18
  · exact factoredHeatR022Q00Point19
  · exact factoredHeatR022Q00Point20
  · exact factoredHeatR022Q00Point21
  · exact factoredHeatR022Q00Point22
  · exact factoredHeatR022Q00Point23
  · exact factoredHeatR022Q00Point24
  · exact factoredHeatR022Q00Point25
  · exact factoredHeatR022Q00Point26
  · exact factoredHeatR022Q00Point27
  · exact factoredHeatR022Q00Point28
  · exact factoredHeatR022Q00Point29
  · exact factoredHeatR022Q00Point30
  · exact factoredHeatR022Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR022Q00Bound {t a : ℝ} (tl : ((109/125):ℝ)≤t) (tu : t≤((873/1000):ℝ)) (al : ((981699695747263/1649267441664000):ℝ)≤a) (au : a≤((983310308483263/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2718644350479552475207482587041367/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR022Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (981699695747263/1649267441664000) (983310308483263/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR022Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR022Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR022Q00U (-2718644350479552475207482587041367/324518553658426726783156020576256) factoredHeatR022Q00Samples (by decide +kernel)

theorem factored_original_heat_022 {t a : ℝ} (tb : RealMem derivative_022.t t) (ab : RealMem derivative_022.a a) : reportedHeatPeriod t a≤(derivative_022.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((109/125):ℝ) ((873/1000):ℝ) := by simpa [derivative_022,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((109/125):ℝ)<((873/1000):ℝ)) tB
  have aB : a∈Icc ((981699695747263/1649267441664000):ℝ) ((983310308483263/1649267441664000):ℝ) := by simpa [derivative_022,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((981699695747263/1649267441664000):ℝ)<((983310308483263/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR022Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_022] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_018
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_019
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_020
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_021
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_022
