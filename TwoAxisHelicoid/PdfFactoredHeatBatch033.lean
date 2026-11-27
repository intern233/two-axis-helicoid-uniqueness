import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR033Q00T := Grid.ofRats (883/1000) (221/250)
def factoredHeatR033Q00P : HeatGridParameters := ⟨⟨⟨⟨75212661376140290614457,75449320469235094991708,true⟩,⟨0,0,true⟩⟩, ⟨⟨1137222937206475174207712,1139077406187811637135726,true⟩,⟨0,0,true⟩⟩, ⟨(-1523506599223353872635855),(-1519797661260749666258967),true⟩, ⟨6097205933489208790851973,6134319978716101416147283,true⟩⟩, ⟨390625457601450102217665,414914758161986901116319,true⟩, ⟨596646518675734477820685,603406655668984642471348,true⟩, ⟨(-1451123288445752163428968),(-1437725742515322677851759),true⟩, ⟨(-2707583053273121698382043),(-2700537613705623052680116),true⟩, ⟨(-598279642476978107110446),(-596823145944944164953121),true⟩⟩
theorem factoredHeatR033Q00P_ok : factoredHeatR033Q00P.encloses (heatGridParameters factoredHeatR033Q00T (Grid.ofRats (987682061462147/1649267441664000) (989292674198147/1649267441664000))) := by decide +kernel
def factoredHeatR033Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨603771319097095231110332,604245706249308420848165,true⟩,⟨2418720765767357904084841,2420621170804255641878390,true⟩,⟨⟨710660759538448397037479,712515228519784860013012,true⟩,⟨976387537772864473798076,978242006754200936777283,true⟩⟩⟩
  | 1 => ⟨⟨9369349375067495634092,9421001920924703059238,true⟩,⟨603771319097095231110332,604245706249308420848165,true⟩,⟨⟨(-1151387642501371718095578),(-1145824235557499768196488),true⟩,⟨374320450005355982047306,379883856949227931935784,true⟩⟩⟩
  | 2 => ⟨⟨9045606476005616370,9167191270645442215,true⟩,⟨9369349375067495634092,9421001920924703059238,true⟩,⟨⟨(-10813997533816876141199),(-1541652627409439330537),true⟩,⟨(-1213546207074546525817760),(-1204273862168139088990543),true⟩⟩⟩
  | 3 => ⟨⟨543287593049103,556747112210917,true⟩,⟨9045606476005616370,9167191270645442215,true⟩,⟨⟨1145909375690653065783041,1158890658559595989494466,true⟩,⟨358852810485657542714184,371834093354600466414787,true⟩⟩⟩
  | 4 => ⟨⟨(-32329401423),36469734834,true⟩,⟨543287593049103,556747112210917,true⟩,⟨⟨(-709907566970270478874509),(-693217346138792068228670),true⟩,⟨976191205259855534944610,992881426091333945594341,true⟩⟩⟩
  | _ => ⟨⟨(-34359737896),34359738868,true⟩,⟨(-32329401423),36469734834,true⟩,⟨⟨(-731738781520393684098998),(-711339622726379786551495),true⟩,⟨(-980190722207109818995680),(-959791563413095921444761),true⟩⟩⟩
theorem factoredHeatR033Q00F_ok : ∀ n : Fin 6, (factoredHeatR033Q00F n).encloses (FactoredFrequency.build factoredHeatR033Q00T (Grid.ofRats (987682061462147/1649267441664000) (989292674198147/1649267441664000)) n) := by decide +kernel
def factoredHeatR033Q00U : ℕ → ℚ
  | 0 => (-659587/15625)
  | 1 => (-31840273/1000000)
  | 2 => (-2568739/125000)
  | 3 => (-12721401/1000000)
  | 4 => (-8077359/1000000)
  | 5 => (-173293/31250)
  | 6 => (-5143/1250)
  | 7 => (-3403269/1000000)
  | 8 => (-101173/31250)
  | 9 => (-1895731/500000)
  | 10 => (-5809083/1000000)
  | 11 => (-4915807/500000)
  | 12 => (-3835501/250000)
  | 13 => (-21092653/1000000)
  | 14 => (-4857767/200000)
  | 15 => (-22963223/1000000)
  | 16 => (-9474703/500000)
  | 17 => (-3673953/250000)
  | 18 => (-12036543/1000000)
  | 19 => (-10833279/1000000)
  | 20 => (-5222611/500000)
  | 21 => (-10121647/1000000)
  | 22 => (-8936749/1000000)
  | 23 => (-1173751/200000)
  | 24 => (504473/1000000)
  | 25 => (10806067/1000000)
  | 26 => (23867371/1000000)
  | 27 => (34364979/1000000)
  | 28 => (658017/20000)
  | 29 => (2443249/200000)
  | 30 => (-19169057/1000000)
  | 31 => (-10119599/250000)
  | _ => 0
theorem factoredHeatR033Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR033Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR033Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR033Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR033Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR033Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR033Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR033Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR033Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR033Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR033Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR033Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR033Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR033Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR033Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR033Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR033Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR033Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR033Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR033Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR033Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR033Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR033Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR033Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR033Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR033Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR033Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR033Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR033Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR033Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR033Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR033Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR033Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR033Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR033Q00P factoredHeatR033Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR033Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR033Q00Point00
  · exact factoredHeatR033Q00Point01
  · exact factoredHeatR033Q00Point02
  · exact factoredHeatR033Q00Point03
  · exact factoredHeatR033Q00Point04
  · exact factoredHeatR033Q00Point05
  · exact factoredHeatR033Q00Point06
  · exact factoredHeatR033Q00Point07
  · exact factoredHeatR033Q00Point08
  · exact factoredHeatR033Q00Point09
  · exact factoredHeatR033Q00Point10
  · exact factoredHeatR033Q00Point11
  · exact factoredHeatR033Q00Point12
  · exact factoredHeatR033Q00Point13
  · exact factoredHeatR033Q00Point14
  · exact factoredHeatR033Q00Point15
  · exact factoredHeatR033Q00Point16
  · exact factoredHeatR033Q00Point17
  · exact factoredHeatR033Q00Point18
  · exact factoredHeatR033Q00Point19
  · exact factoredHeatR033Q00Point20
  · exact factoredHeatR033Q00Point21
  · exact factoredHeatR033Q00Point22
  · exact factoredHeatR033Q00Point23
  · exact factoredHeatR033Q00Point24
  · exact factoredHeatR033Q00Point25
  · exact factoredHeatR033Q00Point26
  · exact factoredHeatR033Q00Point27
  · exact factoredHeatR033Q00Point28
  · exact factoredHeatR033Q00Point29
  · exact factoredHeatR033Q00Point30
  · exact factoredHeatR033Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR033Q00Bound {t a : ℝ} (tl : ((883/1000):ℝ)≤t) (tu : t≤((221/250):ℝ)) (al : ((987682061462147/1649267441664000):ℝ)≤a) (au : a≤((989292674198147/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-81491304784821007255269385114383/10141204801825835211973625643008):ℚ):ℝ) := by
  have ts : factoredHeatR033Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (987682061462147/1649267441664000) (989292674198147/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR033Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR033Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR033Q00U (-81491304784821007255269385114383/10141204801825835211973625643008) factoredHeatR033Q00Samples (by decide +kernel)

theorem factored_original_heat_033 {t a : ℝ} (tb : RealMem derivative_033.t t) (ab : RealMem derivative_033.a a) : reportedHeatPeriod t a≤(derivative_033.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((883/1000):ℝ) ((221/250):ℝ) := by simpa [derivative_033,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((883/1000):ℝ)<((221/250):ℝ)) tB
  have aB : a∈Icc ((987682061462147/1649267441664000):ℝ) ((989292674198147/1649267441664000):ℝ) := by simpa [derivative_033,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((987682061462147/1649267441664000):ℝ)<((989292674198147/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR033Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_033] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR034Q00T := Grid.ofRats (221/250) (177/200)
def factoredHeatR034Q00P : HeatGridParameters := ⟨⟨⟨⟨74976744602938474934335,75212661376209010092195,true⟩,⟨0,0,true⟩⟩, ⟨⟨1137855970753847852537215,1139710439735184315465231,true⟩,⟨0,0,true⟩⟩, ⟨(-1522240532128608515976845),(-1518531594166004309599961),true⟩, ⟨6089082972032470464754182,6126093904323244709876650,true⟩⟩, ⟨391363415140232678319118,415632723515433164499807,true⟩, ⟨596599844192503497487801,603347939933483847398161,true⟩, ⟨(-1449185976234235644008762),(-1435828056310394037713583),true⟩, ⟨(-2703790381619858512314525),(-2696767521375424410590282),true⟩, ⟨(-597782459091502633960729),(-596325962559468691803407),true⟩⟩
theorem factoredHeatR034Q00P_ok : factoredHeatR034Q00P.encloses (heatGridParameters factoredHeatR034Q00T (Grid.ofRats (988231853291513/1649267441664000) (989842466027513/1649267441664000))) := by decide +kernel
def factoredHeatR034Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨603297304381474168952961,603771319097163950608724,true⟩,⟨2420621170804186922314304,2422523069001996461048298,true⟩,⟨⟨710148907664242516293035,712003376645578979268535,true⟩,⟨976760014781302217075357,978614483762638680054556,true⟩⟩⟩
  | 1 => ⟨⟨9317980024793543756086,9369349375136215111298,true⟩,⟨603297304381474168952961,603771319097163950608724,true⟩,⟨⟨(-1151978614520022461938139),(-1146415207576150512039040),true⟩,⟨372515641267457715033847,378079048211329664922278,true⟩⟩⟩
  | 2 => ⟨⟨8925634331866981681,9045606544725093107,true⟩,⟨9317980024793543756086,9369349375136215111298,true⟩,⟨⟨(-7648853566886764716028),1623491339520672094530,true⟩,⟨(-1213558238214024454241839),(-1204285893307617017414706),true⟩⟩⟩
  | 3 => ⟨⟨530218886787267,543356312525840,true⟩,⟨8925634331866981681,9045606544725093107,true⟩,⟨⟨1144562495814590863596651,1157543778683533787308366,true⟩,⟨363074390136420276246664,376055673005363199947633,true⟩⟩⟩
  | 4 => ⟨⟨(-32406053526),36390075314,true⟩,⟨530218886787267,543356312525840,true⟩,⟨⟨(-714539581155278538413562),(-697849360323800127767144),true⟩,⟨972874032705615130038727,989564253537093540688927,true⟩⟩⟩
  | _ => ⟨⟨(-34359737922),34359738841,true⟩,⟨(-32406053526),36390075314,true⟩,⟨⟨(-726139729208624648564454),(-705740570414610751016689),true⟩,⟨(-984330648205830704540084),(-963931489411816806988766),true⟩⟩⟩
theorem factoredHeatR034Q00F_ok : ∀ n : Fin 6, (factoredHeatR034Q00F n).encloses (FactoredFrequency.build factoredHeatR034Q00T (Grid.ofRats (988231853291513/1649267441664000) (989842466027513/1649267441664000)) n) := by decide +kernel
def factoredHeatR034Q00U : ℕ → ℚ
  | 0 => (-42039163/1000000)
  | 1 => (-6360883/200000)
  | 2 => (-10295443/500000)
  | 3 => (-255671/20000)
  | 4 => (-1626909/200000)
  | 5 => (-698833/125000)
  | 6 => (-2073557/500000)
  | 7 => (-3423671/1000000)
  | 8 => (-811133/250000)
  | 9 => (-3784343/1000000)
  | 10 => (-5783531/1000000)
  | 11 => (-4890693/500000)
  | 12 => (-305287/20000)
  | 13 => (-10498689/500000)
  | 14 => (-12102079/500000)
  | 15 => (-22924313/1000000)
  | 16 => (-4738453/250000)
  | 17 => (-14723789/1000000)
  | 18 => (-12067361/1000000)
  | 19 => (-10855853/1000000)
  | 20 => (-10456051/1000000)
  | 21 => (-5059929/500000)
  | 22 => (-5577/625)
  | 23 => (-2923181/500000)
  | 24 => (130313/250000)
  | 25 => (5397271/500000)
  | 26 => (1487519/62500)
  | 27 => (34244379/1000000)
  | 28 => (32799457/1000000)
  | 29 => (12266641/1000000)
  | 30 => (-9461891/500000)
  | 31 => (-20093481/500000)
  | _ => 0
theorem factoredHeatR034Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR034Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR034Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR034Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR034Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR034Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR034Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR034Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR034Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR034Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR034Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR034Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR034Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR034Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR034Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR034Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR034Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR034Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR034Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR034Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR034Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR034Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR034Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR034Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR034Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR034Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR034Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR034Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR034Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR034Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR034Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR034Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR034Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR034Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR034Q00P factoredHeatR034Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR034Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR034Q00Point00
  · exact factoredHeatR034Q00Point01
  · exact factoredHeatR034Q00Point02
  · exact factoredHeatR034Q00Point03
  · exact factoredHeatR034Q00Point04
  · exact factoredHeatR034Q00Point05
  · exact factoredHeatR034Q00Point06
  · exact factoredHeatR034Q00Point07
  · exact factoredHeatR034Q00Point08
  · exact factoredHeatR034Q00Point09
  · exact factoredHeatR034Q00Point10
  · exact factoredHeatR034Q00Point11
  · exact factoredHeatR034Q00Point12
  · exact factoredHeatR034Q00Point13
  · exact factoredHeatR034Q00Point14
  · exact factoredHeatR034Q00Point15
  · exact factoredHeatR034Q00Point16
  · exact factoredHeatR034Q00Point17
  · exact factoredHeatR034Q00Point18
  · exact factoredHeatR034Q00Point19
  · exact factoredHeatR034Q00Point20
  · exact factoredHeatR034Q00Point21
  · exact factoredHeatR034Q00Point22
  · exact factoredHeatR034Q00Point23
  · exact factoredHeatR034Q00Point24
  · exact factoredHeatR034Q00Point25
  · exact factoredHeatR034Q00Point26
  · exact factoredHeatR034Q00Point27
  · exact factoredHeatR034Q00Point28
  · exact factoredHeatR034Q00Point29
  · exact factoredHeatR034Q00Point30
  · exact factoredHeatR034Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR034Q00Bound {t a : ℝ} (tl : ((221/250):ℝ)≤t) (tu : t≤((177/200):ℝ)) (al : ((988231853291513/1649267441664000):ℝ)≤a) (au : a≤((989842466027513/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2610249896494285499450917673740467/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR034Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (988231853291513/1649267441664000) (989842466027513/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR034Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR034Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR034Q00U (-2610249896494285499450917673740467/324518553658426726783156020576256) factoredHeatR034Q00Samples (by decide +kernel)

theorem factored_original_heat_034 {t a : ℝ} (tb : RealMem derivative_034.t t) (ab : RealMem derivative_034.a a) : reportedHeatPeriod t a≤(derivative_034.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((221/250):ℝ) ((177/200):ℝ) := by simpa [derivative_034,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((221/250):ℝ)<((177/200):ℝ)) tB
  have aB : a∈Icc ((988231853291513/1649267441664000):ℝ) ((989842466027513/1649267441664000):ℝ) := by simpa [derivative_034,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((988231853291513/1649267441664000):ℝ)<((989842466027513/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR034Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_034] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR035Q00T := Grid.ofRats (177/200) (443/500)
def factoredHeatR035Q00P : HeatGridParameters := ⟨⟨⟨⟨74741567821153790352976,74976744603007194412066,true⟩,⟨0,0,true⟩⟩, ⟨⟨1138490148728263178361608,1140344617709599641289626,true⟩,⟨0,0,true⟩⟩, ⟨(-1520972176179777864328053),(-1517263238217173657951174),true⟩, ⟨6080972709099956774589965,6117880872992624345964032,true⟩⟩, ⟨392101994227826451137274,416351416252776125649559,true⟩, ⟨596549925608384467895541,603286000331433670764887,true⟩, ⟨(-1447256389202440150516507),(-1433937954030686902713537),true⟩, ⟨(-2700004303878011521034080),(-2693003945134154799088126),true⟩, ⟨(-597284376875129723095274),(-595827880343095780937955),true⟩⟩
theorem factoredHeatR035Q00P_ok : factoredHeatR035Q00P.encloses (heatGridParameters factoredHeatR035Q00T (Grid.ofRats (988782639059731/1649267441664000) (990393251795731/1649267441664000))) := by decide +kernel
def factoredHeatR035Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨602823661809980392130074,603297304381542888451564,true⟩,⟨2422523069001927741484551,2424426461533835567887774,true⟩,⟨⟨709635934940722510191881,711490403922058973167252,true⟩,⟨977132896369658582623379,978987365350995045602512,true⟩⟩⟩
  | 1 => ⟨⟨9266892317357522582648,9317980024862263233288,true⟩,⟨602823661809980392130074,603297304381542888451564,true⟩,⟨⟨(-1152567811328465700631763),(-1147004404384593750732439),true⟩,⟨370706641073158913651499,376270048017030863540130,true⟩⟩⟩
  | 2 => ⟨⟨8807253381790649841,8925634400586458419,true⟩,⟨9266892317357522582648,9317980024862263233288,true⟩,⟨⟨(-4477966813506100319900),4794378092901336490338,true⟩,⟨(-1213561981716070968111667),(-1204289636809663531284854),true⟩⟩⟩
  | 3 => ⟨⟨517464526526880,530287606264004,true⟩,⟨8807253381790649841,8925634400586458419,true⟩,⟨⟨1143197674207470189707055,1156178957076413113418133,true⟩,⟨367298623001116711136335,380279905870059634836736,true⟩⟩⟩
  | 4 => ⟨⟨(-32479811752),36313423211,true⟩,⟨517464526526880,530287606264004,true⟩,⟨⟨(-719164242477208265553609),(-702474021645729854907292),true⟩,⟨969529011762715175581875,986219232594193586231862,true⟩⟩⟩
  | _ => ⟨⟨(-34359737946),34359738815,true⟩,⟨(-32479811752),36313423211,true⟩,⟨⟨(-720506737523169172957153),(-700107578729155275407962),true⟩,⟨(-988445651939921936367203),(-968046493145908038814320),true⟩⟩⟩
theorem factoredHeatR035Q00F_ok : ∀ n : Fin 6, (factoredHeatR035Q00F n).encloses (FactoredFrequency.build factoredHeatR035Q00T (Grid.ofRats (988782639059731/1649267441664000) (990393251795731/1649267441664000)) n) := by decide +kernel
def factoredHeatR035Q00U : ℕ → ℚ
  | 0 => (-2093233/50000)
  | 1 => (-31767529/1000000)
  | 2 => (-20630807/1000000)
  | 3 => (-12844953/1000000)
  | 4 => (-4095627/500000)
  | 5 => (-5635637/1000000)
  | 6 => (-2089803/500000)
  | 7 => (-1721957/500000)
  | 8 => (-3251433/1000000)
  | 9 => (-944297/250000)
  | 10 => (-719753/125000)
  | 11 => (-4865683/500000)
  | 12 => (-15187031/1000000)
  | 13 => (-2612807/125000)
  | 14 => (-4823923/200000)
  | 15 => (-5721277/250000)
  | 16 => (-18957691/1000000)
  | 17 => (-2950251/200000)
  | 18 => (-1209779/100000)
  | 19 => (-2719537/250000)
  | 20 => (-10466671/1000000)
  | 21 => (-2023583/200000)
  | 22 => (-2227391/250000)
  | 23 => (-5823973/1000000)
  | 24 => (537947/1000000)
  | 25 => (10782947/1000000)
  | 26 => (11866697/500000)
  | 27 => (533192/15625)
  | 28 => (4087313/125000)
  | 29 => (1539547/125000)
  | 30 => (-3736081/200000)
  | 31 => (-7979401/200000)
  | _ => 0
theorem factoredHeatR035Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR035Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR035Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR035Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR035Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR035Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR035Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR035Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR035Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR035Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR035Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR035Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR035Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR035Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR035Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR035Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR035Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR035Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR035Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR035Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR035Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR035Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR035Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR035Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR035Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR035Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR035Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR035Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR035Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR035Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR035Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR035Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR035Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR035Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR035Q00P factoredHeatR035Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR035Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR035Q00Point00
  · exact factoredHeatR035Q00Point01
  · exact factoredHeatR035Q00Point02
  · exact factoredHeatR035Q00Point03
  · exact factoredHeatR035Q00Point04
  · exact factoredHeatR035Q00Point05
  · exact factoredHeatR035Q00Point06
  · exact factoredHeatR035Q00Point07
  · exact factoredHeatR035Q00Point08
  · exact factoredHeatR035Q00Point09
  · exact factoredHeatR035Q00Point10
  · exact factoredHeatR035Q00Point11
  · exact factoredHeatR035Q00Point12
  · exact factoredHeatR035Q00Point13
  · exact factoredHeatR035Q00Point14
  · exact factoredHeatR035Q00Point15
  · exact factoredHeatR035Q00Point16
  · exact factoredHeatR035Q00Point17
  · exact factoredHeatR035Q00Point18
  · exact factoredHeatR035Q00Point19
  · exact factoredHeatR035Q00Point20
  · exact factoredHeatR035Q00Point21
  · exact factoredHeatR035Q00Point22
  · exact factoredHeatR035Q00Point23
  · exact factoredHeatR035Q00Point24
  · exact factoredHeatR035Q00Point25
  · exact factoredHeatR035Q00Point26
  · exact factoredHeatR035Q00Point27
  · exact factoredHeatR035Q00Point28
  · exact factoredHeatR035Q00Point29
  · exact factoredHeatR035Q00Point30
  · exact factoredHeatR035Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR035Q00Bound {t a : ℝ} (tl : ((177/200):ℝ)≤t) (tu : t≤((443/500):ℝ)) (al : ((988782639059731/1649267441664000):ℝ)≤a) (au : a≤((990393251795731/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-1306116845170417503237334216819565/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR035Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (988782639059731/1649267441664000) (990393251795731/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR035Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR035Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR035Q00U (-1306116845170417503237334216819565/162259276829213363391578010288128) factoredHeatR035Q00Samples (by decide +kernel)

theorem factored_original_heat_035 {t a : ℝ} (tb : RealMem derivative_035.t t) (ab : RealMem derivative_035.a a) : reportedHeatPeriod t a≤(derivative_035.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((177/200):ℝ) ((443/500):ℝ) := by simpa [derivative_035,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((177/200):ℝ)<((443/500):ℝ)) tB
  have aB : a∈Icc ((988782639059731/1649267441664000):ℝ) ((990393251795731/1649267441664000):ℝ) := by simpa [derivative_035,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((988782639059731/1649267441664000):ℝ)<((990393251795731/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR035Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_035] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR036Q00T := Grid.ofRats (443/500) (887/1000)
def factoredHeatR036Q00P : HeatGridParameters := ⟨⟨⟨⟨74507128709682527303884,74741567821222509830710,true⟩,⟨0,0,true⟩⟩, ⟨⟨1139125472178228194748137,1140979941159564657676157,true⟩,⟨0,0,true⟩⟩, ⟨(-1519701529279847831554992),(-1515992591317243625178116),true⟩, ⟨6072875140069242470193280,6109680878945761172152413,true⟩⟩, ⟨392841201510916080492638,417070842773012740154327,true⟩, ⟨596496767470827140090861,603220841382279308564775,true⟩, ⟨(-1445334506683960826693886),(-1432055415518761966741947),true⟩, ⟨(-2696224829430494198109763),(-2689246894689202860457658),true⟩, ⟨(-596785395004363868579779),(-595328898472329926422463),true⟩⟩
theorem factoredHeatR036Q00P_ok : factoredHeatR036Q00P.encloses (heatGridParameters factoredHeatR036Q00T (Grid.ofRats (989334419677433/1649267441664000) (990945032413433/1649267441664000))) := by decide +kernel
def factoredHeatR036Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨602350391090447335113437,602823661810049111628871,true⟩,⟨2424426461533766848322594,2426331349573881229582082,true⟩,⟨⟨709121839601488417099249,710976308582824880075018,true⟩,⟨977506181594337501901636,979360650575673964881181,true⟩⟩⟩
  | 1 => ⟨⟨9216084708595689830959,9266892317426242059841,true⟩,⟨602350391090447335113437,602823661810049111628871,true⟩,⟨⟨(-1153155217022161427203917),(-1147591810078289477304832),true⟩,⟨368893445889723898725050,374456852833595848613403,true⟩⟩⟩
  | 2 => ⟨⟨8690442521723158387,8807253450510126578,true⟩,⟨9216084708595689830959,9266892317426242059841,true⟩,⟨⟨(-1301353792520763968464),7970991113886672841068,true⟩,⟨(-1213557392514876421513669),(-1204285047608468984687562),true⟩⟩⟩
  | 3 => ⟨⟨505016951197500,517533246003617,true⟩,⟨8690442521723158387,8807253450510126578,true⟩,⟨⟨1141814843001939602083382,1154796125870882525795094,true⟩,⟨371525431959454773210871,384506714828397696911990,true⟩⟩⟩
  | 4 => ⟨⟨(-32550785355),36239664985,true⟩,⟨505016951197500,517533246003617,true⟩,⟨⟨(-723781369962836117896892),(-707091149131357707251326),true⟩,⟨966156093203918670375273,982846314035397081024402,true⟩⟩⟩
  | _ => ⟨⟨(-34359737969),34359738791,true⟩,⟨(-32550785355),36239664985,true⟩,⟨⟨(-714839856106992367124811),(-694440697312978469576687),true⟩,⟨(-992535427144088862939626),(-972136268350074965387676),true⟩⟩⟩
theorem factoredHeatR036Q00F_ok : ∀ n : Fin 6, (factoredHeatR036Q00F n).encloses (FactoredFrequency.build factoredHeatR036Q00T (Grid.ofRats (989334419677433/1649267441664000) (990945032413433/1649267441664000)) n) := by decide +kernel
def factoredHeatR036Q00U : ℕ → ℚ
  | 0 => (-20845037/500000)
  | 1 => (-31729633/1000000)
  | 2 => (-5167421/250000)
  | 3 => (-12905613/1000000)
  | 4 => (-8247489/1000000)
  | 5 => (-5680297/1000000)
  | 6 => (-1052969/250000)
  | 7 => (-3463999/1000000)
  | 8 => (-3258241/1000000)
  | 9 => (-942503/250000)
  | 10 => (-2866299/500000)
  | 11 => (-9681547/1000000)
  | 12 => (-7555023/500000)
  | 13 => (-1300493/62500)
  | 14 => (-24035211/1000000)
  | 15 => (-1427851/62500)
  | 16 => (-18961047/1000000)
  | 17 => (-14778213/1000000)
  | 18 => (-1515979/125000)
  | 19 => (-2180033/200000)
  | 20 => (-2619271/250000)
  | 21 => (-10115821/1000000)
  | 22 => (-1779169/200000)
  | 23 => (-580159/100000)
  | 24 => (277277/500000)
  | 25 => (134641/12500)
  | 26 => (11833319/500000)
  | 27 => (340047/10000)
  | 28 => (32597983/1000000)
  | 29 => (12365453/1000000)
  | 30 => (-9219459/500000)
  | 31 => (-1584341/40000)
  | _ => 0
theorem factoredHeatR036Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR036Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR036Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR036Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR036Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR036Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR036Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR036Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR036Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR036Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR036Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR036Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR036Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR036Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR036Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR036Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR036Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR036Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR036Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR036Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR036Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR036Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR036Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR036Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR036Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR036Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR036Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR036Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR036Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR036Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR036Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR036Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR036Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR036Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR036Q00P factoredHeatR036Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR036Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR036Q00Point00
  · exact factoredHeatR036Q00Point01
  · exact factoredHeatR036Q00Point02
  · exact factoredHeatR036Q00Point03
  · exact factoredHeatR036Q00Point04
  · exact factoredHeatR036Q00Point05
  · exact factoredHeatR036Q00Point06
  · exact factoredHeatR036Q00Point07
  · exact factoredHeatR036Q00Point08
  · exact factoredHeatR036Q00Point09
  · exact factoredHeatR036Q00Point10
  · exact factoredHeatR036Q00Point11
  · exact factoredHeatR036Q00Point12
  · exact factoredHeatR036Q00Point13
  · exact factoredHeatR036Q00Point14
  · exact factoredHeatR036Q00Point15
  · exact factoredHeatR036Q00Point16
  · exact factoredHeatR036Q00Point17
  · exact factoredHeatR036Q00Point18
  · exact factoredHeatR036Q00Point19
  · exact factoredHeatR036Q00Point20
  · exact factoredHeatR036Q00Point21
  · exact factoredHeatR036Q00Point22
  · exact factoredHeatR036Q00Point23
  · exact factoredHeatR036Q00Point24
  · exact factoredHeatR036Q00Point25
  · exact factoredHeatR036Q00Point26
  · exact factoredHeatR036Q00Point27
  · exact factoredHeatR036Q00Point28
  · exact factoredHeatR036Q00Point29
  · exact factoredHeatR036Q00Point30
  · exact factoredHeatR036Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR036Q00Bound {t a : ℝ} (tl : ((443/500):ℝ)≤t) (tu : t≤((887/1000):ℝ)) (al : ((989334419677433/1649267441664000):ℝ)≤a) (au : a≤((990945032413433/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-1306856723656014456600963815831477/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR036Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (989334419677433/1649267441664000) (990945032413433/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR036Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR036Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR036Q00U (-1306856723656014456600963815831477/162259276829213363391578010288128) factoredHeatR036Q00Samples (by decide +kernel)

theorem factored_original_heat_036 {t a : ℝ} (tb : RealMem derivative_036.t t) (ab : RealMem derivative_036.a a) : reportedHeatPeriod t a≤(derivative_036.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((443/500):ℝ) ((887/1000):ℝ) := by simpa [derivative_036,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((443/500):ℝ)<((887/1000):ℝ)) tB
  have aB : a∈Icc ((989334419677433/1649267441664000):ℝ) ((990945032413433/1649267441664000):ℝ) := by simpa [derivative_036,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((989334419677433/1649267441664000):ℝ)<((990945032413433/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR036Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_036] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR037Q00T := Grid.ofRats (887/1000) (111/125)
def factoredHeatR037Q00P : HeatGridParameters := ⟨⟨⟨⟨74273424954701496380478,74507128709751246781613,true⟩,⟨0,0,true⟩⟩, ⟨⟨1139761942189039665573425,1141616411170376128501447,true⟩,⟨0,0,true⟩⟩, ⟨(-1518428589258224889904413),(-1514719651295620683527541),true⟩, ⟨6064790260035503076475964,6101493916123814560880751,true⟩⟩, ⟨393581043713589668502511,417791009557930339829327,true⟩, ⟨596440374281586327523305,603152467559621353020703,true⟩, ⟨(-1443420307990993985600589),(-1430180420594166950999342),true⟩, ⟨(-2692451967466266473716493),(-2685496379552150581532790),true⟩, ⟨(-596285512626814985324349),(-594829016094781043167037),true⟩⟩
theorem factoredHeatR037Q00P_ok : factoredHeatR037Q00P.encloses (heatGridParameters factoredHeatR037Q00T (Grid.ofRats (989887196087203/1649267441664000) (991497808823203/1649267441664000))) := by decide +kernel
def factoredHeatR037Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨601877491930937809369816,602350391090516054611816,true⟩,⟨2426331349573812510018346,2428237734297164218007508,true⟩,⟨⟨708606619848732256553875,710461088830068719529356,true⟩,⟨977879869527880118477034,979734338509216581456297,true⟩⟩⟩
  | 1 => ⟨⟨9165555662810492809650,9216084708664409308157,true⟩,⟨601877491930937809369816,602350391090516054611816,true⟩,⟨⟨(-1153740815674889143442483),(-1148177408731017193543719),true⟩,⟨367076052115117758247023,372639459058989708135033,true⟩⟩⟩
  | 2 => ⟨⟨8575180927514724176,8690442590442635125,true⟩,⟨9165555662810492809650,9216084708664409308157,true⟩,⟨⟨1880968924319270449176,11153313830726707260115,true⟩,⟨(-1213544425464642256820154),(-1204272080558234819992665),true⟩⟩⟩
  | 3 => ⟨⟨492868781597665,505085670674237,true⟩,⟨8575180927514724176,8690442590442635125,true⟩,⟨⟨1140413934405611834802395,1153395217274554758514565,true⟩,⟨375754739502933117091027,388736022371876040792679,true⟩⟩⟩
  | 4 => ⟨⟨(-32619079464),36168691382,true⟩,⟨492868781597665,505085670674237,true⟩,⟨⟨(-728390781882152567932677),(-711700561050674157287074),true⟩,⟨962755228546916512941841,979445449378394923590897,true⟩⟩⟩
  | _ => ⟨⟨(-34359737991),34359738768,true⟩,⟨(-32619079464),36168691382,true⟩,⟨⟨(-709139136715850088807964),(-688739977921836191259838),true⟩,⟨(-996599666859413099087659),(-976200508065399201535578),true⟩⟩⟩
theorem factoredHeatR037Q00F_ok : ∀ n : Fin 6, (factoredHeatR037Q00F n).encloses (FactoredFrequency.build factoredHeatR037Q00T (Grid.ofRats (989887196087203/1649267441664000) (991497808823203/1649267441664000)) n) := by decide +kernel
def factoredHeatR037Q00U : ℕ → ℚ
  | 0 => (-41514433/1000000)
  | 1 => (-6338147/200000)
  | 2 => (-20707521/1000000)
  | 3 => (-1296553/100000)
  | 4 => (-1660649/200000)
  | 5 => (-35779/6250)
  | 6 => (-1060981/250000)
  | 7 => (-870981/250000)
  | 8 => (-1632477/500000)
  | 9 => (-752563/200000)
  | 10 => (-1426807/250000)
  | 11 => (-2407977/250000)
  | 12 => (-15033389/1000000)
  | 13 => (-20713669/1000000)
  | 14 => (-1197547/50000)
  | 15 => (-11402917/500000)
  | 16 => (-18963881/1000000)
  | 17 => (-14804661/1000000)
  | 18 => (-6078741/500000)
  | 19 => (-10921901/1000000)
  | 20 => (-10487287/1000000)
  | 21 => (-5056787/500000)
  | 22 => (-222051/25000)
  | 23 => (-2889607/500000)
  | 24 => (22843/40000)
  | 25 => (10759541/1000000)
  | 26 => (23600039/1000000)
  | 27 => (1694281/50000)
  | 28 => (324979/10000)
  | 29 => (6206943/500000)
  | 30 => (-18199299/1000000)
  | 31 => (-19660757/500000)
  | _ => 0
theorem factoredHeatR037Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR037Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR037Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR037Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR037Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR037Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR037Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR037Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR037Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR037Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR037Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR037Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR037Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR037Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR037Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR037Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR037Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR037Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR037Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR037Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR037Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR037Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR037Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR037Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR037Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR037Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR037Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR037Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR037Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR037Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR037Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR037Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR037Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR037Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR037Q00P factoredHeatR037Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR037Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR037Q00Point00
  · exact factoredHeatR037Q00Point01
  · exact factoredHeatR037Q00Point02
  · exact factoredHeatR037Q00Point03
  · exact factoredHeatR037Q00Point04
  · exact factoredHeatR037Q00Point05
  · exact factoredHeatR037Q00Point06
  · exact factoredHeatR037Q00Point07
  · exact factoredHeatR037Q00Point08
  · exact factoredHeatR037Q00Point09
  · exact factoredHeatR037Q00Point10
  · exact factoredHeatR037Q00Point11
  · exact factoredHeatR037Q00Point12
  · exact factoredHeatR037Q00Point13
  · exact factoredHeatR037Q00Point14
  · exact factoredHeatR037Q00Point15
  · exact factoredHeatR037Q00Point16
  · exact factoredHeatR037Q00Point17
  · exact factoredHeatR037Q00Point18
  · exact factoredHeatR037Q00Point19
  · exact factoredHeatR037Q00Point20
  · exact factoredHeatR037Q00Point21
  · exact factoredHeatR037Q00Point22
  · exact factoredHeatR037Q00Point23
  · exact factoredHeatR037Q00Point24
  · exact factoredHeatR037Q00Point25
  · exact factoredHeatR037Q00Point26
  · exact factoredHeatR037Q00Point27
  · exact factoredHeatR037Q00Point28
  · exact factoredHeatR037Q00Point29
  · exact factoredHeatR037Q00Point30
  · exact factoredHeatR037Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR037Q00Bound {t a : ℝ} (tl : ((887/1000):ℝ)≤t) (tu : t≤((111/125):ℝ)) (al : ((989887196087203/1649267441664000):ℝ)≤a) (au : a≤((991497808823203/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-1307358171361744812635241021560323/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR037Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (989887196087203/1649267441664000) (991497808823203/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR037Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR037Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR037Q00U (-1307358171361744812635241021560323/162259276829213363391578010288128) factoredHeatR037Q00Samples (by decide +kernel)

theorem factored_original_heat_037 {t a : ℝ} (tb : RealMem derivative_037.t t) (ab : RealMem derivative_037.a a) : reportedHeatPeriod t a≤(derivative_037.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((887/1000):ℝ) ((111/125):ℝ) := by simpa [derivative_037,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((887/1000):ℝ)<((111/125):ℝ)) tB
  have aB : a∈Icc ((989887196087203/1649267441664000):ℝ) ((991497808823203/1649267441664000):ℝ) := by simpa [derivative_037,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((989887196087203/1649267441664000):ℝ)<((991497808823203/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR037Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_037] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_033
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_034
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_035
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_036
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_037
