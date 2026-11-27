import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR043Q00T := Grid.ofRats (893/1000) (447/500)
def factoredHeatR043Q00P : HeatGridParameters := ⟨⟨⟨⟨72886516248617326678596,73115856050171930140608,true⟩,⟨0,0,true⟩⟩, ⟨⟨1143604901337155047464811,1145459370318491510392845,true⟩,⟨0,0,true⟩⟩, ⟨(-1510742670961994126121616),(-1507033732999389919744768),true⟩, ⟨6016547159410547078812352,6052645441432115575183513,true⟩⟩, ⟨398033308637241658060560,422128572662544753450660,true⟩, ⟨596034331244088454877180,602675168694769516083638,true⟩, ⟨(-1432095322625849991948248),(-1419087740774842067639059),true⟩, ⟨(-2669954148345838587614989),(-2663131038548445266778159),true⟩, ⟨(-593267259569873741857454),(-591810763037839799700160),true⟩⟩
theorem factoredHeatR043Q00P_ok : factoredHeatR043Q00P.encloses (heatGridParameters factoredHeatR043Q00T (Grid.ofRats (66214987961551/109951162777600) (66322362143951/109951162777600))) := by decide +kernel
def factoredHeatR043Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨599047883414748404464983,599518559332043981938983,true⟩,⟨2437792149352814060917699,2439707538902987600575181,true⟩,⟨⟨705491587332899633476244,707346056314236096451987,true⟩,⟨980130401687912866742027,981984870669249329721687,true⟩⟩⟩
  | 1 => ⟨⟨8868146266641641653542,8917035715994400766743,true⟩,⟨599047883414748404464983,599518559332043981938983,true⟩,⟨⟨(-1157215561250879699296937),(-1151652154307007749397813),true⟩,⟨356083320380387159792594,361646727324259109680760,true⟩⟩⟩
  | 2 => ⟨⟨7915014135524496326,8021402297446822852,true⟩,⟨8868146266641641653542,8917035715994400766743,true⟩,⟨⟨21093853294720952889128,30366198201128389699374,true⟩,⟨(-1213288150115059055048960),(-1204015805208651618222433),true⟩⟩⟩
  | 3 => ⟨⟨425875883936142,436441655349779,true⟩,⟨7915014135524496326,8021402297446822852,true⟩,⟨⟨1131625080340066278780062,1144606363209009202492437,true⟩,⟨401178637737415511907035,414159920606358435609356,true⟩⟩⟩
  | 4 => ⟨⟨(-32977980285),35795709220,true⟩,⟨425875883936142,436441655349779,true⟩,⟨⟨(-755874924419513536664265),(-739184703588035126018561),true⟩,⟨941760575551030215626291,958450796382508626274780,true⟩⟩⟩
  | _ => ⟨⟨(-34359738098),34359738654,true⟩,⟨(-32977980285),35795709220,true⟩,⟨⟨(-674227428436097216808448),(-653828269642083319260080),true⟩,⟨(-1020431559207298870027699),(-1000032400413284972474564),true⟩⟩⟩
theorem factoredHeatR043Q00F_ok : ∀ n : Fin 6, (factoredHeatR043Q00F n).encloses (FactoredFrequency.build factoredHeatR043Q00T (Grid.ofRats (66214987961551/109951162777600) (66322362143951/109951162777600)) n) := by decide +kernel
def factoredHeatR043Q00U : ℕ → ℚ
  | 0 => (-10112063/250000)
  | 1 => (-31436979/1000000)
  | 2 => (-1307067/62500)
  | 3 => (-13309541/1000000)
  | 4 => (-2156947/250000)
  | 5 => (-5984083/1000000)
  | 6 => (-4431549/1000000)
  | 7 => (-22501/6250)
  | 8 => (-1651641/500000)
  | 9 => (-3719243/1000000)
  | 10 => (-2778231/500000)
  | 11 => (-9338371/1000000)
  | 12 => (-14580333/1000000)
  | 13 => (-10077827/500000)
  | 14 => (-23448239/1000000)
  | 15 => (-11280677/500000)
  | 16 => (-3794037/200000)
  | 17 => (-7476413/500000)
  | 18 => (-12327281/1000000)
  | 19 => (-11046483/1000000)
  | 20 => (-10544171/1000000)
  | 21 => (-10096967/1000000)
  | 22 => (-4398757/500000)
  | 23 => (-5645137/1000000)
  | 24 => (334183/500000)
  | 25 => (333989/31250)
  | 26 => (232037/10000)
  | 27 => (6636307/200000)
  | 28 => (31906289/1000000)
  | 29 => (12691117/1000000)
  | 30 => (-8400077/500000)
  | 31 => (-2351877/62500)
  | _ => 0
theorem factoredHeatR043Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR043Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR043Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR043Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR043Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR043Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR043Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR043Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR043Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR043Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR043Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR043Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR043Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR043Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR043Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR043Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR043Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR043Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR043Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR043Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR043Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR043Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR043Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR043Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR043Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR043Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR043Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR043Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR043Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR043Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR043Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR043Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR043Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR043Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR043Q00P factoredHeatR043Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR043Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR043Q00Point00
  · exact factoredHeatR043Q00Point01
  · exact factoredHeatR043Q00Point02
  · exact factoredHeatR043Q00Point03
  · exact factoredHeatR043Q00Point04
  · exact factoredHeatR043Q00Point05
  · exact factoredHeatR043Q00Point06
  · exact factoredHeatR043Q00Point07
  · exact factoredHeatR043Q00Point08
  · exact factoredHeatR043Q00Point09
  · exact factoredHeatR043Q00Point10
  · exact factoredHeatR043Q00Point11
  · exact factoredHeatR043Q00Point12
  · exact factoredHeatR043Q00Point13
  · exact factoredHeatR043Q00Point14
  · exact factoredHeatR043Q00Point15
  · exact factoredHeatR043Q00Point16
  · exact factoredHeatR043Q00Point17
  · exact factoredHeatR043Q00Point18
  · exact factoredHeatR043Q00Point19
  · exact factoredHeatR043Q00Point20
  · exact factoredHeatR043Q00Point21
  · exact factoredHeatR043Q00Point22
  · exact factoredHeatR043Q00Point23
  · exact factoredHeatR043Q00Point24
  · exact factoredHeatR043Q00Point25
  · exact factoredHeatR043Q00Point26
  · exact factoredHeatR043Q00Point27
  · exact factoredHeatR043Q00Point28
  · exact factoredHeatR043Q00Point29
  · exact factoredHeatR043Q00Point30
  · exact factoredHeatR043Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR043Q00Bound {t a : ℝ} (tl : ((893/1000):ℝ)≤t) (tu : t≤((447/500):ℝ)) (al : ((66214987961551/109951162777600):ℝ)≤a) (au : a≤((66322362143951/109951162777600):ℝ)) : reportedHeatPeriod t a≤(((-2612755682219241866526676036567795/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR043Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (66214987961551/109951162777600) (66322362143951/109951162777600)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR043Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR043Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR043Q00U (-2612755682219241866526676036567795/324518553658426726783156020576256) factoredHeatR043Q00Samples (by decide +kernel)

theorem factored_original_heat_043 {t a : ℝ} (tb : RealMem derivative_043.t t) (ab : RealMem derivative_043.a a) : reportedHeatPeriod t a≤(derivative_043.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((893/1000):ℝ) ((447/500):ℝ) := by simpa [derivative_043,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((893/1000):ℝ)<((447/500):ℝ)) tB
  have aB : a∈Icc ((66214987961551/109951162777600):ℝ) ((66322362143951/109951162777600):ℝ) := by simpa [derivative_043,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((66214987961551/109951162777600):ℝ)<((66322362143951/109951162777600):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR043Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_043] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR044Q00T := Grid.ofRats (447/500) (179/200)
def factoredHeatR044Q00P : HeatGridParameters := ⟨⟨⟨⟨72657895808804641427383,72886516248686046156309,true⟩,⟨0,0,true⟩⟩, ⟨⟨1144249428163461033934637,1146103897144797496862674,true⟩,⟨0,0,true⟩⟩, ⟨(-1509453617309382153181959),(-1505744679346777946805116),true⟩, ⟨6008550954584633051679609,6044549517407379646121143,true⟩⟩, ⟨398777692345270977816964,422854228574074118407068,true⟩, ⟨595955418597667645430566,602584453867143892202236,true⟩, ⟨(-1430234334407414197312009),(-1417264988651053403524921),true⟩, ⟨(-2666227815072895903116497),(-2659426520755624884244233),true⟩, ⟨(-592761049384232633910529),(-591304552852198691753239),true⟩⟩
theorem factoredHeatR044Q00P_ok : factoredHeatR044Q00P.encloses (heatGridParameters factoredHeatR044Q00T (Grid.ofRats (331261531068403/549755813888000) (331798401980403/549755813888000))) := by decide +kernel
def factoredHeatR044Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨598577577020392204876268,599047883414817123963331,true⟩,⟨2439707538902918881010814,2441624433387436238565095,true⟩,⟨⟨704968445800672518112340,706822914782008981087910,true⟩,⟨980506882440737493227092,982361351422073956206493,true⟩⟩⟩
  | 1 => ⟨⟨8819524863637490596877,8868146266710361130723,true⟩,⟨598577577020392204876268,599047883414817123963331,true⟩,⟨⟨(-1157788060400448166379834),(-1152224653456576216480514),true⟩,⟨354236437223504339946736,359799844167376289835053,true⟩⟩⟩
  | 2 => ⟨⟨7810037070718442373,7915014204243973064,true⟩,⟨8819524863637490596877,8868146266710361130723,true⟩,⟨⟨24315662211642023865500,33588007118049460675911,true⟩,⟨(-1213215267341263725614594),(-1203942922434856288787948),true⟩⟩⟩
  | 3 => ⟨⟨415631321131469,425944603412879,true⟩,⟨7810037070718442373,7915014204243973064,true⟩,⟨⟨1130095744357725093267559,1143077027226668016980417,true⟩,⟨405423214805804892099879,418404497674747815802763,true⟩⟩⟩
  | 4 => ⟨⟨(-33030146337),35741496452,true⟩,⟨415631321131469,425944603412879,true⟩,⟨⟨(-760425156559445197039805),(-743734935727966786392910),true⟩,⟨938162809003524811042677,954853029835003221692245,true⟩⟩⟩
  | _ => ⟨⟨(-34359738113),34359738639,true⟩,⟨(-33030146337),35741496452,true⟩,⟨⟨(-668291496616297686844801),(-647892337822283789296341),true⟩,⟨(-1024308383136300548624677),(-1003909224342286651071314),true⟩⟩⟩
theorem factoredHeatR044Q00F_ok : ∀ n : Fin 6, (factoredHeatR044Q00F n).encloses (FactoredFrequency.build factoredHeatR044Q00T (Grid.ofRats (331261531068403/549755813888000) (331798401980403/549755813888000)) n) := by decide +kernel
def factoredHeatR044Q00U : ℕ → ℚ
  | 0 => (-20135239/500000)
  | 1 => (-156957/5000)
  | 2 => (-20943811/1000000)
  | 3 => (-13364313/1000000)
  | 4 => (-4340107/500000)
  | 5 => (-301311/50000)
  | 6 => (-892409/200000)
  | 7 => (-3618983/1000000)
  | 8 => (-3309351/1000000)
  | 9 => (-1855961/500000)
  | 10 => (-1382903/250000)
  | 11 => (-9290161/1000000)
  | 12 => (-14505963/1000000)
  | 13 => (-20063863/1000000)
  | 14 => (-11682477/500000)
  | 15 => (-22519681/1000000)
  | 16 => (-18969493/1000000)
  | 17 => (-1497579/100000)
  | 18 => (-12354241/1000000)
  | 19 => (-276657/25000)
  | 20 => (-1319117/125000)
  | 21 => (-1261711/125000)
  | 22 => (-548947/62500)
  | 23 => (-5622829/1000000)
  | 24 => (27371/40000)
  | 25 => (427017/40000)
  | 26 => (11569091/500000)
  | 27 => (33065891/1000000)
  | 28 => (3180913/100000)
  | 29 => (12735133/1000000)
  | 30 => (-16573269/1000000)
  | 31 => (-3735317/100000)
  | _ => 0
theorem factoredHeatR044Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR044Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR044Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR044Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR044Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR044Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR044Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR044Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR044Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR044Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR044Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR044Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR044Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR044Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR044Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR044Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR044Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR044Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR044Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR044Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR044Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR044Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR044Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR044Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR044Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR044Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR044Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR044Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR044Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR044Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR044Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR044Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR044Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR044Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR044Q00P factoredHeatR044Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR044Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR044Q00Point00
  · exact factoredHeatR044Q00Point01
  · exact factoredHeatR044Q00Point02
  · exact factoredHeatR044Q00Point03
  · exact factoredHeatR044Q00Point04
  · exact factoredHeatR044Q00Point05
  · exact factoredHeatR044Q00Point06
  · exact factoredHeatR044Q00Point07
  · exact factoredHeatR044Q00Point08
  · exact factoredHeatR044Q00Point09
  · exact factoredHeatR044Q00Point10
  · exact factoredHeatR044Q00Point11
  · exact factoredHeatR044Q00Point12
  · exact factoredHeatR044Q00Point13
  · exact factoredHeatR044Q00Point14
  · exact factoredHeatR044Q00Point15
  · exact factoredHeatR044Q00Point16
  · exact factoredHeatR044Q00Point17
  · exact factoredHeatR044Q00Point18
  · exact factoredHeatR044Q00Point19
  · exact factoredHeatR044Q00Point20
  · exact factoredHeatR044Q00Point21
  · exact factoredHeatR044Q00Point22
  · exact factoredHeatR044Q00Point23
  · exact factoredHeatR044Q00Point24
  · exact factoredHeatR044Q00Point25
  · exact factoredHeatR044Q00Point26
  · exact factoredHeatR044Q00Point27
  · exact factoredHeatR044Q00Point28
  · exact factoredHeatR044Q00Point29
  · exact factoredHeatR044Q00Point30
  · exact factoredHeatR044Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR044Q00Bound {t a : ℝ} (tl : ((447/500):ℝ)≤t) (tu : t≤((179/200):ℝ)) (al : ((331261531068403/549755813888000):ℝ)≤a) (au : a≤((331798401980403/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-5100277621938573778458069256005/633825300114114700748351602688):ℚ):ℝ) := by
  have ts : factoredHeatR044Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (331261531068403/549755813888000) (331798401980403/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR044Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR044Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR044Q00U (-5100277621938573778458069256005/633825300114114700748351602688) factoredHeatR044Q00Samples (by decide +kernel)

theorem factored_original_heat_044 {t a : ℝ} (tb : RealMem derivative_044.t t) (ab : RealMem derivative_044.a a) : reportedHeatPeriod t a≤(derivative_044.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((447/500):ℝ) ((179/200):ℝ) := by simpa [derivative_044,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((447/500):ℝ)<((179/200):ℝ)) tB
  have aB : a∈Icc ((331261531068403/549755813888000):ℝ) ((331798401980403/549755813888000):ℝ) := by simpa [derivative_044,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((331261531068403/549755813888000):ℝ)<((331798401980403/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR044Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_044] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR045Q00T := Grid.ofRats (179/200) (112/125)
def factoredHeatR045Q00P : HeatGridParameters := ⟨⟨⟨⟨72429992474270000145265,72657895808873360905094,true⟩,⟨0,0,true⟩⟩, ⟨⟨1144895110513509207027710,1146749579494845669955749,true⟩,⟨0,0,true⟩⟩, ⟨(-1508162252609285806995809),(-1504453314646681600618969),true⟩, ⟨6000567394775989431349606,6036466571520391547225622,true⟩⟩, ⟨399522767327240182731975,423580676794424104017014,true⟩, ⟨595873306757754433309778,602490559121764820367239,true⟩, ⟨(-1428380865647947825236785),(-1415449619733850147661189),true⟩, ⟨(-2662508160988816863288365),(-2655728607492203347410569),true⟩, ⟨(-592253931652366650443145),(-590797435120332708285859),true⟩⟩
theorem factoredHeatR045Q00P_ok : factoredHeatR045Q00P.encloses (heatGridParameters factoredHeatR045Q00T (Grid.ofRats (331448456854509/549755813888000) (331985327766509/549755813888000))) := by decide +kernel
def factoredHeatR045Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨598107639858798020034844,598577577020460924374602,true⟩,⟨2441624433387367519000821,2443542833988665645240855,true⟩,⟨⟨704444165184845453994305,706298634166181916969877,true⟩,⟨980883758445706284638688,982738227427042747618142,true⟩⟩⟩
  | 1 => ⟨⟨8771170037295361395863,8819524863706210074056,true⟩,⟨598107639858798020034844,598577577020460924374602,true⟩,⟨⟨(-1158358623315912364723561),(-1152795216372040414824386),true⟩,⟨352385327169720126513685,357948734113592076401833,true⟩⟩⟩
  | 2 => ⟨⟨7706452319798221379,7810037139437919111,true⟩,⟨8771170037295361395863,8819524863706210074056,true⟩,⟨⟨27543040970073392812221,36815385876480829623508,true⟩,⟨(-1213133642684052857192799),(-1203861297777645420365324),true⟩⟩⟩
  | 3 => ⟨⟨405633174252727,415700040608206,true⟩,⟨7706452319798221379,7810037139437919111,true⟩,⟨⟨1128547793967829370335580,1141529076836772294048712,true⟩,⟨409669649187303117739755,422650932056246041442996,true⟩⟩⟩
  | 4 => ⟨⟨(-33080342944),35689330400,true⟩,⟨405633174252727,415700040608206,true⟩,⟨⟨(-764966184476635546775627),(-748275963645157136129903),true⟩,⟨934536742001539282861836,951226962833017693510122,true⟩⟩⟩
  | _ => ⟨⟨(-34359738127),34359738624,true⟩,⟨(-33080342944),35689330400,true⟩,⟨⟨(-662322228343114142975972),(-641923069549100245427815),true⟩,⟨(-1028157185617627098900389),(-1007758026823613201347196),true⟩⟩⟩
theorem factoredHeatR045Q00F_ok : ∀ n : Fin 6, (factoredHeatR045Q00F n).encloses (FactoredFrequency.build factoredHeatR045Q00T (Grid.ofRats (331448456854509/549755813888000) (331985327766509/549755813888000)) n) := by decide +kernel
def factoredHeatR045Q00U : ℕ → ℚ
  | 0 => (-626449/15625)
  | 1 => (-1959057/62500)
  | 2 => (-524339/25000)
  | 3 => (-3354589/250000)
  | 4 => (-2183041/250000)
  | 5 => (-6068041/1000000)
  | 6 => (-4492319/1000000)
  | 7 => (-3637651/1000000)
  | 8 => (-3315329/1000000)
  | 9 => (-463073/125000)
  | 10 => (-2753421/500000)
  | 11 => (-1155269/125000)
  | 12 => (-2886383/200000)
  | 13 => (-9986207/500000)
  | 14 => (-11640907/500000)
  | 15 => (-22477753/1000000)
  | 16 => (-2371039/125000)
  | 17 => (-7499133/500000)
  | 18 => (-619041/50000)
  | 19 => (-11085801/1000000)
  | 20 => (-5280749/500000)
  | 21 => (-1261283/125000)
  | 22 => (-4384357/500000)
  | 23 => (-5600533/1000000)
  | 24 => (140019/200000)
  | 25 => (333223/31250)
  | 26 => (11536409/500000)
  | 27 => (16475363/500000)
  | 28 => (15856187/500000)
  | 29 => (1597317/125000)
  | 30 => (-4086963/250000)
  | 31 => (-4634717/125000)
  | _ => 0
theorem factoredHeatR045Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR045Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR045Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR045Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR045Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR045Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR045Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR045Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR045Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR045Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR045Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR045Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR045Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR045Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR045Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR045Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR045Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR045Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR045Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR045Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR045Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR045Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR045Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR045Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR045Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR045Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR045Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR045Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR045Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR045Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR045Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR045Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR045Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR045Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR045Q00P factoredHeatR045Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR045Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR045Q00Point00
  · exact factoredHeatR045Q00Point01
  · exact factoredHeatR045Q00Point02
  · exact factoredHeatR045Q00Point03
  · exact factoredHeatR045Q00Point04
  · exact factoredHeatR045Q00Point05
  · exact factoredHeatR045Q00Point06
  · exact factoredHeatR045Q00Point07
  · exact factoredHeatR045Q00Point08
  · exact factoredHeatR045Q00Point09
  · exact factoredHeatR045Q00Point10
  · exact factoredHeatR045Q00Point11
  · exact factoredHeatR045Q00Point12
  · exact factoredHeatR045Q00Point13
  · exact factoredHeatR045Q00Point14
  · exact factoredHeatR045Q00Point15
  · exact factoredHeatR045Q00Point16
  · exact factoredHeatR045Q00Point17
  · exact factoredHeatR045Q00Point18
  · exact factoredHeatR045Q00Point19
  · exact factoredHeatR045Q00Point20
  · exact factoredHeatR045Q00Point21
  · exact factoredHeatR045Q00Point22
  · exact factoredHeatR045Q00Point23
  · exact factoredHeatR045Q00Point24
  · exact factoredHeatR045Q00Point25
  · exact factoredHeatR045Q00Point26
  · exact factoredHeatR045Q00Point27
  · exact factoredHeatR045Q00Point28
  · exact factoredHeatR045Q00Point29
  · exact factoredHeatR045Q00Point30
  · exact factoredHeatR045Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR045Q00Bound {t a : ℝ} (tl : ((179/200):ℝ)≤t) (tu : t≤((112/125):ℝ)) (al : ((331448456854509/549755813888000):ℝ)≤a) (au : a≤((331985327766509/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-1304836875349211681145297411123133/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR045Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (331448456854509/549755813888000) (331985327766509/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR045Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR045Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR045Q00U (-1304836875349211681145297411123133/162259276829213363391578010288128) factoredHeatR045Q00Samples (by decide +kernel)

theorem factored_original_heat_045 {t a : ℝ} (tb : RealMem derivative_045.t t) (ab : RealMem derivative_045.a a) : reportedHeatPeriod t a≤(derivative_045.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((179/200):ℝ) ((112/125):ℝ) := by simpa [derivative_045,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((179/200):ℝ)<((112/125):ℝ)) tB
  have aB : a∈Icc ((331448456854509/549755813888000):ℝ) ((331985327766509/549755813888000):ℝ) := by simpa [derivative_045,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((331448456854509/549755813888000):ℝ)<((331985327766509/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR045Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_045] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR046Q00T := Grid.ofRats (112/125) (897/1000)
def factoredHeatR046Q00P : HeatGridParameters := ⟨⟨⟨⟨72202803995695799297555,72429992474338719622971,true⟩,⟨0,0,true⟩⟩, ⟨⟨1145541949550774487340583,1147396418532110950268623,true⟩,⟨0,0,true⟩⟩, ⟨(-1506868574534755246370059),(-1503159636572151039993224),true⟩, ⟨5992596473881339272000444,6028396596544666043482205,true⟩⟩, ⟨400268540646466586331173,424307924205785549685587,true⟩, ⟨595788000174352340876790,602393488889143370246550,true⟩, ⟨(-1426534895931386683107671),(-1413641614096182078161108),true⟩, ⟨(-2658795193602676126437539),(-2652037306573817172465496),true⟩, ⟨(-591745905460484725659778),(-590289408928450783502494),true⟩⟩
theorem factoredHeatR046Q00P_ok : factoredHeatR046Q00P.encloses (heatGridParameters factoredHeatR046Q00T (Grid.ofRats (994907152508701/1649267441664000) (996517765244701/1649267441664000))) := by decide +kernel
def factoredHeatR046Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨597638071640084967646795,598107639858866739533066,true⟩,⟨2443542833988596925676382,2445462741890041819991692,true⟩,⟨⟨703918743609028325084103,705773212590364788059721,true⟩,⟨981261028770293872516680,983115497751630335496144,true⟩⟩⟩
  | 1 => ⟨⟨8723080326054864099446,8771170037364080873039,true⟩,⟨597638071640084967646795,598107639858866739533066,true⟩,⟨⟨(-1158927233628477783941641),(-1153363826684605834042378),true⟩,⟨350529986725192646375556,356093393669064596263761,true⟩⟩⟩
  | 2 => ⟨⟨7604241416463977612,7706452388517698117,true⟩,⟨8723080326054864099446,8771170037364080873039,true⟩,⟨⟨30775971198586837929585,40048316104994274740102,true⟩,⟨(-1213043230283009621440409),(-1203770885376602184613747),true⟩⟩⟩
  | 3 => ⟨⟨395875516174503,405701893729464,true⟩,⟨7604241416463977612,7706452388517698117,true⟩,⟨⟨1126981162739391558392719,1139962445608334482106043,true⟩,⟨413917858091585741472498,426899140960528665176020,true⟩⟩⟩
  | 4 => ⟨⟨(-33128644458),35639133793,true⟩,⟨395875516174503,405701893729464,true⟩,⟨⟨(-769497817802965827094785),(-752807596971487416447933),true⟩,⟨930882334545276553368820,947572555376754964018117,true⟩⟩⟩
  | _ => ⟨⟨(-34359738140),34359738610,true⟩,⟨(-33128644458),35639133793,true⟩,⟨⟨(-656319697438210930479851),(-635920538644197032931427),true⟩,⟨(-1031977652362620921273079),(-1011578493568607023719481),true⟩⟩⟩
theorem factoredHeatR046Q00F_ok : ∀ n : Fin 6, (factoredHeatR046Q00F n).encloses (FactoredFrequency.build factoredHeatR046Q00T (Grid.ofRats (994907152508701/1649267441664000) (996517765244701/1649267441664000)) n) := by decide +kernel
def factoredHeatR046Q00U : ℕ → ℚ
  | 0 => (-39915033/1000000)
  | 1 => (-1251901/40000)
  | 2 => (-10501163/500000)
  | 3 => (-13471673/1000000)
  | 4 => (-8783639/1000000)
  | 5 => (-1221909/200000)
  | 6 => (-4522371/1000000)
  | 7 => (-1828081/500000)
  | 8 => (-3321217/1000000)
  | 9 => (-369723/100000)
  | 10 => (-109643/20000)
  | 11 => (-9194343/1000000)
  | 12 => (-14358187/1000000)
  | 13 => (-19881307/1000000)
  | 14 => (-11599409/500000)
  | 15 => (-11217787/500000)
  | 16 => (-2370831/125000)
  | 17 => (-3004051/200000)
  | 18 => (-12407019/1000000)
  | 19 => (-1388131/125000)
  | 20 => (-5284929/500000)
  | 21 => (-10086697/1000000)
  | 22 => (-8754201/1000000)
  | 23 => (-5578249/1000000)
  | 24 => (178957/250000)
  | 25 => (10650781/1000000)
  | 26 => (23007609/1000000)
  | 27 => (32836039/1000000)
  | 28 => (31616019/1000000)
  | 29 => (3205333/250000)
  | 30 => (-16123859/1000000)
  | 31 => (-18401863/500000)
  | _ => 0
theorem factoredHeatR046Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR046Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR046Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR046Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR046Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR046Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR046Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR046Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR046Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR046Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR046Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR046Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR046Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR046Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR046Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR046Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR046Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR046Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR046Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR046Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR046Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR046Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR046Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR046Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR046Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR046Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR046Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR046Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR046Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR046Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR046Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR046Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR046Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR046Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR046Q00P factoredHeatR046Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR046Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR046Q00Point00
  · exact factoredHeatR046Q00Point01
  · exact factoredHeatR046Q00Point02
  · exact factoredHeatR046Q00Point03
  · exact factoredHeatR046Q00Point04
  · exact factoredHeatR046Q00Point05
  · exact factoredHeatR046Q00Point06
  · exact factoredHeatR046Q00Point07
  · exact factoredHeatR046Q00Point08
  · exact factoredHeatR046Q00Point09
  · exact factoredHeatR046Q00Point10
  · exact factoredHeatR046Q00Point11
  · exact factoredHeatR046Q00Point12
  · exact factoredHeatR046Q00Point13
  · exact factoredHeatR046Q00Point14
  · exact factoredHeatR046Q00Point15
  · exact factoredHeatR046Q00Point16
  · exact factoredHeatR046Q00Point17
  · exact factoredHeatR046Q00Point18
  · exact factoredHeatR046Q00Point19
  · exact factoredHeatR046Q00Point20
  · exact factoredHeatR046Q00Point21
  · exact factoredHeatR046Q00Point22
  · exact factoredHeatR046Q00Point23
  · exact factoredHeatR046Q00Point24
  · exact factoredHeatR046Q00Point25
  · exact factoredHeatR046Q00Point26
  · exact factoredHeatR046Q00Point27
  · exact factoredHeatR046Q00Point28
  · exact factoredHeatR046Q00Point29
  · exact factoredHeatR046Q00Point30
  · exact factoredHeatR046Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR046Q00Bound {t a : ℝ} (tl : ((112/125):ℝ)≤t) (tu : t≤((897/1000):ℝ)) (al : ((994907152508701/1649267441664000):ℝ)≤a) (au : a≤((996517765244701/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2607766403756317954222433742509331/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR046Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (994907152508701/1649267441664000) (996517765244701/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR046Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR046Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR046Q00U (-2607766403756317954222433742509331/324518553658426726783156020576256) factoredHeatR046Q00Samples (by decide +kernel)

theorem factored_original_heat_046 {t a : ℝ} (tb : RealMem derivative_046.t t) (ab : RealMem derivative_046.a a) : reportedHeatPeriod t a≤(derivative_046.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((112/125):ℝ) ((897/1000):ℝ) := by simpa [derivative_046,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((112/125):ℝ)<((897/1000):ℝ)) tB
  have aB : a∈Icc ((994907152508701/1649267441664000):ℝ) ((996517765244701/1649267441664000):ℝ) := by simpa [derivative_046,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((994907152508701/1649267441664000):ℝ)<((996517765244701/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR046Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_046] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR047Q00T := Grid.ofRats (897/1000) (449/500)
def factoredHeatR047Q00P : HeatGridParameters := ⟨⟨⟨⟨71976328130819786685658,72202803995764518775258,true⟩,⟨0,0,true⟩⟩, ⟨⟨1146189946457126655874492,1148044415438463118802535,true⟩,⟨0,0,true⟩⟩, ⟨(-1505572580722050909302237),(-1501863642759446702925406),true⟩, ⟨5984638185625434754850552,6020339585084686814845910,true⟩⟩, ⟨401015019420362115857829,425035977748979201528508,true⟩, ⟨595699503277546735971120,602293247579738876292948,true⟩, ⟨(-1424696404855455447854512),(-1411840951822965105245798),true⟩, ⟨(-2655088920244023588544738),(-2648352625634860112210710),true⟩, ⟨(-591236969880348504187110),(-589780473348314562029830),true⟩⟩
theorem factoredHeatR047Q00P_ok : factoredHeatR047Q00P.encloses (heatGridParameters factoredHeatR047Q00T (Grid.ofRats (995469940067189/1649267441664000) (997080552803189/1649267441664000))) := by decide +kernel
def factoredHeatR047Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨597168872074599747946751,597638071640153687145412,true⟩,⟨2445462741889973100425546,2447384158275860540765192,true⟩,⟨⟨703392179180159941927993,705246648161496404903471,true⟩,⟨981638692486897858640634,983493161468234321620010,true⟩⟩⟩
  | 1 => ⟨⟨8675254276368908785417,8723080326123583576621,true⟩,⟨597168872074599747946751,597638071640153687145412,true⟩,⟨⟨(-1159493874927340043829661),(-1153930467983468093930608),true⟩,⟨348670412381457086690509,354233819325329036578464,true⟩⟩⟩
  | 2 => ⟨⟨7503386139334931296,7604241485183454349,true⟩,⟨8675254276368908785417,8723080326123583576621,true⟩,⟨⟨34014434367637014136419,43286779274044450947287,true⟩,⟨(-1212943984197911300416946),(-1203671639291503863589979),true⟩⟩⟩
  | 3 => ⟨⟨386352562338531,395944235651240,true⟩,⟨7503386139334931296,7604241485183454349,true⟩,⟨⟨1125395784385729351719752,1138377067254672275433199,true⟩,⟨418167758193834441281176,431149041062777364984895,true⟩⟩⟩
  | 4 => ⟨⟨(-33175122427),35590832279,true⟩,⟨386352562338531,395944235651240,true⟩,⟨⟨(-774019865281778228014395),(-757329644450299817368173),true⟩,⟨927199547573249565186591,943889768404727975835152,true⟩⟩⟩
  | _ => ⟨⟨(-34359738152),34359738597,true⟩,⟨(-33175122427),35590832279,true⟩,⟨⟨(-650283980174967642473742),(-629884821380953744925586),true⟩,⟨(-1035769468391229472649216),(-1015370309597215575095753),true⟩⟩⟩
theorem factoredHeatR047Q00F_ok : ∀ n : Fin 6, (factoredHeatR047Q00F n).encloses (FactoredFrequency.build factoredHeatR047Q00T (Grid.ofRats (995469940067189/1649267441664000) (997080552803189/1649267441664000)) n) := by decide +kernel
def factoredHeatR047Q00U : ℕ → ℚ
  | 0 => (-39737379/1000000)
  | 1 => (-31249251/1000000)
  | 2 => (-10515057/500000)
  | 3 => (-6762133/500000)
  | 4 => (-8834639/1000000)
  | 5 => (-3075367/500000)
  | 6 => (-2276101/500000)
  | 7 => (-3674517/1000000)
  | 8 => (-415877/125000)
  | 9 => (-184493/50000)
  | 10 => (-5457537/1000000)
  | 11 => (-1829347/200000)
  | 12 => (-7142389/500000)
  | 13 => (-19790541/1000000)
  | 14 => (-23115969/1000000)
  | 15 => (-22393147/1000000)
  | 16 => (-2370563/125000)
  | 17 => (-15041761/1000000)
  | 18 => (-12432839/1000000)
  | 19 => (-11124019/1000000)
  | 20 => (-2115603/200000)
  | 21 => (-5041493/500000)
  | 22 => (-4369807/500000)
  | 23 => (-5555979/1000000)
  | 24 => (365737/500000)
  | 25 => (265959/25000)
  | 26 => (22942553/1000000)
  | 27 => (16360913/500000)
  | 28 => (15760031/500000)
  | 29 => (6431763/500000)
  | 30 => (-1590161/100000)
  | 31 => (-36531133/1000000)
  | _ => 0
theorem factoredHeatR047Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR047Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR047Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR047Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR047Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR047Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR047Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR047Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR047Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR047Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR047Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR047Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR047Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR047Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR047Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR047Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR047Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR047Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR047Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR047Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR047Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR047Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR047Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR047Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR047Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR047Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR047Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR047Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR047Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR047Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR047Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR047Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR047Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR047Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR047Q00P factoredHeatR047Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR047Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR047Q00Point00
  · exact factoredHeatR047Q00Point01
  · exact factoredHeatR047Q00Point02
  · exact factoredHeatR047Q00Point03
  · exact factoredHeatR047Q00Point04
  · exact factoredHeatR047Q00Point05
  · exact factoredHeatR047Q00Point06
  · exact factoredHeatR047Q00Point07
  · exact factoredHeatR047Q00Point08
  · exact factoredHeatR047Q00Point09
  · exact factoredHeatR047Q00Point10
  · exact factoredHeatR047Q00Point11
  · exact factoredHeatR047Q00Point12
  · exact factoredHeatR047Q00Point13
  · exact factoredHeatR047Q00Point14
  · exact factoredHeatR047Q00Point15
  · exact factoredHeatR047Q00Point16
  · exact factoredHeatR047Q00Point17
  · exact factoredHeatR047Q00Point18
  · exact factoredHeatR047Q00Point19
  · exact factoredHeatR047Q00Point20
  · exact factoredHeatR047Q00Point21
  · exact factoredHeatR047Q00Point22
  · exact factoredHeatR047Q00Point23
  · exact factoredHeatR047Q00Point24
  · exact factoredHeatR047Q00Point25
  · exact factoredHeatR047Q00Point26
  · exact factoredHeatR047Q00Point27
  · exact factoredHeatR047Q00Point28
  · exact factoredHeatR047Q00Point29
  · exact factoredHeatR047Q00Point30
  · exact factoredHeatR047Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR047Q00Bound {t a : ℝ} (tl : ((897/1000):ℝ)≤t) (tu : t≤((449/500):ℝ)) (al : ((995469940067189/1649267441664000):ℝ)≤a) (au : a≤((997080552803189/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2605635286464105081927658777931497/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR047Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (995469940067189/1649267441664000) (997080552803189/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR047Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR047Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR047Q00U (-2605635286464105081927658777931497/324518553658426726783156020576256) factoredHeatR047Q00Samples (by decide +kernel)

theorem factored_original_heat_047 {t a : ℝ} (tb : RealMem derivative_047.t t) (ab : RealMem derivative_047.a a) : reportedHeatPeriod t a≤(derivative_047.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((897/1000):ℝ) ((449/500):ℝ) := by simpa [derivative_047,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((897/1000):ℝ)<((449/500):ℝ)) tB
  have aB : a∈Icc ((995469940067189/1649267441664000):ℝ) ((997080552803189/1649267441664000):ℝ) := by simpa [derivative_047,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((995469940067189/1649267441664000):ℝ)<((997080552803189/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR047Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_047] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_043
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_044
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_045
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_046
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_047
