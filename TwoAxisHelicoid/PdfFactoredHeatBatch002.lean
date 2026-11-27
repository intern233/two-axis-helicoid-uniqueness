import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR002Q00T := Grid.ofRats (213/250) (853/1000)
def factoredHeatR002Q00P : HeatGridParameters := ⟨⟨⟨⟨82906126226876535667510,83166993058143201374828,true⟩,⟨0,0,true⟩⟩, ⟨⟨1118161189620050647508907,1120015658601387110436860,true⟩,⟨0,0,true⟩⟩, ⟨(-1561630094396202926033586),(-1557921156433598719656576),true⟩, ⟨6355334323559105481079571,6395822229789683443148060,true⟩⟩, ⟨368018101030246286393818,392989514125719291804387,true⟩, ⟨596457654011146376548314,603602965346373559233398,true⟩, ⟨(-1515125783693683909407949),(-1500426889000482095063122),true⟩, ⟨(-2828365765190790907498191),(-2820579905563196091698236),true⟩, ⟨(-613250704022501673474460),(-611794207490467731317039),true⟩⟩
theorem factoredHeatR002Q00P_ok : factoredHeatR002Q00P.encloses (heatGridParameters factoredHeatR002Q00T (Grid.ofRats (323708955878011/549755813888000) (324245826790011/549755813888000))) := by decide +kernel
def factoredHeatR002Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨618651963525587533927196,619138042499371617660969,true⟩,⟨2360542459046919371941253,2362397153000218492438412,true⟩,⟨⟨725981485917063363276013,727835954898399826251602,true⟩,⟨965046548552172540788633,966901017533509003767703,true⟩⟩⟩
  | 1 => ⟨⟨11110327245646183549184,11171577676647452253054,true⟩,⟨618651963525587533927196,619138042499371617660969,true⟩,⟨⟨(-1132271630330454504181462),(-1126708223386582554282290),true⟩,⟨428210341067219505465553,433773748011091455355096,true⟩⟩⟩
  | 2 => ⟨⟨13683407958811095827,13867330842280425422,true⟩,⟨11110327245646183549184,11171577676647452253054,true⟩,⟨⟨(-106003604576953060968562),(-96731259670545624157423),true⟩,⟨(-1209304708207142959669064),(-1200032363300735522842740),true⟩⟩⟩
  | 3 => ⟨⟨1155675110299181,1184227630086253,true⟩,⟨13683407958811095827,13867330842280425422,true⟩,⟨⟨1179139240790529989775541,1192120523659472913482905,true⟩,⟨229694497187822267483323,242675780056765191177616,true⟩⟩⟩
  | 4 => ⟨⟨(-27665671632),41316444340,true⟩,⟨1155675110299181,1184227630086253,true⟩,⟨⟨(-563610753380861347049322),(-546920532549382936405025),true⟩,⟨1065517871101657371517412,1082208091933135782168845,true⟩⟩⟩
  | _ => ⟨⟨(-34359735709),34359741180,true⟩,⟨(-27665671632),41316444340,true⟩,⟨⟨(-888308714972848846631590),(-867909556178834949083953),true⟩,⟨(-841118337970401193228633),(-820719179176387295681645),true⟩⟩⟩
theorem factoredHeatR002Q00F_ok : ∀ n : Fin 6, (factoredHeatR002Q00F n).encloses (FactoredFrequency.build factoredHeatR002Q00T (Grid.ofRats (323708955878011/549755813888000) (324245826790011/549755813888000)) n) := by decide +kernel
def factoredHeatR002Q00U : ℕ → ℚ
  | 0 => (-5938431/125000)
  | 1 => (-32328781/1000000)
  | 2 => (-18725369/1000000)
  | 3 => (-5209193/500000)
  | 4 => (-6070161/1000000)
  | 5 => (-1993059/500000)
  | 6 => (-5979/2000)
  | 7 => (-2691603/1000000)
  | 8 => (-2955677/1000000)
  | 9 => (-999483/250000)
  | 10 => (-1328329/200000)
  | 11 => (-1149581/100000)
  | 12 => (-17924291/1000000)
  | 13 => (-24228669/1000000)
  | 14 => (-26916699/1000000)
  | 15 => (-12001613/500000)
  | 16 => (-9265143/500000)
  | 17 => (-6782709/500000)
  | 18 => (-1088671/100000)
  | 19 => (-9995503/1000000)
  | 20 => (-1000137/100000)
  | 21 => (-10093581/1000000)
  | 22 => (-4655183/500000)
  | 23 => (-408677/62500)
  | 24 => (-29709/500000)
  | 25 => (5561413/500000)
  | 26 => (26022781/1000000)
  | 27 => (38370571/1000000)
  | 28 => (36280207/1000000)
  | 29 => (10294371/1000000)
  | 30 => (-5558923/200000)
  | 31 => (-50196353/1000000)
  | _ => 0
theorem factoredHeatR002Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR002Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR002Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR002Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR002Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR002Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR002Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR002Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR002Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR002Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR002Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR002Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR002Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR002Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR002Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR002Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR002Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR002Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR002Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR002Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR002Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR002Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR002Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR002Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR002Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR002Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR002Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR002Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR002Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR002Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR002Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR002Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR002Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR002Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR002Q00P factoredHeatR002Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR002Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR002Q00Point00
  · exact factoredHeatR002Q00Point01
  · exact factoredHeatR002Q00Point02
  · exact factoredHeatR002Q00Point03
  · exact factoredHeatR002Q00Point04
  · exact factoredHeatR002Q00Point05
  · exact factoredHeatR002Q00Point06
  · exact factoredHeatR002Q00Point07
  · exact factoredHeatR002Q00Point08
  · exact factoredHeatR002Q00Point09
  · exact factoredHeatR002Q00Point10
  · exact factoredHeatR002Q00Point11
  · exact factoredHeatR002Q00Point12
  · exact factoredHeatR002Q00Point13
  · exact factoredHeatR002Q00Point14
  · exact factoredHeatR002Q00Point15
  · exact factoredHeatR002Q00Point16
  · exact factoredHeatR002Q00Point17
  · exact factoredHeatR002Q00Point18
  · exact factoredHeatR002Q00Point19
  · exact factoredHeatR002Q00Point20
  · exact factoredHeatR002Q00Point21
  · exact factoredHeatR002Q00Point22
  · exact factoredHeatR002Q00Point23
  · exact factoredHeatR002Q00Point24
  · exact factoredHeatR002Q00Point25
  · exact factoredHeatR002Q00Point26
  · exact factoredHeatR002Q00Point27
  · exact factoredHeatR002Q00Point28
  · exact factoredHeatR002Q00Point29
  · exact factoredHeatR002Q00Point30
  · exact factoredHeatR002Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR002Q00Bound {t a : ℝ} (tl : ((213/250):ℝ)≤t) (tu : t≤((853/1000):ℝ)) (al : ((323708955878011/549755813888000):ℝ)≤a) (au : a≤((324245826790011/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-1359058685970995049352810646812885/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR002Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (323708955878011/549755813888000) (324245826790011/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR002Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR002Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR002Q00U (-1359058685970995049352810646812885/162259276829213363391578010288128) factoredHeatR002Q00Samples (by decide +kernel)

theorem factored_original_heat_002 {t a : ℝ} (tb : RealMem derivative_002.t t) (ab : RealMem derivative_002.a a) : reportedHeatPeriod t a≤(derivative_002.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((213/250):ℝ) ((853/1000):ℝ) := by simpa [derivative_002,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((213/250):ℝ)<((853/1000):ℝ)) tB
  have aB : a∈Icc ((323708955878011/549755813888000):ℝ) ((324245826790011/549755813888000):ℝ) := by simpa [derivative_002,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((323708955878011/549755813888000):ℝ)<((324245826790011/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR002Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_002] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR003Q00T := Grid.ofRats (853/1000) (427/500)
def factoredHeatR003Q00P : HeatGridParameters := ⟨⟨⟨⟨82646077647019860248843,82906126226945255145330,true⟩,⟨0,0,true⟩⟩, ⟨⟨1118759219854284719892273,1120613688835621182820228,true⟩,⟨0,0,true⟩⟩, ⟨(-1560434033927734781266849),(-1556725095965130574889844),true⟩, ⟨6346816275958250446768912,6387189796254430122175009,true⟩⟩, ⟨368740059824664408230482,393687729462680372625909,true⟩, ⟨596513896481842664568645,603646454340617337757124,true⟩, ⟨(-1512938583153548695278547),(-1498283957867218362990230),true⟩, ⟨(-2824374466528748141234104),(-2816613770465760914763434),true⟩, ⟨(-612781012174878087206857),(-611324515642844145049439),true⟩⟩
theorem factoredHeatR003Q00P_ok : factoredHeatR003Q00P.encloses (heatGridParameters factoredHeatR003Q00T (Grid.ofRats (971646258964651/1649267441664000) (973256871700651/1649267441664000))) := by decide +kernel
def factoredHeatR003Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨618166266167525658525952,618651963525656253426112,true⟩,⟨2362397153000149772876858,2364253304198857450114479,true⟩,⟨⟨725503550036634358429913,727358019017970821405281,true⟩,⟨965406016837231896424186,967260485818568359402887,true⟩⟩⟩
  | 1 => ⟨⟨11049412632571954971823,11110327245714903026467,true⟩,⟨618166266167525658525952,618651963525656253426112,true⟩,⟨⟨(-1132909994481642462910245),(-1127346587537770513011397),true⟩,⟨426533662186437687582237,432097069130309637471442,true⟩⟩⟩
  | 2 => ⟨⟨13501924517741301657,13683408027530572565,true⟩,⟨11049412632571954971823,11110327245714903026467,true⟩,⟨⟨(-103023676322028355684332),(-93751331415620918872847),true⟩,⟨(-1209551744770768603836847),(-1200279399864361167010129),true⟩⟩⟩
  | 3 => ⟨⟨1127876440448911,1155743829775918,true⟩,⟨13501924517741301657,13683408027530572565,true⟩,⟨⟨1178314283367287046302745,1191295566236229970010106,true⟩,⟨233798616536837536317482,246779899405780460011846,true⟩⟩⟩
  | 4 => ⟨⟨(-27918395345),41053805105,true⟩,⟨1127876440448911,1155743829775918,true⟩,⟨⟨(-568386191896280585511541),(-551695971064802174867582),true⟩,⟨1063035132254905029156206,1079725353086383439807203,true⟩⟩⟩
  | _ => ⟨⟨(-34359735854),34359741028,true⟩,⟨(-27918395345),41053805105,true⟩,⟨⟨(-883774318285704178417257),(-863375159491690280869396),true⟩,⟨(-845884216629526243768479),(-825485057835512346221138),true⟩⟩⟩
theorem factoredHeatR003Q00F_ok : ∀ n : Fin 6, (factoredHeatR003Q00F n).encloses (FactoredFrequency.build factoredHeatR003Q00T (Grid.ofRats (971646258964651/1649267441664000) (973256871700651/1649267441664000)) n) := by decide +kernel
def factoredHeatR003Q00U : ℕ → ℚ
  | 0 => (-23670859/500000)
  | 1 => (-32333951/1000000)
  | 2 => (-4700487/250000)
  | 3 => (-525211/50000)
  | 4 => (-1228433/200000)
  | 5 => (-2020539/500000)
  | 6 => (-3029081/1000000)
  | 7 => (-2716989/1000000)
  | 8 => (-2966529/1000000)
  | 9 => (-498953/125000)
  | 10 => (-6613547/1000000)
  | 11 => (-2859693/250000)
  | 12 => (-17835441/1000000)
  | 13 => (-4824359/200000)
  | 14 => (-3354243/125000)
  | 15 => (-4795067/200000)
  | 16 => (-4638239/250000)
  | 17 => (-6805049/500000)
  | 18 => (-10929703/1000000)
  | 19 => (-2506669/250000)
  | 20 => (-10019093/1000000)
  | 21 => (-5048523/500000)
  | 22 => (-4649921/500000)
  | 23 => (-651771/100000)
  | 24 => (-19949/500000)
  | 25 => (11113961/1000000)
  | 26 => (12975481/500000)
  | 27 => (19116409/500000)
  | 28 => (18081721/500000)
  | 29 => (5184091/500000)
  | 30 => (-6870793/250000)
  | 31 => (-24930911/500000)
  | _ => 0
theorem factoredHeatR003Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR003Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR003Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR003Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR003Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR003Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR003Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR003Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR003Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR003Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR003Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR003Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR003Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR003Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR003Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR003Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR003Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR003Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR003Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR003Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR003Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR003Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR003Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR003Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR003Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR003Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR003Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR003Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR003Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR003Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR003Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR003Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR003Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR003Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR003Q00P factoredHeatR003Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR003Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR003Q00Point00
  · exact factoredHeatR003Q00Point01
  · exact factoredHeatR003Q00Point02
  · exact factoredHeatR003Q00Point03
  · exact factoredHeatR003Q00Point04
  · exact factoredHeatR003Q00Point05
  · exact factoredHeatR003Q00Point06
  · exact factoredHeatR003Q00Point07
  · exact factoredHeatR003Q00Point08
  · exact factoredHeatR003Q00Point09
  · exact factoredHeatR003Q00Point10
  · exact factoredHeatR003Q00Point11
  · exact factoredHeatR003Q00Point12
  · exact factoredHeatR003Q00Point13
  · exact factoredHeatR003Q00Point14
  · exact factoredHeatR003Q00Point15
  · exact factoredHeatR003Q00Point16
  · exact factoredHeatR003Q00Point17
  · exact factoredHeatR003Q00Point18
  · exact factoredHeatR003Q00Point19
  · exact factoredHeatR003Q00Point20
  · exact factoredHeatR003Q00Point21
  · exact factoredHeatR003Q00Point22
  · exact factoredHeatR003Q00Point23
  · exact factoredHeatR003Q00Point24
  · exact factoredHeatR003Q00Point25
  · exact factoredHeatR003Q00Point26
  · exact factoredHeatR003Q00Point27
  · exact factoredHeatR003Q00Point28
  · exact factoredHeatR003Q00Point29
  · exact factoredHeatR003Q00Point30
  · exact factoredHeatR003Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR003Q00Bound {t a : ℝ} (tl : ((853/1000):ℝ)≤t) (tu : t≤((427/500):ℝ)) (al : ((971646258964651/1649267441664000):ℝ)≤a) (au : a≤((973256871700651/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2729056318259863094983757791282471/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR003Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (971646258964651/1649267441664000) (973256871700651/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR003Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR003Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR003Q00U (-2729056318259863094983757791282471/324518553658426726783156020576256) factoredHeatR003Q00Samples (by decide +kernel)

theorem factored_original_heat_003 {t a : ℝ} (tb : RealMem derivative_003.t t) (ab : RealMem derivative_003.a a) : reportedHeatPeriod t a≤(derivative_003.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((853/1000):ℝ) ((427/500):ℝ) := by simpa [derivative_003,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((853/1000):ℝ)<((427/500):ℝ)) tB
  have aB : a∈Icc ((971646258964651/1649267441664000):ℝ) ((973256871700651/1649267441664000):ℝ) := by simpa [derivative_003,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((971646258964651/1649267441664000):ℝ)<((973256871700651/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR003Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_003] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR004Q00T := Grid.ofRats (427/500) (171/200)
def factoredHeatR004Q00P : HeatGridParameters := ⟨⟨⟨⟨82386844751925736465161,82646077647088579726649,true⟩,⟨0,0,true⟩⟩, ⟨⟨1119358366348431445091209,1121212835329767908019166,true⟩,⟨0,0,true⟩⟩, ⟨(-1559235740939441330868974),(-1555526802976837124491972),true⟩, ⟨6338310988688614047143571,6378570505139487748333573,true⟩⟩, ⟨369462450063044595706402,394386495511109100864116,true⟩, ⟨596566750585096982096963,603686577167474303285091,true⟩, ⟨(-1510759762344243907122366),(-1496149248330775656374087),true⟩, ⟨(-2820389366138428035845782),(-2812653744756889399763080),true⟩, ⟨(-612310443618769229221833),(-610853947086735287064419),true⟩⟩
theorem factoredHeatR004Q00P_ok : factoredHeatR004Q00P.encloses (heatGridParameters factoredHeatR004Q00T (Grid.ofRats (972166619770871/1649267441664000) (973777232506871/1649267441664000))) := by decide +kernel
def factoredHeatR004Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨617680950125514707637961,618166266167594378024882,true⟩,⟨2364253304198788730552836,2366110913787872400836863,true⟩,⟨⟨725024543798852351778804,726879012780188814754150,true⟩,⟨965765918960407819804508,967620387941744282783200,true⟩⟩⟩
  | 1 => ⟨⟨10988831996166813758819,11049412632640674449104,true⟩,⟨617680950125514707637961,618166266167594378024882,true⟩,⟨⟨(-1133547054248951476484697),(-1127983647305079526585484),true⟩,⟨424852905526255384612584,430416312470127334502103,true⟩⟩⟩
  | 2 => ⟨⟨13322848096866985938,13501924586460778395,true⟩,⟨10988831996166813758819,11049412632640674449104,true⟩,⟨⟨(-100037582271057479093219),(-90765237364650042282328),true⟩,⟨(-1209791850503001911490192),(-1200519505596594474664024),true⟩⟩⟩
  | 3 => ⟨⟨1100746421384569,1127945159925648,true⟩,⟨13322848096866985938,13501924586460778395,true⟩,⟨⟨1177473539738282524000114,1190454822607225447707396,true⟩,⟨237907507148600039338025,250888790017542963032378,true⟩⟩⟩
  | 4 => ⟨⟨(-28161577882),40801081392,true⟩,⟨1100746421384569,1127945159925648,true⟩,⟨⟨(-573159412180078406665048),(-556469191348599996021379),true⟩,⟨1060526463653552288971684,1077216684485030699622290,true⟩⟩⟩
  | _ => ⟨⟨(-34359735990),34359740883,true⟩,⟨(-28161577882),40801081392,true⟩,⟨⟨(-879205519365390935147509),(-858806360571377037599464),true⟩,⟨(-850634177465511221297775),(-830235018671497323750121),true⟩⟩⟩
theorem factoredHeatR004Q00F_ok : ∀ n : Fin 6, (factoredHeatR004Q00F n).encloses (FactoredFrequency.build factoredHeatR004Q00T (Grid.ofRats (972166619770871/1649267441664000) (973777232506871/1649267441664000)) n) := by decide +kernel
def factoredHeatR004Q00U : ℕ → ℚ
  | 0 => (-4717553/100000)
  | 1 => (-32337679/1000000)
  | 2 => (-2359663/125000)
  | 3 => (-10589287/1000000)
  | 4 => (-6213711/1000000)
  | 5 => (-4095743/1000000)
  | 6 => (-61369/20000)
  | 7 => (-1371107/500000)
  | 8 => (-744319/250000)
  | 9 => (-3985291/1000000)
  | 10 => (-3292767/500000)
  | 11 => (-711373/62500)
  | 12 => (-17746977/1000000)
  | 13 => (-24015321/1000000)
  | 14 => (-6687809/250000)
  | 15 => (-957881/40000)
  | 16 => (-9287489/500000)
  | 17 => (-2730843/200000)
  | 18 => (-685769/62500)
  | 19 => (-402303/40000)
  | 20 => (-10036601/1000000)
  | 21 => (-10100339/1000000)
  | 22 => (-1161151/125000)
  | 23 => (-6496571/1000000)
  | 24 => (-10233/500000)
  | 25 => (5552499/500000)
  | 26 => (5175859/200000)
  | 27 => (19047833/500000)
  | 28 => (9011809/250000)
  | 29 => (10441143/1000000)
  | 30 => (-1358707/50000)
  | 31 => (-49528871/1000000)
  | _ => 0
theorem factoredHeatR004Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR004Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR004Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR004Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR004Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR004Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR004Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR004Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR004Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR004Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR004Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR004Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR004Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR004Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR004Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR004Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR004Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR004Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR004Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR004Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR004Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR004Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR004Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR004Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR004Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR004Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR004Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR004Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR004Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR004Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR004Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR004Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR004Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR004Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR004Q00P factoredHeatR004Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR004Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR004Q00Point00
  · exact factoredHeatR004Q00Point01
  · exact factoredHeatR004Q00Point02
  · exact factoredHeatR004Q00Point03
  · exact factoredHeatR004Q00Point04
  · exact factoredHeatR004Q00Point05
  · exact factoredHeatR004Q00Point06
  · exact factoredHeatR004Q00Point07
  · exact factoredHeatR004Q00Point08
  · exact factoredHeatR004Q00Point09
  · exact factoredHeatR004Q00Point10
  · exact factoredHeatR004Q00Point11
  · exact factoredHeatR004Q00Point12
  · exact factoredHeatR004Q00Point13
  · exact factoredHeatR004Q00Point14
  · exact factoredHeatR004Q00Point15
  · exact factoredHeatR004Q00Point16
  · exact factoredHeatR004Q00Point17
  · exact factoredHeatR004Q00Point18
  · exact factoredHeatR004Q00Point19
  · exact factoredHeatR004Q00Point20
  · exact factoredHeatR004Q00Point21
  · exact factoredHeatR004Q00Point22
  · exact factoredHeatR004Q00Point23
  · exact factoredHeatR004Q00Point24
  · exact factoredHeatR004Q00Point25
  · exact factoredHeatR004Q00Point26
  · exact factoredHeatR004Q00Point27
  · exact factoredHeatR004Q00Point28
  · exact factoredHeatR004Q00Point29
  · exact factoredHeatR004Q00Point30
  · exact factoredHeatR004Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR004Q00Bound {t a : ℝ} (tl : ((427/500):ℝ)≤t) (tu : t≤((171/200):ℝ)) (al : ((972166619770871/1649267441664000):ℝ)≤a) (au : a≤((973777232506871/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2738503216448377603467823650444295/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR004Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (972166619770871/1649267441664000) (973777232506871/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR004Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR004Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR004Q00U (-2738503216448377603467823650444295/324518553658426726783156020576256) factoredHeatR004Q00Samples (by decide +kernel)

theorem factored_original_heat_004 {t a : ℝ} (tb : RealMem derivative_004.t t) (ab : RealMem derivative_004.a a) : reportedHeatPeriod t a≤(derivative_004.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((427/500):ℝ) ((171/200):ℝ) := by simpa [derivative_004,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((427/500):ℝ)<((171/200):ℝ)) tB
  have aB : a∈Icc ((972166619770871/1649267441664000):ℝ) ((973777232506871/1649267441664000):ℝ) := by simpa [derivative_004,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((972166619770871/1649267441664000):ℝ)<((973777232506871/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR004Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_004] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR005Q00T := Grid.ofRats (171/200) (107/125)
def factoredHeatR005Q00P : HeatGridParameters := ⟨⟨⟨⟨82128424983065937684295,82386844751994455942973,true⟩,⟨0,0,true⟩⟩, ⟨⟨1119958629865877529900288,1121813098847213992828247,true⟩,⟨0,0,true⟩⟩, ⟨(-1558035213904549161250812),(-1554326275941944954873814),true⟩, ⟨6329818462613741775648126,6369964356045734321608339,true⟩⟩, ⟨370185277319157844789257,395085817416710402752174,true⟩, ⟨596616221024669831237899,603723338489000116460012,true⟩, ⟨(-1508589299774851550735041),(-1494022739479612632915512),true⟩, ⟨(-2816410480207303611237470),(-2808699845013677758073183),true⟩, ⟨(-611838997754612582040905),(-610382501222578639883494),true⟩⟩
theorem factoredHeatR005Q00P_ok : factoredHeatR005Q00P.encloses (heatGridParameters factoredHeatR005Q00T (Grid.ofRats (972687950715697/1649267441664000) (974298563451697/1649267441664000))) := by decide +kernel
def factoredHeatR005Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨617196015100187331863281,617680950125583427137008,true⟩,⟨2366110913787803681274588,2367969982913130389460701,true⟩,⟨⟨724544465713772720615128,726398934695109183590391,true⟩,⟨966126253964536436471665,967980722945872899450316,true⟩⟩⟩
  | 1 => ⟨⟨10928583505336218461294,10988831996235533236097,true⟩,⟨617196015100187331863281,617680950125583427137008,true⟩,⟨⟨(-1134182795063694313377031),(-1128619388119822363477841),true⟩,⟨423168067364814889768172,428731474308686839657638,true⟩⟩⟩
  | 2 => ⟨⟨13146146771808782218,13322848165586462676,true⟩,⟨10928583505336218461294,10988831996235533236097,true⟩,⟨⟨(-97045333629085612453908),(-87772988722678175642612),true⟩,⟨(-1210024982863219429641122),(-1200752637956811992814506),true⟩⟩⟩
  | 3 => ⟨⟨1074268969823179,1100815140861306,true⟩,⟨13146146771808782218,13322848165586462676,true⟩,⟨⟨1176616939251440834691463,1189598222120383758399185,true⟩,⟨242021108497861603315403,255002391366804527010259,true⟩⟩⟩
  | 4 => ⟨⟨(-28395579453),40557898855,true⟩,⟨1074268969823179,1100815140861306,true⟩,⟨⟨(-577930262785396205430852),(-561240041953917794787075),true⟩,⟨1057991792974056048589078,1074682013805534459239690,true⟩⟩⟩
  | _ => ⟨⟨(-34359736119),34359740747,true⟩,⟨(-28395579453),40557898855,true⟩,⟨⟨(-874602303395179418807660),(-854203144601165521260246),true⟩,⟨(-855367946100022038592687),(-834968787306008141045536),true⟩⟩⟩
theorem factoredHeatR005Q00F_ok : ∀ n : Fin 6, (factoredHeatR005Q00F n).encloses (FactoredFrequency.build factoredHeatR005Q00T (Grid.ofRats (972687950715697/1649267441664000) (974298563451697/1649267441664000)) n) := by decide +kernel
def factoredHeatR005Q00U : ℕ → ℚ
  | 0 => (-23504449/500000)
  | 1 => (-32339979/1000000)
  | 2 => (-4737861/250000)
  | 3 => (-5336793/500000)
  | 4 => (-6284799/1000000)
  | 5 => (-4150113/1000000)
  | 6 => (-1553803/500000)
  | 7 => (-2767279/1000000)
  | 8 => (-1493959/500000)
  | 9 => (-994733/250000)
  | 10 => (-3278803/500000)
  | 11 => (-11325397/1000000)
  | 12 => (-8829449/500000)
  | 13 => (-5977307/250000)
  | 14 => (-26668577/1000000)
  | 15 => (-11959151/500000)
  | 16 => (-3719271/200000)
  | 17 => (-3424443/250000)
  | 18 => (-11014511/1000000)
  | 19 => (-10088201/1000000)
  | 20 => (-10053891/1000000)
  | 21 => (-10103459/1000000)
  | 22 => (-4639233/500000)
  | 23 => (-1295083/200000)
  | 24 => (-1123/1000000)
  | 25 => (5547969/500000)
  | 26 => (1290389/50000)
  | 27 => (3795911/100000)
  | 28 => (35931583/1000000)
  | 29 => (5256631/500000)
  | 30 => (-13433749/500000)
  | 31 => (-9839499/200000)
  | _ => 0
theorem factoredHeatR005Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR005Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR005Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR005Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR005Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR005Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR005Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR005Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR005Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR005Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR005Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR005Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR005Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR005Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR005Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR005Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR005Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR005Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR005Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR005Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR005Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR005Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR005Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR005Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR005Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR005Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR005Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR005Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR005Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR005Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR005Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR005Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR005Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR005Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR005Q00P factoredHeatR005Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR005Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR005Q00Point00
  · exact factoredHeatR005Q00Point01
  · exact factoredHeatR005Q00Point02
  · exact factoredHeatR005Q00Point03
  · exact factoredHeatR005Q00Point04
  · exact factoredHeatR005Q00Point05
  · exact factoredHeatR005Q00Point06
  · exact factoredHeatR005Q00Point07
  · exact factoredHeatR005Q00Point08
  · exact factoredHeatR005Q00Point09
  · exact factoredHeatR005Q00Point10
  · exact factoredHeatR005Q00Point11
  · exact factoredHeatR005Q00Point12
  · exact factoredHeatR005Q00Point13
  · exact factoredHeatR005Q00Point14
  · exact factoredHeatR005Q00Point15
  · exact factoredHeatR005Q00Point16
  · exact factoredHeatR005Q00Point17
  · exact factoredHeatR005Q00Point18
  · exact factoredHeatR005Q00Point19
  · exact factoredHeatR005Q00Point20
  · exact factoredHeatR005Q00Point21
  · exact factoredHeatR005Q00Point22
  · exact factoredHeatR005Q00Point23
  · exact factoredHeatR005Q00Point24
  · exact factoredHeatR005Q00Point25
  · exact factoredHeatR005Q00Point26
  · exact factoredHeatR005Q00Point27
  · exact factoredHeatR005Q00Point28
  · exact factoredHeatR005Q00Point29
  · exact factoredHeatR005Q00Point30
  · exact factoredHeatR005Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR005Q00Bound {t a : ℝ} (tl : ((171/200):ℝ)≤t) (tu : t≤((107/125):ℝ)) (al : ((972687950715697/1649267441664000):ℝ)≤a) (au : a≤((974298563451697/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-686658837745972167127981144512065/81129638414606681695789005144064):ℚ):ℝ) := by
  have ts : factoredHeatR005Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (972687950715697/1649267441664000) (974298563451697/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR005Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR005Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR005Q00U (-686658837745972167127981144512065/81129638414606681695789005144064) factoredHeatR005Q00Samples (by decide +kernel)

theorem factored_original_heat_005 {t a : ℝ} (tb : RealMem derivative_005.t t) (ab : RealMem derivative_005.a a) : reportedHeatPeriod t a≤(derivative_005.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((171/200):ℝ) ((107/125):ℝ) := by simpa [derivative_005,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((171/200):ℝ)<((107/125):ℝ)) tB
  have aB : a∈Icc ((972687950715697/1649267441664000):ℝ) ((974298563451697/1649267441664000):ℝ) := by simpa [derivative_005,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((972687950715697/1649267441664000):ℝ)<((974298563451697/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR005Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_005] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR006Q00T := Grid.ofRats (107/125) (857/1000)
def factoredHeatR006Q00P : HeatGridParameters := ⟨⟨⟨⟨81870815789937478135487,82128424983134657162099,true⟩,⟨0,0,true⟩⟩, ⟨⟨1120560011193003256619947,1122414480174339719547908,true⟩,⟨0,0,true⟩⟩, ⟨(-1556832451250297707811491),(-1553123513287693501434497),true⟩, ⟨6321338698316384950804694,6361371348295971458614448,true⟩⟩, ⟨370908547217580814931708,395785700381957281676514,true⟩, ⟨596662312480598024220806,603756742943616419238008,true⟩, ⟨(-1506427173952095913215472),(-1491904410397614253139020),true⟩, ⟨(-2812437824677728005769750),(-2804752087565745433829527),true⟩, ⟨(-611366673964786516213342),(-609910177432752574055934),true⟩⟩
theorem factoredHeatR006Q00P_ok : factoredHeatR006Q00P.encloses (heatGridParameters factoredHeatR006Q00T (Grid.ofRats (973210252482103/1649267441664000) (974820865218103/1649267441664000))) := by decide +kernel
def factoredHeatR006Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨616711460792411212063047,617196015100256051362280,true⟩,⟨2367969982913061669898894,2369830512721398776220154,true⟩,⟨⟨724063314271644621179133,725917783252981084154355,true⟩,⟨966487020901624087411727,968341489882960550390359,true⟩⟩⟩
  | 1 => ⟨⟨10868665339024973279521,10928583505404937938570,true⟩,⟨616711460792411212063047,617196015100256051362280,true⟩,⟨⟨(-1134817202332370074799139),(-1129253795388498124899707),true⟩,⟨421479143944734120059562,427042550888606069949247,true⟩⟩⟩
  | 2 => ⟨⟨12971789041601302810,13146146840528258956,true⟩,⟨10868665339024973279521,10928583505404937938570,true⟩,⟨⟨(-94046941686533587249237),(-84774596780126150438317),true⟩,⟨(-1210251099233727264507443),(-1200978754327319827681159),true⟩⟩⟩
  | 3 => ⟨⟨1048428389338399,1074337689299916,true⟩,⟨12971789041601302810,13146146840528258956,true⟩,⟨⟨1175744411286280863661257,1188725694155223787369032,true⟩,⟨246139359652618128529018,259120642521561052224007,true⟩⟩⟩
  | 4 => ⟨⟨(-28620746672),40323897284,true⟩,⟨1048428389338399,1074337689299916,true⟩,⟨⟨(-582698591434362073701976),(-566008370602883663057686),true⟩,⟨1055431048450727090252657,1072121269282205500903681,true⟩⟩⟩
  | _ => ⟨⟨(-34359736241),34359740618,true⟩,⟨(-28620746672),40323897284,true⟩,⟨⟨(-869964657275984415745319),(-849565498481970518197519),true⟩,⟨(-860085247113940935951265),(-839686088319927038403599),true⟩⟩⟩
theorem factoredHeatR006Q00F_ok : ∀ n : Fin 6, (factoredHeatR006Q00F n).encloses (FactoredFrequency.build factoredHeatR006Q00T (Grid.ofRats (973210252482103/1649267441664000) (974820865218103/1649267441664000)) n) := by decide +kernel
def factoredHeatR006Q00U : ℕ → ℚ
  | 0 => (-9368367/200000)
  | 1 => (-16170433/500000)
  | 2 => (-4756093/250000)
  | 3 => (-10757117/1000000)
  | 4 => (-6355347/1000000)
  | 5 => (-4204187/1000000)
  | 6 => (-786637/250000)
  | 7 => (-2792179/1000000)
  | 8 => (-374807/125000)
  | 9 => (-993137/250000)
  | 10 => (-6529757/1000000)
  | 11 => (-5634529/500000)
  | 12 => (-8785601/500000)
  | 13 => (-23803507/1000000)
  | 14 => (-26585969/1000000)
  | 15 => (-23889169/1000000)
  | 16 => (-18617093/1000000)
  | 17 => (-429399/31250)
  | 18 => (-442253/40000)
  | 19 => (-1264819/125000)
  | 20 => (-5035483/500000)
  | 21 => (-10106409/1000000)
  | 22 => (-1853523/200000)
  | 23 => (-1613561/250000)
  | 24 => (18131/1000000)
  | 25 => (554339/50000)
  | 26 => (804263/31250)
  | 27 => (9455787/250000)
  | 28 => (223853/6250)
  | 29 => (2116909/200000)
  | 30 => (-6640807/250000)
  | 31 => (-48867689/1000000)
  | _ => 0
theorem factoredHeatR006Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR006Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR006Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR006Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR006Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR006Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR006Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR006Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR006Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR006Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR006Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR006Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR006Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR006Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR006Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR006Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR006Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR006Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR006Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR006Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR006Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR006Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR006Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR006Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR006Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR006Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR006Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR006Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR006Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR006Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR006Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR006Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR006Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR006Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR006Q00P factoredHeatR006Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR006Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR006Q00Point00
  · exact factoredHeatR006Q00Point01
  · exact factoredHeatR006Q00Point02
  · exact factoredHeatR006Q00Point03
  · exact factoredHeatR006Q00Point04
  · exact factoredHeatR006Q00Point05
  · exact factoredHeatR006Q00Point06
  · exact factoredHeatR006Q00Point07
  · exact factoredHeatR006Q00Point08
  · exact factoredHeatR006Q00Point09
  · exact factoredHeatR006Q00Point10
  · exact factoredHeatR006Q00Point11
  · exact factoredHeatR006Q00Point12
  · exact factoredHeatR006Q00Point13
  · exact factoredHeatR006Q00Point14
  · exact factoredHeatR006Q00Point15
  · exact factoredHeatR006Q00Point16
  · exact factoredHeatR006Q00Point17
  · exact factoredHeatR006Q00Point18
  · exact factoredHeatR006Q00Point19
  · exact factoredHeatR006Q00Point20
  · exact factoredHeatR006Q00Point21
  · exact factoredHeatR006Q00Point22
  · exact factoredHeatR006Q00Point23
  · exact factoredHeatR006Q00Point24
  · exact factoredHeatR006Q00Point25
  · exact factoredHeatR006Q00Point26
  · exact factoredHeatR006Q00Point27
  · exact factoredHeatR006Q00Point28
  · exact factoredHeatR006Q00Point29
  · exact factoredHeatR006Q00Point30
  · exact factoredHeatR006Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR006Q00Bound {t a : ℝ} (tl : ((107/125):ℝ)≤t) (tu : t≤((857/1000):ℝ)) (al : ((973210252482103/1649267441664000):ℝ)≤a) (au : a≤((974820865218103/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2753586333147261751344108422223779/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR006Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (973210252482103/1649267441664000) (974820865218103/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR006Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR006Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR006Q00U (-2753586333147261751344108422223779/324518553658426726783156020576256) factoredHeatR006Q00Samples (by decide +kernel)

theorem factored_original_heat_006 {t a : ℝ} (tb : RealMem derivative_006.t t) (ab : RealMem derivative_006.a a) : reportedHeatPeriod t a≤(derivative_006.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((107/125):ℝ) ((857/1000):ℝ) := by simpa [derivative_006,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((107/125):ℝ)<((857/1000):ℝ)) tB
  have aB : a∈Icc ((973210252482103/1649267441664000):ℝ) ((974820865218103/1649267441664000):ℝ) := by simpa [derivative_006,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((973210252482103/1649267441664000):ℝ)<((974820865218103/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR006Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_006] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_002
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_003
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_004
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_005
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_006
