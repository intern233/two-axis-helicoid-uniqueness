import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR023Q00T := Grid.ofRats (873/1000) (437/500)
def factoredHeatR023Q00P : HeatGridParameters := ⟨⟨⟨⟨77613044530568524868973,77857256507577393596927,true⟩,⟨0,0,true⟩⟩, ⟨⟨1130955318296497335792634,1132809787277833798720628,true⟩,⟨0,0,true⟩⟩, ⟨(-1536041837043309549466049),(-1532332899080705343089121),true⟩, ⟨6179134890525722900893177,6217299271725284939223777,true⟩⟩, ⟨383277459869613759541747,407774770213411417869294,true⟩, ⟨596933410229496378737900,603815506058808995000023,true⟩, ⟨(-1470925867336852933565346),(-1457124178291880953691017),true⟩, ⟨(-2745870228994129432811584),(-2738594643220913623298871),true⟩, ⟨(-603202218857749818313472),(-601745722325715876156115),true⟩⟩
theorem factoredHeatR023Q00P_ok : factoredHeatR023Q00P.encloses (heatGridParameters factoredHeatR023Q00T (Grid.ofRats (327412870907139/549755813888000) (327949741819139/549755813888000))) := by decide +kernel
def factoredHeatR023Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨608531998621316746640888,609010126271182499804810,true⟩,⟨2399798581805815607715136,2401684119556577109270825,true⟩,⟨⟨715718015990082963194394,717572484971419426169778,true⟩,⟨972685225523214447133239,974539694504550910112227,true⟩⟩⟩
  | 1 => ⟨⟨9898879097459979189277,9953450902396683340604,true⟩,⟨608531998621316746640888,609010126271182499804810,true⟩,⟨⟨(-1145383748882649088662575),(-1139820341938777138763175),true⟩,⟨392138798849933363784958,397702205793805313674063,true⟩⟩⟩
  | 2 => ⟨⟨10337694299996814885,10476646436866813079,true⟩,⟨9898879097459979189277,9953450902396683340604,true⟩,⟨⟨(-42146097866118290809012),(-32873752959710853998514),true⟩,⟨(-1212979932658229357684695),(-1203707587751821920858082),true⟩⟩⟩
  | 3 => ⟨⟨693066472573119,710217465938159,true⟩,⟨10337694299996814885,10476646436866813079,true⟩,⟨⟨1158406406414656851873315,1171387689283599775583108,true⟩,⟨316799484061635483675939,329780766930578407374155,true⟩⟩⟩
  | 4 => ⟨⟨(-31376388273),37460139103,true⟩,⟨693066472573119,710217465938159,true⟩,⟨⟨(-663222126229775257546561),(-646531905398296846901052),true⟩,⟨1007842732204612995361537,1024532953036091406012018,true⟩⟩⟩
  | _ => ⟨⟨(-34359737544),34359739240,true⟩,⟨(-31376388273),37460139103,true⟩,⟨⟨(-785853393523012652359322),(-765454234728998754810873),true⟩,⟨(-937487451615059153062979),(-917088292821045255512441),true⟩⟩⟩
theorem factoredHeatR023Q00F_ok : ∀ n : Fin 6, (factoredHeatR023Q00F n).encloses (FactoredFrequency.build factoredHeatR023Q00T (Grid.ofRats (327412870907139/549755813888000) (327949741819139/549755813888000)) n) := by decide +kernel
def factoredHeatR023Q00U : ℕ → ℚ
  | 0 => (-10987127/250000)
  | 1 => (-16069393/500000)
  | 2 => (-20081113/1000000)
  | 3 => (-12058661/1000000)
  | 4 => (-3739711/500000)
  | 5 => (-2537683/500000)
  | 6 => (-188757/50000)
  | 7 => (-319051/100000)
  | 8 => (-3161359/1000000)
  | 9 => (-3860409/1000000)
  | 10 => (-6068987/1000000)
  | 11 => (-5172751/500000)
  | 12 => (-8068651/500000)
  | 13 => (-689537/31250)
  | 14 => (-12571461/500000)
  | 15 => (-5833849/250000)
  | 16 => (-9437749/500000)
  | 17 => (-2877507/200000)
  | 18 => (-11706887/1000000)
  | 19 => (-10592207/1000000)
  | 20 => (-5162721/500000)
  | 21 => (-10130857/1000000)
  | 22 => (-9067393/1000000)
  | 23 => (-3046307/500000)
  | 24 => (165939/500000)
  | 25 => (2183431/200000)
  | 26 => (76708/3125)
  | 27 => (35599483/1000000)
  | 28 => (16969777/500000)
  | 29 => (2334937/200000)
  | 30 => (-5432419/250000)
  | 31 => (-86947/2000)
  | _ => 0
theorem factoredHeatR023Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR023Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR023Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR023Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR023Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR023Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR023Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR023Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR023Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR023Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR023Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR023Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR023Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR023Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR023Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR023Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR023Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR023Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR023Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR023Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR023Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR023Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR023Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR023Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR023Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR023Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR023Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR023Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR023Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR023Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR023Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR023Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR023Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR023Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR023Q00P factoredHeatR023Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR023Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR023Q00Point00
  · exact factoredHeatR023Q00Point01
  · exact factoredHeatR023Q00Point02
  · exact factoredHeatR023Q00Point03
  · exact factoredHeatR023Q00Point04
  · exact factoredHeatR023Q00Point05
  · exact factoredHeatR023Q00Point06
  · exact factoredHeatR023Q00Point07
  · exact factoredHeatR023Q00Point08
  · exact factoredHeatR023Q00Point09
  · exact factoredHeatR023Q00Point10
  · exact factoredHeatR023Q00Point11
  · exact factoredHeatR023Q00Point12
  · exact factoredHeatR023Q00Point13
  · exact factoredHeatR023Q00Point14
  · exact factoredHeatR023Q00Point15
  · exact factoredHeatR023Q00Point16
  · exact factoredHeatR023Q00Point17
  · exact factoredHeatR023Q00Point18
  · exact factoredHeatR023Q00Point19
  · exact factoredHeatR023Q00Point20
  · exact factoredHeatR023Q00Point21
  · exact factoredHeatR023Q00Point22
  · exact factoredHeatR023Q00Point23
  · exact factoredHeatR023Q00Point24
  · exact factoredHeatR023Q00Point25
  · exact factoredHeatR023Q00Point26
  · exact factoredHeatR023Q00Point27
  · exact factoredHeatR023Q00Point28
  · exact factoredHeatR023Q00Point29
  · exact factoredHeatR023Q00Point30
  · exact factoredHeatR023Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR023Q00Bound {t a : ℝ} (tl : ((873/1000):ℝ)≤t) (tu : t≤((437/500):ℝ)) (al : ((327412870907139/549755813888000):ℝ)≤a) (au : a≤((327949741819139/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-1299609684158230058969598550346073/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR023Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (327412870907139/549755813888000) (327949741819139/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR023Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR023Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR023Q00U (-1299609684158230058969598550346073/162259276829213363391578010288128) factoredHeatR023Q00Samples (by decide +kernel)

theorem factored_original_heat_023 {t a : ℝ} (tb : RealMem derivative_023.t t) (ab : RealMem derivative_023.a a) : reportedHeatPeriod t a≤(derivative_023.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((873/1000):ℝ) ((437/500):ℝ) := by simpa [derivative_023,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((873/1000):ℝ)<((437/500):ℝ)) tB
  have aB : a∈Icc ((327412870907139/549755813888000):ℝ) ((327949741819139/549755813888000):ℝ) := by simpa [derivative_023,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((327412870907139/549755813888000):ℝ)<((327949741819139/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR023Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_023] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR024Q00T := Grid.ofRats (437/500) (7/8)
def factoredHeatR024Q00P : HeatGridParameters := ⟨⟨⟨⟨77369598564304275018663,77613044530637244346736,true⟩,⟨0,0,true⟩⟩, ⟨⟨1131576963861716377520166,1133431432843052840448162,true⟩,⟨0,0,true⟩⟩, ⟨(-1534798545912871466010983),(-1531089607950267259634059),true⟩, ⟨6170884719619442761017984,6208942478122801790477537,true⟩⟩, ⟨384009695062340931469694,408485683943025741722623,true⟩, ⟨596919477889576838801214,603789277898548354939303,true⟩, ⟨(-1468910159322648147161758),(-1455149537364587292247148),true⟩, ⟨(-2742012178038039072004588),(-2734759968076879334203743),true⟩, ⟨(-602713979572542614268969),(-601257483040508672111616),true⟩⟩
theorem factoredHeatR024Q00P_ok : factoredHeatR024Q00P.encloses (heatGridParameters factoredHeatR024Q00T (Grid.ofRats (982778514048823/1649267441664000) (984389126784823/1649267441664000))) := by decide +kernel
def factoredHeatR024Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨608054246344669746040605,608531998621385466139571,true⟩,⟨2401684119556508389707766,2403571138786855820624644,true⟩,⟨⟨715217276927086037061162,717071745908422500036514,true⟩,⟨973053605206463050990938,974908074187799513969894,true⟩⟩⟩
  | 1 => ⟨⟨9844606493534035891642,9898879097528698666506,true⟩,⟨608054246344669746040605,608531998621385466139571,true⟩,⟨⟨(-1145991609053024115291654),(-1140428202109152165392399),true⟩,⟨390375706622522829002411,395939113566394778891330,true⟩⟩⟩
  | 2 => ⟨⟨10200585157196784098,10337694368716291623,true⟩,⟨9844606493534035891642,9898879097528698666506,true⟩,⟨⟨(-39039245998491056830865),(-29766901092083620020220),true⟩,⟨(-1213072379235150677091108),(-1203800034328743240264302),true⟩⟩⟩
  | 3 => ⟨⟨676395084382670,693135192049856,true⟩,⟨10200585157196784098,10337694368716291623,true⟩,⟨⟨1157235182274595863488035,1170216465143538787197860,true⟩,⟨320990418420225593281121,333971701289168516979443,true⟩⟩⟩
  | 4 => ⟨⟨(-31489019853),37343088464,true⟩,⟨676395084382670,693135192049856,true⟩,⟨⟨(-667917930948695847379139),(-651227710117217436733964),true⟩,⟨1004801143461312391228495,1021491364292790801878532,true⟩⟩⟩
  | _ => ⟨⟨(-34359737589),34359739193,true⟩,⟨(-31489019853),37343088464,true⟩,⟨⟨(-780595953407877893924329),(-760196794613863996376503),true⟩,⟨(-941859959708311787484096),(-921460800914297889934046),true⟩⟩⟩
theorem factoredHeatR024Q00F_ok : ∀ n : Fin 6, (factoredHeatR024Q00F n).encloses (FactoredFrequency.build factoredHeatR024Q00T (Grid.ofRats (982778514048823/1649267441664000) (984389126784823/1649267441664000)) n) := by decide +kernel
def factoredHeatR024Q00U : ℕ → ℚ
  | 0 => (-43775879/1000000)
  | 1 => (-3211397/100000)
  | 2 => (-5033227/250000)
  | 3 => (-6064163/500000)
  | 4 => (-7541341/1000000)
  | 5 => (-64047/12500)
  | 6 => (-1905027/500000)
  | 7 => (-1606251/500000)
  | 8 => (-3170009/1000000)
  | 9 => (-3853613/1000000)
  | 10 => (-6042629/1000000)
  | 11 => (-205863/20000)
  | 12 => (-16056209/1000000)
  | 13 => (-21966289/1000000)
  | 14 => (-25056923/1000000)
  | 15 => (-23299617/1000000)
  | 16 => (-9442693/500000)
  | 17 => (-180259/12500)
  | 18 => (-11741613/1000000)
  | 19 => (-331799/31250)
  | 20 => (-10338363/1000000)
  | 21 => (-10130817/1000000)
  | 22 => (-1810947/200000)
  | 23 => (-1517607/250000)
  | 24 => (10923/31250)
  | 25 => (5453201/500000)
  | 26 => (6119487/250000)
  | 27 => (17736831/500000)
  | 28 => (4229201/125000)
  | 29 => (5866003/500000)
  | 30 => (-5366139/250000)
  | 31 => (-21583599/500000)
  | _ => 0
theorem factoredHeatR024Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR024Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR024Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR024Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR024Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR024Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR024Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR024Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR024Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR024Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR024Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR024Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR024Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR024Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR024Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR024Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR024Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR024Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR024Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR024Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR024Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR024Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR024Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR024Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR024Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR024Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR024Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR024Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR024Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR024Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR024Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR024Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR024Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR024Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR024Q00P factoredHeatR024Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR024Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR024Q00Point00
  · exact factoredHeatR024Q00Point01
  · exact factoredHeatR024Q00Point02
  · exact factoredHeatR024Q00Point03
  · exact factoredHeatR024Q00Point04
  · exact factoredHeatR024Q00Point05
  · exact factoredHeatR024Q00Point06
  · exact factoredHeatR024Q00Point07
  · exact factoredHeatR024Q00Point08
  · exact factoredHeatR024Q00Point09
  · exact factoredHeatR024Q00Point10
  · exact factoredHeatR024Q00Point11
  · exact factoredHeatR024Q00Point12
  · exact factoredHeatR024Q00Point13
  · exact factoredHeatR024Q00Point14
  · exact factoredHeatR024Q00Point15
  · exact factoredHeatR024Q00Point16
  · exact factoredHeatR024Q00Point17
  · exact factoredHeatR024Q00Point18
  · exact factoredHeatR024Q00Point19
  · exact factoredHeatR024Q00Point20
  · exact factoredHeatR024Q00Point21
  · exact factoredHeatR024Q00Point22
  · exact factoredHeatR024Q00Point23
  · exact factoredHeatR024Q00Point24
  · exact factoredHeatR024Q00Point25
  · exact factoredHeatR024Q00Point26
  · exact factoredHeatR024Q00Point27
  · exact factoredHeatR024Q00Point28
  · exact factoredHeatR024Q00Point29
  · exact factoredHeatR024Q00Point30
  · exact factoredHeatR024Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR024Q00Bound {t a : ℝ} (tl : ((437/500):ℝ)≤t) (tu : t≤((7/8):ℝ)) (al : ((982778514048823/1649267441664000):ℝ)≤a) (au : a≤((984389126784823/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-1275145233244573066074824793433219/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR024Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (982778514048823/1649267441664000) (984389126784823/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR024Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR024Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR024Q00U (-1275145233244573066074824793433219/162259276829213363391578010288128) factoredHeatR024Q00Samples (by decide +kernel)

theorem factored_original_heat_024 {t a : ℝ} (tb : RealMem derivative_024.t t) (ab : RealMem derivative_024.a a) : reportedHeatPeriod t a≤(derivative_024.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((437/500):ℝ) ((7/8):ℝ) := by simpa [derivative_024,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((437/500):ℝ)<((7/8):ℝ)) tB
  have aB : a∈Icc ((982778514048823/1649267441664000):ℝ) ((984389126784823/1649267441664000):ℝ) := by simpa [derivative_024,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((982778514048823/1649267441664000):ℝ)<((984389126784823/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR024Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_024] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR025Q00T := Grid.ofRats (7/8) (219/250)
def factoredHeatR025Q00P : HeatGridParameters := ⟨⟨⟨⟨77126916205998568344300,77369598564372994496419,true⟩,⟨0,0,true⟩⟩, ⟨⟨1132199743778193280074439,1134054212759529743002437,true⟩,⟨0,0,true⟩⟩, ⟨(-1533552986079917660902432),(-1529844048117313454525512),true⟩, ⟨6162647285554279254143512,6200598777653161622028091,true⟩⟩, ⟨384742485905473259679426,409197264734849404147823,true⟩, ⟨596902254954603293720010,603759780500763719254400,true⟩, ⟨(-1466902384867834983986987),(-1453182683532000392663491),true⟩, ⟨(-2738160616163096020249439),(-2730931700841650041240255),true⟩, ⟨(-602224849369940838745844),(-600768352837906896588494),true⟩⟩
theorem factoredHeatR025Q00P_ok : factoredHeatR025Q00P.encloses (heatGridParameters factoredHeatR025Q00T (Grid.ofRats (327773133521409/549755813888000) (328310004433409/549755813888000))) := by decide +kernel
def factoredHeatR025Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨607576869146471140090144,608054246344738465539134,true⟩,⟨2403571138786787101061661,2405459640660728852428652,true⟩,⟨⟨714715434259646814763862,716569903240983277739339,true⟩,⟨973422398851916739465474,975276867833253202444536,true⟩⟩⟩
  | 1 => ⟨⟨9790631450120539695379,9844606493602755368868,true⟩,⟨607576869146471140090144,608054246344738465539134,true⟩,⟨⟨(-1146597850429927432733433),(-1141034443486055482834314),true⟩,⟨388608459011841083772160,394171865955713033660911,true⟩⟩⟩
  | 2 => ⟨⟨10065294496974331799,10200585225916260836,true⟩,⟨9790631450120539695379,9844606493602755368868,true⟩,⟨⟨(-35926496857798318701574),(-26654151951390881890824),true⟩,⟨(-1213156984408694268035150),(-1203884639502286831208199),true⟩⟩⟩
  | 3 => ⟨⟨660124698717740,676463803859407,true⟩,⟨10065294496974331799,10200585225916260836,true⟩,⟨⟨1156046702036239687552228,1169027984905182611262574,true⟩,⟨325184745603766108784894,338166028472709032483811,true⟩⟩⟩
  | 4 => ⟨⟨(-31597399209),37230456884,true⟩,⟨660124698717740,676463803859407,true⟩,⟨⟨(-672608139152299712070492),(-655917918320821301424175),true⟩,⟨1001732246020209371883048,1018422466851687782534119,true⟩⟩⟩
  | _ => ⟨⟨(-34359737631),34359739148,true⟩,⟨(-31597399209),37230456884,true⟩,⟨⟨(-775304204168084789929081),(-754905045374070892380763),true⟩,⟨(-946210557155714166677756),(-925811398361700269127084),true⟩⟩⟩
theorem factoredHeatR025Q00F_ok : ∀ n : Fin 6, (factoredHeatR025Q00F n).encloses (FactoredFrequency.build factoredHeatR025Q00T (Grid.ofRats (327773133521409/549755813888000) (328310004433409/549755813888000)) n) := by decide +kernel
def factoredHeatR025Q00U : ℕ → ℚ
  | 0 => (-21801527/500000)
  | 1 => (-3208801/100000)
  | 2 => (-4036719/200000)
  | 3 => (-2439447/200000)
  | 4 => (-760279/100000)
  | 5 => (-2585923/500000)
  | 6 => (-3844749/1000000)
  | 7 => (-646867/200000)
  | 8 => (-3177943/1000000)
  | 9 => (-3846797/1000000)
  | 10 => (-3008177/500000)
  | 11 => (-10241013/1000000)
  | 12 => (-15975469/1000000)
  | 13 => (-10933881/500000)
  | 14 => (-6242763/250000)
  | 15 => (-23263509/1000000)
  | 16 => (-18894709/1000000)
  | 17 => (-14453377/1000000)
  | 18 => (-11775947/1000000)
  | 19 => (-212853/20000)
  | 20 => (-10351073/1000000)
  | 21 => (-506521/50000)
  | 22 => (-1808397/200000)
  | 23 => (-6048013/1000000)
  | 24 => (73421/200000)
  | 25 => (680973/62500)
  | 26 => (24409489/1000000)
  | 27 => (282787/8000)
  | 28 => (8432033/250000)
  | 29 => (11788609/1000000)
  | 30 => (-21201489/1000000)
  | 31 => (-42862431/1000000)
  | _ => 0
theorem factoredHeatR025Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR025Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR025Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR025Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR025Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR025Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR025Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR025Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR025Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR025Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR025Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR025Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR025Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR025Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR025Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR025Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR025Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR025Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR025Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR025Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR025Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR025Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR025Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR025Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR025Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR025Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR025Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR025Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR025Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR025Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR025Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR025Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR025Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR025Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR025Q00P factoredHeatR025Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR025Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR025Q00Point00
  · exact factoredHeatR025Q00Point01
  · exact factoredHeatR025Q00Point02
  · exact factoredHeatR025Q00Point03
  · exact factoredHeatR025Q00Point04
  · exact factoredHeatR025Q00Point05
  · exact factoredHeatR025Q00Point06
  · exact factoredHeatR025Q00Point07
  · exact factoredHeatR025Q00Point08
  · exact factoredHeatR025Q00Point09
  · exact factoredHeatR025Q00Point10
  · exact factoredHeatR025Q00Point11
  · exact factoredHeatR025Q00Point12
  · exact factoredHeatR025Q00Point13
  · exact factoredHeatR025Q00Point14
  · exact factoredHeatR025Q00Point15
  · exact factoredHeatR025Q00Point16
  · exact factoredHeatR025Q00Point17
  · exact factoredHeatR025Q00Point18
  · exact factoredHeatR025Q00Point19
  · exact factoredHeatR025Q00Point20
  · exact factoredHeatR025Q00Point21
  · exact factoredHeatR025Q00Point22
  · exact factoredHeatR025Q00Point23
  · exact factoredHeatR025Q00Point24
  · exact factoredHeatR025Q00Point25
  · exact factoredHeatR025Q00Point26
  · exact factoredHeatR025Q00Point27
  · exact factoredHeatR025Q00Point28
  · exact factoredHeatR025Q00Point29
  · exact factoredHeatR025Q00Point30
  · exact factoredHeatR025Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR025Q00Bound {t a : ℝ} (tl : ((7/8):ℝ)≤t) (tu : t≤((219/250):ℝ)) (al : ((327773133521409/549755813888000):ℝ)≤a) (au : a≤((328310004433409/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-640166757458105690991357348509335/81129638414606681695789005144064):ℚ):ℝ) := by
  have ts : factoredHeatR025Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (327773133521409/549755813888000) (328310004433409/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR025Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR025Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR025Q00U (-640166757458105690991357348509335/81129638414606681695789005144064) factoredHeatR025Q00Samples (by decide +kernel)

theorem factored_original_heat_025 {t a : ℝ} (tb : RealMem derivative_025.t t) (ab : RealMem derivative_025.a a) : reportedHeatPeriod t a≤(derivative_025.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((7/8):ℝ) ((219/250):ℝ) := by simpa [derivative_025,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((7/8):ℝ)<((219/250):ℝ)) tB
  have aB : a∈Icc ((327773133521409/549755813888000):ℝ) ((328310004433409/549755813888000):ℝ) := by simpa [derivative_025,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((327773133521409/549755813888000):ℝ)<((328310004433409/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR025Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_025] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR026Q00T := Grid.ofRats (219/250) (877/1000)
def factoredHeatR026Q00P : HeatGridParameters := ⟨⟨⟨⟨76884995060470563288834,77126916206067287822056,true⟩,⟨0,0,true⟩⟩, ⟨⟨1132823659002460784499261,1134678127983797247427261,true⟩,⟨0,0,true⟩⟩, ⟨(-1532305155631382652052784),(-1528596217668778445675868),true⟩, ⟨6154422585262543274962286,6192268166058424748582212,true⟩⟩, ⟨385475838685099486077291,409909518557578044023742,true⟩, ⟨596881746038739511070376,603727018441154782313970,true⟩, ⟨(-1464902523028193398238600),(-1451223596380305976424239),true⟩, ⟨(-2734315554775580197314998),(-2727109853265312877732675),true⟩, ⟨(-601734827498685433698763),(-600278330966651491541416),true⟩⟩
theorem factoredHeatR026Q00P_ok : factoredHeatR026Q00P.encloses (heatGridParameters factoredHeatR026Q00T (Grid.ofRats (983861273098381/1649267441664000) (985471885834381/1649267441664000))) := by decide +kernel
def factoredHeatR026Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨607099866732250657633937,607576869146539859588815,true⟩,⟨2405459640660660132865494,2407349626343119164929077,true⟩,⟨⟨714212486311591309800724,716066955292927772776218,true⟩,⟨973791605514883928613751,975646074496220391592852,true⟩⟩⟩
  | 1 => ⟨⟨9736952335783882893135,9790631450189259172598,true⟩,⟨607099866732250657633937,607576869146539859588815,true⟩,⟨⟨(-1147202457566139476995153),(-1141639050622267527095850),true⟩,⟨386837052402774857121013,392400459346646807009917,true⟩⟩⟩
  | 2 => ⟨⟨9931798200741758994,10065294565693808537,true⟩,⟨9736952335783882893135,9790631450189259172598,true⟩,⟨⟨(-32807865123591726584255),(-23535520217184289773164),true⟩,⟨(-1213233703918078143001822),(-1203961359011670706174485),true⟩⟩⟩
  | 3 => ⟨⟨644245670129275,660193418194477,true⟩,⟨9931798200741758994,10065294565693808537,true⟩,⟨⟨1154840896646895290466865,1167822179515838214177298,true⟩,⟨329382394084115416814517,342363676953058340513596,true⟩⟩⟩
  | 4 => ⟨⟨(-31701686878),37122077528,true⟩,⟨644245670129275,660193418194477,true⟩,⟨⟨(-677292579442622308839082),(-660602358611143898193111),true⟩,⟨998635982263477979335472,1015326203094956389986093,true⟩⟩⟩
  | _ => ⟨⟨(-34359737671),34359739106,true⟩,⟨(-31701686878),37122077528,true⟩,⟨⟨(-769978172831778800845490),(-749579014037764903297264),true⟩,⟨(-950538947013391803132713),(-930139788219377905582000),true⟩⟩⟩
theorem factoredHeatR026Q00F_ok : ∀ n : Fin 6, (factoredHeatR026Q00F n).encloses (FactoredFrequency.build factoredHeatR026Q00T (Grid.ofRats (983861273098381/1649267441664000) (985471885834381/1649267441664000)) n) := by decide +kernel
def factoredHeatR026Q00U : ℕ → ℚ
  | 0 => (-21715021/500000)
  | 1 => (-801523/25000)
  | 2 => (-20233181/1000000)
  | 3 => (-3066347/250000)
  | 4 => (-3831883/500000)
  | 5 => (-5219623/1000000)
  | 6 => (-155169/40000)
  | 7 => (-407001/125000)
  | 8 => (-49777/15625)
  | 9 => (-95999/25000)
  | 10 => (-74877/12500)
  | 11 => (-10189091/1000000)
  | 12 => (-7947539/500000)
  | 13 => (-10884801/500000)
  | 14 => (-388833/15625)
  | 15 => (-929083/40000)
  | 16 => (-1890347/100000)
  | 17 => (-14485507/1000000)
  | 18 => (-1180989/100000)
  | 19 => (-5333727/500000)
  | 20 => (-5181787/500000)
  | 21 => (-5064933/500000)
  | 22 => (-9029143/1000000)
  | 23 => (-6025597/1000000)
  | 24 => (76917/200000)
  | 25 => (10884653/1000000)
  | 26 => (4868237/200000)
  | 27 => (35223619/1000000)
  | 28 => (33623123/1000000)
  | 29 => (5922249/500000)
  | 30 => (-10470231/500000)
  | 31 => (-21279597/500000)
  | _ => 0
theorem factoredHeatR026Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR026Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR026Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR026Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR026Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR026Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR026Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR026Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR026Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR026Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR026Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR026Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR026Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR026Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR026Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR026Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR026Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR026Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR026Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR026Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR026Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR026Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR026Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR026Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR026Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR026Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR026Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR026Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR026Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR026Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR026Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR026Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR026Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR026Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR026Q00P factoredHeatR026Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR026Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR026Q00Point00
  · exact factoredHeatR026Q00Point01
  · exact factoredHeatR026Q00Point02
  · exact factoredHeatR026Q00Point03
  · exact factoredHeatR026Q00Point04
  · exact factoredHeatR026Q00Point05
  · exact factoredHeatR026Q00Point06
  · exact factoredHeatR026Q00Point07
  · exact factoredHeatR026Q00Point08
  · exact factoredHeatR026Q00Point09
  · exact factoredHeatR026Q00Point10
  · exact factoredHeatR026Q00Point11
  · exact factoredHeatR026Q00Point12
  · exact factoredHeatR026Q00Point13
  · exact factoredHeatR026Q00Point14
  · exact factoredHeatR026Q00Point15
  · exact factoredHeatR026Q00Point16
  · exact factoredHeatR026Q00Point17
  · exact factoredHeatR026Q00Point18
  · exact factoredHeatR026Q00Point19
  · exact factoredHeatR026Q00Point20
  · exact factoredHeatR026Q00Point21
  · exact factoredHeatR026Q00Point22
  · exact factoredHeatR026Q00Point23
  · exact factoredHeatR026Q00Point24
  · exact factoredHeatR026Q00Point25
  · exact factoredHeatR026Q00Point26
  · exact factoredHeatR026Q00Point27
  · exact factoredHeatR026Q00Point28
  · exact factoredHeatR026Q00Point29
  · exact factoredHeatR026Q00Point30
  · exact factoredHeatR026Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR026Q00Bound {t a : ℝ} (tl : ((219/250):ℝ)≤t) (tu : t≤((877/1000):ℝ)) (al : ((983861273098381/1649267441664000):ℝ)≤a) (au : a≤((985471885834381/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2569825336225615096277138512095275/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR026Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (983861273098381/1649267441664000) (985471885834381/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR026Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR026Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR026Q00U (-2569825336225615096277138512095275/324518553658426726783156020576256) factoredHeatR026Q00Samples (by decide +kernel)

theorem factored_original_heat_026 {t a : ℝ} (tb : RealMem derivative_026.t t) (ab : RealMem derivative_026.a a) : reportedHeatPeriod t a≤(derivative_026.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((219/250):ℝ) ((877/1000):ℝ) := by simpa [derivative_026,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((219/250):ℝ)<((877/1000):ℝ)) tB
  have aB : a∈Icc ((983861273098381/1649267441664000):ℝ) ((985471885834381/1649267441664000):ℝ) := by simpa [derivative_026,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((983861273098381/1649267441664000):ℝ)<((985471885834381/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR026Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_026] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR027Q00T := Grid.ofRats (877/1000) (439/500)
def factoredHeatR027Q00P : HeatGridParameters := ⟨⟨⟨⟨76643832740052293455250,76884995060539282766584,true⟩,⟨0,0,true⟩⟩, ⟨⟨1133448710514045207344295,1135303179495381670272297,true⟩,⟨0,0,true⟩⟩, ⟨(-1531055052608213806362713),(-1527346114645609599985801),true⟩, ⟨6146210615442656682428718,6183950638849487737829411,true⟩⟩, ⟨386209759742628097112508,410622451440570808674749,true⟩, ⟨596857955730789111574490,603690996270107349355162,true⟩, ⟨(-1462910552861041762716866),(-1449272255495274168481108),true⟩, ⟨(-2730477005072426523868316),(-2723294436886609283069821),true⟩, ⟨(-601243913189458229110154),(-599787416657424286952810),true⟩⟩
theorem factoredHeatR027Q00P_ok : factoredHeatR027Q00P.encloses (heatGridParameters factoredHeatR027Q00T (Grid.ofRats (984404132502007/1649267441664000) (986014745238007/1649267441664000))) := by decide +kernel
def factoredHeatR027Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨606623238807769213126475,607099866732319377132584,true⟩,⟨2407349626343050445365673,2409241096999865006114757,true⟩,⟨⟨713708431386648461638512,715562900367984924613868,true⟩,⟨974161224259094171633981,976015693240430634612975,true⟩⟩⟩
  | 1 => ⟨⟨9683567528033132997439,9736952335852602370355,true⟩,⟨606623238807769213126475,607099866732319377132584,true⟩,⟨⟨(-1147805414983253578206720),(-1142242008039381628307567),true⟩,⟨385061483148313727463420,390624890092185677352136,true⟩⟩⟩
  | 2 => ⟨⟨9800072469796901894,9931798269461235731,true⟩,⟨9683567528033132997439,9736952335852602370355,true⟩,⟨⟨(-29683365584819180214748),(-20411020678411743404488),true⟩,⟨(-1213302493423193546746701),(-1204030148516786109920152),true⟩⟩⟩
  | 3 => ⟨⟨628748585173459,644314389606012,true⟩,⟨9800072469796901894,9931798269461235731,true⟩,⟨⟨1153617697132647161934816,1166598980001590085645476,true⟩,⟨333583291877010948354521,346564574745953872053888,true⟩⟩⟩
  | 4 => ⟨⟨(-31802037333),37017789859,true⟩,⟨628748585173459,644314389606012,true⟩,⟨⟨(-681971079568366022363807),(-665280858736887611718355),true⟩,⟨995512295301869266475921,1012202516133347677125916,true⟩⟩⟩
  | _ => ⟨⟨(-34359737709),34359739066,true⟩,⟨(-31802037333),37017789859,true⟩,⟨⟨(-764617888491568804996868),(-744218729697554907449259),true⟩,⟨(-954844831453992119466854),(-934445672659978221916629),true⟩⟩⟩
theorem factoredHeatR027Q00F_ok : ∀ n : Fin 6, (factoredHeatR027Q00F n).encloses (FactoredFrequency.build factoredHeatR027Q00T (Grid.ofRats (984404132502007/1649267441664000) (986014745238007/1649267441664000)) n) := by decide +kernel
def factoredHeatR027Q00U : ℕ → ℚ
  | 0 => (-8651371/200000)
  | 1 => (-32032711/1000000)
  | 2 => (-20281671/1000000)
  | 3 => (-6166393/500000)
  | 4 => (-7724271/1000000)
  | 5 => (-526709/100000)
  | 6 => (-3913481/1000000)
  | 7 => (-1638761/500000)
  | 8 => (-3193417/1000000)
  | 9 => (-1916551/500000)
  | 10 => (-372753/62500)
  | 11 => (-1267173/125000)
  | 12 => (-3163007/200000)
  | 13 => (-21671809/1000000)
  | 14 => (-24799703/1000000)
  | 15 => (-11595159/500000)
  | 16 => (-9455837/500000)
  | 17 => (-14517111/1000000)
  | 18 => (-148043/12500)
  | 19 => (-10691979/1000000)
  | 20 => (-1296983/125000)
  | 21 => (-2532289/250000)
  | 22 => (-901621/100000)
  | 23 => (-6003183/1000000)
  | 24 => (401977/1000000)
  | 25 => (10873659/1000000)
  | 26 => (4854607/200000)
  | 27 => (548428/15625)
  | 28 => (33518579/1000000)
  | 29 => (11899681/1000000)
  | 30 => (-20681457/1000000)
  | 31 => (-21128741/500000)
  | _ => 0
theorem factoredHeatR027Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR027Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR027Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR027Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR027Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR027Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR027Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR027Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR027Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR027Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR027Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR027Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR027Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR027Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR027Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR027Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR027Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR027Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR027Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR027Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR027Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR027Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR027Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR027Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR027Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR027Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR027Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR027Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR027Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR027Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR027Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR027Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR027Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR027Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR027Q00P factoredHeatR027Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR027Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR027Q00Point00
  · exact factoredHeatR027Q00Point01
  · exact factoredHeatR027Q00Point02
  · exact factoredHeatR027Q00Point03
  · exact factoredHeatR027Q00Point04
  · exact factoredHeatR027Q00Point05
  · exact factoredHeatR027Q00Point06
  · exact factoredHeatR027Q00Point07
  · exact factoredHeatR027Q00Point08
  · exact factoredHeatR027Q00Point09
  · exact factoredHeatR027Q00Point10
  · exact factoredHeatR027Q00Point11
  · exact factoredHeatR027Q00Point12
  · exact factoredHeatR027Q00Point13
  · exact factoredHeatR027Q00Point14
  · exact factoredHeatR027Q00Point15
  · exact factoredHeatR027Q00Point16
  · exact factoredHeatR027Q00Point17
  · exact factoredHeatR027Q00Point18
  · exact factoredHeatR027Q00Point19
  · exact factoredHeatR027Q00Point20
  · exact factoredHeatR027Q00Point21
  · exact factoredHeatR027Q00Point22
  · exact factoredHeatR027Q00Point23
  · exact factoredHeatR027Q00Point24
  · exact factoredHeatR027Q00Point25
  · exact factoredHeatR027Q00Point26
  · exact factoredHeatR027Q00Point27
  · exact factoredHeatR027Q00Point28
  · exact factoredHeatR027Q00Point29
  · exact factoredHeatR027Q00Point30
  · exact factoredHeatR027Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR027Q00Bound {t a : ℝ} (tl : ((877/1000):ℝ)≤t) (tu : t≤((439/500):ℝ)) (al : ((984404132502007/1649267441664000):ℝ)≤a) (au : a≤((986014745238007/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-1288938082490240941416139853115143/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR027Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (984404132502007/1649267441664000) (986014745238007/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR027Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR027Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR027Q00U (-1288938082490240941416139853115143/162259276829213363391578010288128) factoredHeatR027Q00Samples (by decide +kernel)

theorem factored_original_heat_027 {t a : ℝ} (tb : RealMem derivative_027.t t) (ab : RealMem derivative_027.a a) : reportedHeatPeriod t a≤(derivative_027.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((877/1000):ℝ) ((439/500):ℝ) := by simpa [derivative_027,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((877/1000):ℝ)<((439/500):ℝ)) tB
  have aB : a∈Icc ((984404132502007/1649267441664000):ℝ) ((986014745238007/1649267441664000):ℝ) := by simpa [derivative_027,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((984404132502007/1649267441664000):ℝ)<((986014745238007/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR027Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_027] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_023
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_024
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_025
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_026
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_027
