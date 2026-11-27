import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes24

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredNegativeR001Q00T := Grid.ofRats (361/400) (181/200)
def factoredNegativeR001Q00P : PrimalThetaParameters := ⟨⟨⟨70410763381639383038665,70965945565613753793798,true⟩,⟨0,0,true⟩⟩, ⟨⟨1149339000712214007567711,1151193469693550470495763,true⟩,⟨0,0,true⟩⟩, ⟨(-1499274472211876205915780),(-1495565534249271999538969),true⟩, ⟨5934860843350577736046146,5979685408718067469578124,true⟩⟩
theorem factoredNegativeR001Q00P_ok : factoredNegativeR001Q00P.encloses (primalThetaParameters factoredNegativeR001Q00T (Grid.ofRats (998204904599263/1649267441664000) (999815517335263/1649267441664000))) := by decide +kernel

def factoredNegativeR001Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨593894773123415194107316,595062028358776401149706,true⟩,⟨2456049231307688745659327,2460876410217419491188106,true⟩,⟨⟨700830368895322278666962,702684837876658741642504,true⟩,⟨983469993980061341947993,985324462961397804927493,true⟩⟩⟩
  | 1 => ⟨⟨8347734016744946042003,8463261290470203228354,true⟩,⟨593894773123415194107316,595062028358776401149706,true⟩,⟨⟨(-1162204954968109991743726),(-1156641548024238041844906),true⟩,⟨339620634751596800233948,345184041695468750121516,true⟩⟩⟩
  | 2 => ⟨⟨6833876089168285755,7065836811931122188,true⟩,⟨8347734016744946042003,8463261290470203228354,true⟩,⟨⟨49747933591133448665035,59020278497540885476407,true⟩,⟨(-1212338125064302715561551),(-1203065780157895278734307),true⟩⟩⟩
  | 3 => ⟨⟨325806093639472,346324234422978,true⟩,⟨6833876089168285755,7065836811931122188,true⟩,⟨⟨1117464897250924048494031,1130446180119866972208165,true⟩,⟨438734677240607162179727,451715960109550085884531,true⟩⟩⟩
  | 4 => ⟨⟨(-33454876472),35355983762,true⟩,⟨325806093639472,346324234422978,true⟩,⟨⟨(-795739927818976731204271),(-779049706987498320557404),true⟩,⟨908993997470447642621542,925684218301926053270192,true⟩⟩⟩
  | _ => ⟨⟨(-34359738222),34359738537,true⟩,⟨(-33454876472),35355983762,true⟩,⟨⟨(-620639400280852530232357),(-600240241486838632683511),true⟩,⟨(-1053686456367772423538793),(-1033287297573758525983988),true⟩⟩⟩
theorem factoredNegativeR001Q00F_ok : ∀ n : Fin 6, (factoredNegativeR001Q00F n).encloses (FactoredFrequency.build factoredNegativeR001Q00T (Grid.ofRats (998204904599263/1649267441664000) (999815517335263/1649267441664000)) n) := by decide +kernel
def factoredNegativeR001Q00L : ℕ → ℚ
  | 0 => (2732697/1000000)
  | 1 => (1592067/500000)
  | 2 => (411389/125000)
  | 3 => (1589903/500000)
  | 4 => (2944949/1000000)
  | 5 => (2639639/1000000)
  | 6 => (2283189/1000000)
  | 7 => (937529/500000)
  | 8 => (350357/250000)
  | 9 => (41691/50000)
  | 10 => (157703/1000000)
  | 11 => (-646369/1000000)
  | 12 => (-63027/40000)
  | 13 => (-260691/100000)
  | 14 => (-3678969/1000000)
  | 15 => (-4693933/1000000)
  | 16 => (-13737/2500)
  | 17 => (-5882577/1000000)
  | 18 => (-354717/62500)
  | 19 => (-601141/125000)
  | 20 => (-2681/800)
  | 21 => (-312199/200000)
  | 22 => (3263/15625)
  | 23 => (1647617/1000000)
  | _ => 0
def factoredNegativeR001Q00U : ℕ → ℚ
  | 0 => (187133/62500)
  | 1 => (3448961/1000000)
  | 2 => (711333/200000)
  | 3 => (3443127/1000000)
  | 4 => (640573/200000)
  | 5 => (2889961/1000000)
  | 6 => (2526129/1000000)
  | 7 => (2109757/1000000)
  | 8 => (813897/500000)
  | 9 => (33439/31250)
  | 10 => (82153/200000)
  | 11 => (-181489/500000)
  | 12 => (-627291/500000)
  | 13 => (-449281/200000)
  | 14 => (-3282369/1000000)
  | 15 => (-4250077/1000000)
  | 16 => (-4978359/1000000)
  | 17 => (-8461/1600)
  | 18 => (-2503053/500000)
  | 19 => (-406269/100000)
  | 20 => (-2568171/1000000)
  | 21 => (-397569/500000)
  | 22 => (227869/250000)
  | 23 => (451713/200000)
  | _ => 0
theorem factoredNegativeR001Q00Point00 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (0:Fin 24))).re (factoredNegativeR001Q00L (0:Fin 24)) (factoredNegativeR001Q00U (0:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point01 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (1:Fin 24))).re (factoredNegativeR001Q00L (1:Fin 24)) (factoredNegativeR001Q00U (1:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point02 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (2:Fin 24))).re (factoredNegativeR001Q00L (2:Fin 24)) (factoredNegativeR001Q00U (2:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point03 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (3:Fin 24))).re (factoredNegativeR001Q00L (3:Fin 24)) (factoredNegativeR001Q00U (3:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point04 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (4:Fin 24))).re (factoredNegativeR001Q00L (4:Fin 24)) (factoredNegativeR001Q00U (4:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point05 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (5:Fin 24))).re (factoredNegativeR001Q00L (5:Fin 24)) (factoredNegativeR001Q00U (5:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point06 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (6:Fin 24))).re (factoredNegativeR001Q00L (6:Fin 24)) (factoredNegativeR001Q00U (6:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point07 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (7:Fin 24))).re (factoredNegativeR001Q00L (7:Fin 24)) (factoredNegativeR001Q00U (7:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point08 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (8:Fin 24))).re (factoredNegativeR001Q00L (8:Fin 24)) (factoredNegativeR001Q00U (8:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point09 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (9:Fin 24))).re (factoredNegativeR001Q00L (9:Fin 24)) (factoredNegativeR001Q00U (9:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point10 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (10:Fin 24))).re (factoredNegativeR001Q00L (10:Fin 24)) (factoredNegativeR001Q00U (10:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point11 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (11:Fin 24))).re (factoredNegativeR001Q00L (11:Fin 24)) (factoredNegativeR001Q00U (11:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point12 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (12:Fin 24))).re (factoredNegativeR001Q00L (12:Fin 24)) (factoredNegativeR001Q00U (12:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point13 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (13:Fin 24))).re (factoredNegativeR001Q00L (13:Fin 24)) (factoredNegativeR001Q00U (13:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point14 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (14:Fin 24))).re (factoredNegativeR001Q00L (14:Fin 24)) (factoredNegativeR001Q00U (14:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point15 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (15:Fin 24))).re (factoredNegativeR001Q00L (15:Fin 24)) (factoredNegativeR001Q00U (15:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point16 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (16:Fin 24))).re (factoredNegativeR001Q00L (16:Fin 24)) (factoredNegativeR001Q00U (16:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point17 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (17:Fin 24))).re (factoredNegativeR001Q00L (17:Fin 24)) (factoredNegativeR001Q00U (17:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point18 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (18:Fin 24))).re (factoredNegativeR001Q00L (18:Fin 24)) (factoredNegativeR001Q00U (18:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point19 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (19:Fin 24))).re (factoredNegativeR001Q00L (19:Fin 24)) (factoredNegativeR001Q00U (19:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point20 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (20:Fin 24))).re (factoredNegativeR001Q00L (20:Fin 24)) (factoredNegativeR001Q00U (20:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point21 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (21:Fin 24))).re (factoredNegativeR001Q00L (21:Fin 24)) (factoredNegativeR001Q00U (21:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point22 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (22:Fin 24))).re (factoredNegativeR001Q00L (22:Fin 24)) (factoredNegativeR001Q00U (22:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Point23 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 (23:Fin 24))).re (factoredNegativeR001Q00L (23:Fin 24)) (factoredNegativeR001Q00U (23:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q00Samples : ∀ k : Fin 24, containedInReported (sampledFactoredPrimal factoredNegativeR001Q00P factoredNegativeR001Q00F (factoredNodes24 k)).re (factoredNegativeR001Q00L k) (factoredNegativeR001Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredNegativeR001Q00Point00
  · exact factoredNegativeR001Q00Point01
  · exact factoredNegativeR001Q00Point02
  · exact factoredNegativeR001Q00Point03
  · exact factoredNegativeR001Q00Point04
  · exact factoredNegativeR001Q00Point05
  · exact factoredNegativeR001Q00Point06
  · exact factoredNegativeR001Q00Point07
  · exact factoredNegativeR001Q00Point08
  · exact factoredNegativeR001Q00Point09
  · exact factoredNegativeR001Q00Point10
  · exact factoredNegativeR001Q00Point11
  · exact factoredNegativeR001Q00Point12
  · exact factoredNegativeR001Q00Point13
  · exact factoredNegativeR001Q00Point14
  · exact factoredNegativeR001Q00Point15
  · exact factoredNegativeR001Q00Point16
  · exact factoredNegativeR001Q00Point17
  · exact factoredNegativeR001Q00Point18
  · exact factoredNegativeR001Q00Point19
  · exact factoredNegativeR001Q00Point20
  · exact factoredNegativeR001Q00Point21
  · exact factoredNegativeR001Q00Point22
  · exact factoredNegativeR001Q00Point23

def factoredNegativeR001Q01T := Grid.ofRats (361/400) (181/200)
def factoredNegativeR001Q01P : PrimalThetaParameters := ⟨⟨⟨70410763381639383038665,70965945565613753793798,true⟩,⟨0,0,true⟩⟩, ⟨⟨1151193469693481751015360,1153047938674818213943418,true⟩,⟨0,0,true⟩⟩, ⟨(-1495565534249340719020470),(-1491856596286736512643671),true⟩, ⟨5925882121196136153318992,5970586295612517053156702,true⟩⟩
theorem factoredNegativeR001Q01P_ok : factoredNegativeR001Q01P.encloses (primalThetaParameters factoredNegativeR001Q01T (Grid.ofRats (999815517335263/1649267441664000) (1001426130071263/1649267441664000))) := by decide +kernel

def factoredNegativeR001Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨593894773123415194107316,595062028358776401149706,true⟩,⟨2456049231307688745659327,2460876410217419491188106,true⟩,⟨⟨699319497399700606386401,701173966381037069361879,true⟩,⟨984545318048346332514657,986399787029682795494118,true⟩⟩⟩
  | 1 => ⟨⟨8347734016744946042003,8463261290470203228354,true⟩,⟨593894773123415194107316,595062028358776401149706,true⟩,⟨⟨(-1163768388194263101644311),(-1158204981250391151745572),true⟩,⟨334281428935574162276737,339844835879446112164138,true⟩⟩⟩
  | 2 => ⟨⟨6833876089168285755,7065836811931122188,true⟩,⟨8347734016744946042003,8463261290470203228354,true⟩,⟨⟨59009201105400832867450,68281546011808269679073,true⟩,⟨(-1211885485460044322779385),(-1202613140553636885952023),true⟩⟩⟩
  | 3 => ⟨⟨325806093639472,346324234422978,true⟩,⟨6833876089168285755,7065836811931122188,true⟩,⟨⟨1112619423125414394419509,1125600705994357318134023,true⟩,⟨450777661350306119749114,463758944219249043454524,true⟩⟩⟩
  | 4 => ⟨⟨(-33454876472),35355983762,true⟩,⟨325806093639472,346324234422978,true⟩,⟨⟨(-808329112741864037504558),(-791638891910385626858323),true⟩,⟨898036284667576489991781,914726505499054900639475,true⟩⟩⟩
  | _ => ⟨⟨(-34359738222),34359738537,true⟩,⟨(-33454876472),35355983762,true⟩,⟨⟨(-602945757183672062919614),(-582546598389658165371484),true⟩,⟨(-1063837850365844769023107),(-1043438691571830871468632),true⟩⟩⟩
theorem factoredNegativeR001Q01F_ok : ∀ n : Fin 6, (factoredNegativeR001Q01F n).encloses (FactoredFrequency.build factoredNegativeR001Q01T (Grid.ofRats (999815517335263/1649267441664000) (1001426130071263/1649267441664000)) n) := by decide +kernel
def factoredNegativeR001Q01L : ℕ → ℚ
  | 0 => (2707331/1000000)
  | 1 => (1581811/500000)
  | 2 => (3275469/1000000)
  | 3 => (99011/31250)
  | 4 => (293687/100000)
  | 5 => (105371/40000)
  | 6 => (570033/250000)
  | 7 => (234267/125000)
  | 8 => (1402661/1000000)
  | 9 => (13084/15625)
  | 10 => (8191/50000)
  | 11 => (-637387/1000000)
  | 12 => (-24434/15625)
  | 13 => (-518461/200000)
  | 14 => (-3662397/1000000)
  | 15 => (-58449/12500)
  | 16 => (-5478509/1000000)
  | 17 => (-5871033/1000000)
  | 18 => (-5671887/1000000)
  | 19 => (-9631/2000)
  | 20 => (-1683883/500000)
  | 21 => (-99089/62500)
  | 22 => (180671/1000000)
  | 23 => (404931/250000)
  | _ => 0
def factoredNegativeR001Q01U : ℕ → ℚ
  | 0 => (185497/62500)
  | 1 => (3427759/1000000)
  | 2 => (708091/200000)
  | 3 => (3431227/1000000)
  | 4 => (199653/62500)
  | 5 => (57687/20000)
  | 6 => (504579/200000)
  | 7 => (2108709/1000000)
  | 8 => (203617/125000)
  | 9 => (1073521/1000000)
  | 10 => (416789/1000000)
  | 11 => (-70851/200000)
  | 12 => (-621513/500000)
  | 13 => (-1116109/500000)
  | 14 => (-1633133/500000)
  | 15 => (-2117219/500000)
  | 16 => (-4964691/1000000)
  | 17 => (-5279417/1000000)
  | 18 => (-5005381/1000000)
  | 19 => (-4072147/1000000)
  | 20 => (-2587837/1000000)
  | 21 => (-411301/500000)
  | 22 => (440049/500000)
  | 23 => (222783/100000)
  | _ => 0
theorem factoredNegativeR001Q01Point00 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (0:Fin 24))).re (factoredNegativeR001Q01L (0:Fin 24)) (factoredNegativeR001Q01U (0:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point01 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (1:Fin 24))).re (factoredNegativeR001Q01L (1:Fin 24)) (factoredNegativeR001Q01U (1:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point02 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (2:Fin 24))).re (factoredNegativeR001Q01L (2:Fin 24)) (factoredNegativeR001Q01U (2:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point03 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (3:Fin 24))).re (factoredNegativeR001Q01L (3:Fin 24)) (factoredNegativeR001Q01U (3:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point04 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (4:Fin 24))).re (factoredNegativeR001Q01L (4:Fin 24)) (factoredNegativeR001Q01U (4:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point05 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (5:Fin 24))).re (factoredNegativeR001Q01L (5:Fin 24)) (factoredNegativeR001Q01U (5:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point06 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (6:Fin 24))).re (factoredNegativeR001Q01L (6:Fin 24)) (factoredNegativeR001Q01U (6:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point07 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (7:Fin 24))).re (factoredNegativeR001Q01L (7:Fin 24)) (factoredNegativeR001Q01U (7:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point08 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (8:Fin 24))).re (factoredNegativeR001Q01L (8:Fin 24)) (factoredNegativeR001Q01U (8:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point09 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (9:Fin 24))).re (factoredNegativeR001Q01L (9:Fin 24)) (factoredNegativeR001Q01U (9:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point10 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (10:Fin 24))).re (factoredNegativeR001Q01L (10:Fin 24)) (factoredNegativeR001Q01U (10:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point11 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (11:Fin 24))).re (factoredNegativeR001Q01L (11:Fin 24)) (factoredNegativeR001Q01U (11:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point12 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (12:Fin 24))).re (factoredNegativeR001Q01L (12:Fin 24)) (factoredNegativeR001Q01U (12:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point13 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (13:Fin 24))).re (factoredNegativeR001Q01L (13:Fin 24)) (factoredNegativeR001Q01U (13:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point14 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (14:Fin 24))).re (factoredNegativeR001Q01L (14:Fin 24)) (factoredNegativeR001Q01U (14:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point15 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (15:Fin 24))).re (factoredNegativeR001Q01L (15:Fin 24)) (factoredNegativeR001Q01U (15:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point16 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (16:Fin 24))).re (factoredNegativeR001Q01L (16:Fin 24)) (factoredNegativeR001Q01U (16:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point17 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (17:Fin 24))).re (factoredNegativeR001Q01L (17:Fin 24)) (factoredNegativeR001Q01U (17:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point18 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (18:Fin 24))).re (factoredNegativeR001Q01L (18:Fin 24)) (factoredNegativeR001Q01U (18:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point19 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (19:Fin 24))).re (factoredNegativeR001Q01L (19:Fin 24)) (factoredNegativeR001Q01U (19:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point20 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (20:Fin 24))).re (factoredNegativeR001Q01L (20:Fin 24)) (factoredNegativeR001Q01U (20:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point21 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (21:Fin 24))).re (factoredNegativeR001Q01L (21:Fin 24)) (factoredNegativeR001Q01U (21:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point22 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (22:Fin 24))).re (factoredNegativeR001Q01L (22:Fin 24)) (factoredNegativeR001Q01U (22:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Point23 : containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 (23:Fin 24))).re (factoredNegativeR001Q01L (23:Fin 24)) (factoredNegativeR001Q01U (23:Fin 24))=true := by decide +kernel
theorem factoredNegativeR001Q01Samples : ∀ k : Fin 24, containedInReported (sampledFactoredPrimal factoredNegativeR001Q01P factoredNegativeR001Q01F (factoredNodes24 k)).re (factoredNegativeR001Q01L k) (factoredNegativeR001Q01U k)=true := by
  intro k
  fin_cases k
  · exact factoredNegativeR001Q01Point00
  · exact factoredNegativeR001Q01Point01
  · exact factoredNegativeR001Q01Point02
  · exact factoredNegativeR001Q01Point03
  · exact factoredNegativeR001Q01Point04
  · exact factoredNegativeR001Q01Point05
  · exact factoredNegativeR001Q01Point06
  · exact factoredNegativeR001Q01Point07
  · exact factoredNegativeR001Q01Point08
  · exact factoredNegativeR001Q01Point09
  · exact factoredNegativeR001Q01Point10
  · exact factoredNegativeR001Q01Point11
  · exact factoredNegativeR001Q01Point12
  · exact factoredNegativeR001Q01Point13
  · exact factoredNegativeR001Q01Point14
  · exact factoredNegativeR001Q01Point15
  · exact factoredNegativeR001Q01Point16
  · exact factoredNegativeR001Q01Point17
  · exact factoredNegativeR001Q01Point18
  · exact factoredNegativeR001Q01Point19
  · exact factoredNegativeR001Q01Point20
  · exact factoredNegativeR001Q01Point21
  · exact factoredNegativeR001Q01Point22
  · exact factoredNegativeR001Q01Point23

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factoredNegativeR001Q00Samples
#print axioms TwoAxisHelicoid.PdfVertical.factoredNegativeR001Q01Samples
