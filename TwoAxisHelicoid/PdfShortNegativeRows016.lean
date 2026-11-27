import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip016

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR016Q00T := Grid.ofRats (97/100) (49/50)
def shortNegativeR016Q00P : PrimalThetaParameters := ⟨⟨⟨55630226265185169028528,57405643536239648341027,true⟩,⟨0,0,true⟩⟩, ⟨⟨1193556254993271636869535,1200974130918411330140692,true⟩,⟨0,0,true⟩⟩, ⟨(-1410839963649760947311850),(-1396004211799550280249428),true⟩, ⟨5364766378557461252560127,5508715876376471295462526,true⟩⟩
theorem shortNegativeR016Q00P_ok : shortNegativeR016Q00P.encloses (primalThetaParameters shortNegativeR016Q00T (Grid.ofRats (345535914385319/549755813888000) (347683398033319/549755813888000))) := by decide +kernel

def shortNegativeR016Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨559921889962656369363473,564336820901635709484229,true⟩,⟨2589768349681569400589890,2610188427225637461864460,true⟩,⟨⟨659258012669062766132318,666675888594202459451329,true⟩,⟨1007219575682731051455065,1014637451607870744778935,true⟩⟩⟩
  | 1 => ⟨⟨5527060344982212683480,5839434514587257406845,true⟩,⟨559921889962656369363473,564336820901635709484229,true⟩,⟨⟨(-1202517326290296939366555),(-1180263698515015298439019),true⟩,⟨194032354291213459871571,216285982066495100785520,true⟩⟩⟩
  | 2 => ⟨⟨2510568835144796040,2869182277534794732,true⟩,⟨5527060344982212683480,5839434514587257406845,true⟩,⟨⟨268096507328652160453668,305185886954075748982363,true⟩,⟨(-1192997098994228456204987),(-1155907719368804867664076),true⟩⟩⟩
  | 3 => ⟨⟨52441703371081,66976626346574,true⟩,⟨2510568835144796040,2869182277534794732,true⟩,⟨⟨936958092776318798598116,988883224251884334721787,true⟩,⟨704985751681220472541282,756910883156786008661763,true⟩⟩⟩
  | 4 => ⟨⟨(-34309265089),34433903134,true⟩,⟨52441703371081,66976626346574,true⟩,⟨⟨(-1087525906686862909521002),(-1020765023361155425788181),true⟩,⟨558463267351796833565092,625224150677504317291546,true⟩⟩⟩
  | _ => ⟨⟨(-34359738366),34359738372,true⟩,⟨(-34309265089),34433903134,true⟩,⟨⟨(-163503184467087147744895),(-81906549291237716431479),true⟩,⟨(-1243480799781404552410917),(-1161884164605555121082636),true⟩⟩⟩
theorem shortNegativeR016Q00F_ok : ∀ n : Fin 6, (shortNegativeR016Q00F n).encloses (FactoredFrequency.build shortNegativeR016Q00T (Grid.ofRats (345535914385319/549755813888000) (347683398033319/549755813888000)) n) := by decide +kernel
def shortNegativeR016Q00L : ℕ → ℚ
  | 0 => (550889/1000000)
  | 1 => (181137/125000)
  | 2 => (1520817/1000000)
  | 3 => (569987/500000)
  | 4 => (112821/250000)
  | 5 => (-670833/1000000)
  | 6 => (-1101923/500000)
  | 7 => (-3972721/1000000)
  | 8 => (-2734651/500000)
  | 9 => (-741961/125000)
  | 10 => (-4650187/1000000)
  | 11 => (-2071929/1000000)
  | _ => 0
def shortNegativeR016Q00U : ℕ → ℚ
  | 0 => (291897/200000)
  | 1 => (483011/200000)
  | 2 => (155947/62500)
  | 3 => (522153/250000)
  | 4 => (677267/500000)
  | 5 => (369449/1000000)
  | 6 => (-471503/500000)
  | 7 => (-1248389/500000)
  | 8 => (-481507/125000)
  | 9 => (-193983/50000)
  | 10 => (-2311183/1000000)
  | 11 => (9649/1000000)
  | _ => 0
private theorem shortNegativeR016Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR016Q00L (0:Fin 12)) (shortNegativeR016Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR016Q00L (1:Fin 12)) (shortNegativeR016Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR016Q00L (2:Fin 12)) (shortNegativeR016Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR016Q00L (3:Fin 12)) (shortNegativeR016Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR016Q00L (4:Fin 12)) (shortNegativeR016Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR016Q00L (5:Fin 12)) (shortNegativeR016Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR016Q00L (6:Fin 12)) (shortNegativeR016Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR016Q00L (7:Fin 12)) (shortNegativeR016Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR016Q00L (8:Fin 12)) (shortNegativeR016Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR016Q00L (9:Fin 12)) (shortNegativeR016Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR016Q00L (10:Fin 12)) (shortNegativeR016Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR016Q00L (11:Fin 12)) (shortNegativeR016Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR016Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR016Q00P shortNegativeR016Q00F (shortNegativeNodes12 k)).re (shortNegativeR016Q00L k) (shortNegativeR016Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR016Q00Point00
  · exact shortNegativeR016Q00Point01
  · exact shortNegativeR016Q00Point02
  · exact shortNegativeR016Q00Point03
  · exact shortNegativeR016Q00Point04
  · exact shortNegativeR016Q00Point05
  · exact shortNegativeR016Q00Point06
  · exact shortNegativeR016Q00Point07
  · exact shortNegativeR016Q00Point08
  · exact shortNegativeR016Q00Point09
  · exact shortNegativeR016Q00Point10
  · exact shortNegativeR016Q00Point11

theorem shortNegativeR016Q00Bound {t a : ℝ} (tl : ((97/100):ℝ)≤t) (tu : t≤((49/50):ℝ)) (al : ((345535914385319/549755813888000):ℝ)≤a) (au : a≤((347683398033319/549755813888000):ℝ)) : (((-2244174162871041862355181108369543/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-232499262918855715755472373061767/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR016Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (345535914385319/549755813888000) (347683398033319/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR016Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR016Q00F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR016Q00L shortNegativeR016Q00U (-2244174162871041862355181108369543/1298074214633706907132624082305024) (-232499262918855715755472373061767/1298074214633706907132624082305024) shortNegativeR016Q00Samples (by decide +kernel)

def shortNegativeR016Q01T := Grid.ofRats (97/100) (49/50)
def shortNegativeR016Q01P : PrimalThetaParameters := ⟨⟨⟨55630226265185169028528,57405643536239648341027,true⟩,⟨0,0,true⟩⟩, ⟨⟨1200974130918342610660130,1208392006843482303931311,true⟩,⟨0,0,true⟩⟩, ⟨(-1396004211799618999730612),(-1381168459949408332668237),true⟩, ⟨5333469014705858489838320,5475917306261302277610796,true⟩⟩
theorem shortNegativeR016Q01P_ok : shortNegativeR016Q01P.encloses (primalThetaParameters shortNegativeR016Q01T (Grid.ofRats (347683398033319/549755813888000) (349830881681319/549755813888000))) := by decide +kernel

def shortNegativeR016Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨559921889962656369363473,564336820901635709484229,true⟩,⟨2589768349681569400589890,2610188427225637461864460,true⟩,⟨⟨653042591755303591083009,660460467680443284402281,true⟩,⟨1011268433974428619226868,1018686309899568312551157,true⟩⟩⟩
  | 1 => ⟨⟨5527060344982212683480,5839434514587257406845,true⟩,⟨559921889962656369363473,564336820901635709484229,true⟩,⟨⟨(-1206091792445580426169086),(-1183838164670298785241747),true⟩,⟨172067993219236138034459,194321620994517778947865,true⟩⟩⟩
  | 2 => ⟨⟨2510568835144796040,2869182277534794732,true⟩,⟨5527060344982212683480,5839434514587257406845,true⟩,⟨⟨303987715489781455847822,341077095115205044377319,true⟩,⟨(-1183651759940041826773909),(-1146562380314618238232814),true⟩⟩⟩
  | 3 => ⟨⟨52441703371081,66976626346574,true⟩,⟨2510568835144796040,2869182277534794732,true⟩,⟨⟨904684371117066968398069,956609502592632504522678,true⟩,⟨745657752977055278108429,797582884452620814230853,true⟩⟩⟩
  | 4 => ⟨⟨(-34309265089),34433903134,true⟩,⟨52441703371081,66976626346574,true⟩,⟨⟨(-1118585904997297501694830),(-1051825021671590017963562),true⟩,⟨499377232782083896360335,566138116107791380083997,true⟩⟩⟩
  | _ => ⟨⟨(-34359738366),34359738372,true⟩,⟨(-34309265089),34433903134,true⟩,⟨⟨(-82110173073085069928264),(-513537897235638616044),true⟩,⟨(-1249018069093120124979815),(-1167421433917270693651534),true⟩⟩⟩
theorem shortNegativeR016Q01F_ok : ∀ n : Fin 6, (shortNegativeR016Q01F n).encloses (FactoredFrequency.build shortNegativeR016Q01T (Grid.ofRats (347683398033319/549755813888000) (349830881681319/549755813888000)) n) := by decide +kernel
def shortNegativeR016Q01L : ℕ → ℚ
  | 0 => (14861/31250)
  | 1 => (348453/250000)
  | 2 => (744091/500000)
  | 3 => (563023/500000)
  | 4 => (45429/100000)
  | 5 => (-324311/500000)
  | 6 => (-2160983/1000000)
  | 7 => (-1956919/500000)
  | 8 => (-1349749/250000)
  | 9 => (-5897449/1000000)
  | 10 => (-2332713/500000)
  | 11 => (-2130543/1000000)
  | _ => 0
def shortNegativeR016Q01U : ℕ → ℚ
  | 0 => (686079/500000)
  | 1 => (2350347/1000000)
  | 2 => (1227957/500000)
  | 3 => (414077/200000)
  | 4 => (338681/250000)
  | 5 => (194039/500000)
  | 6 => (-9063/10000)
  | 7 => (-152877/62500)
  | 8 => (-760721/200000)
  | 9 => (-1940393/500000)
  | 10 => (-118517/50000)
  | 11 => (-22189/250000)
  | _ => 0
private theorem shortNegativeR016Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR016Q01L (0:Fin 12)) (shortNegativeR016Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR016Q01L (1:Fin 12)) (shortNegativeR016Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR016Q01L (2:Fin 12)) (shortNegativeR016Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR016Q01L (3:Fin 12)) (shortNegativeR016Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR016Q01L (4:Fin 12)) (shortNegativeR016Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR016Q01L (5:Fin 12)) (shortNegativeR016Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR016Q01L (6:Fin 12)) (shortNegativeR016Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR016Q01L (7:Fin 12)) (shortNegativeR016Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR016Q01L (8:Fin 12)) (shortNegativeR016Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR016Q01L (9:Fin 12)) (shortNegativeR016Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR016Q01L (10:Fin 12)) (shortNegativeR016Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR016Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR016Q01L (11:Fin 12)) (shortNegativeR016Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR016Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR016Q01P shortNegativeR016Q01F (shortNegativeNodes12 k)).re (shortNegativeR016Q01L k) (shortNegativeR016Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR016Q01Point00
  · exact shortNegativeR016Q01Point01
  · exact shortNegativeR016Q01Point02
  · exact shortNegativeR016Q01Point03
  · exact shortNegativeR016Q01Point04
  · exact shortNegativeR016Q01Point05
  · exact shortNegativeR016Q01Point06
  · exact shortNegativeR016Q01Point07
  · exact shortNegativeR016Q01Point08
  · exact shortNegativeR016Q01Point09
  · exact shortNegativeR016Q01Point10
  · exact shortNegativeR016Q01Point11

theorem shortNegativeR016Q01Bound {t a : ℝ} (tl : ((97/100):ℝ)≤t) (tu : t≤((49/50):ℝ)) (al : ((347683398033319/549755813888000):ℝ)≤a) (au : a≤((349830881681319/549755813888000):ℝ)) : (((-2244174162871041862355181108369543/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-232499262918855715755472373061767/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR016Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (347683398033319/549755813888000) (349830881681319/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR016Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR016Q01F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR016Q01L shortNegativeR016Q01U (-2244174162871041862355181108369543/1298074214633706907132624082305024) (-232499262918855715755472373061767/1298074214633706907132624082305024) shortNegativeR016Q01Samples (by decide +kernel)

theorem short_original_negative_016 {t a : ℝ} (tb : RealMem negative_016.t t) (ab : RealMem negative_016.a a) : RealMem negative_016.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((97/100):ℝ) ((49/50):ℝ) := by simpa [negative_016,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((97/100):ℝ)<((49/50):ℝ)) tB
  have aB : a∈Icc ((345535914385319/549755813888000):ℝ) ((349830881681319/549755813888000):ℝ) := by simpa [negative_016,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((345535914385319/549755813888000):ℝ)<((349830881681319/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR016Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_016,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR016Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_016,RealMem] using v

def shortNegativeR017Q00T := Grid.ofRats (49/50) (99/100)
def shortNegativeR017Q00P : PrimalThetaParameters := ⟨⟨⟨53909718342687533260365,55630226265253888506057,true⟩,⟨0,0,true⟩⟩, ⟨⟨1201051127962107531764280,1208469003887247225035461,true⟩,⟨0,0,true⟩⟩, ⟨(-1395850217712089157522312),(-1381014465861878490459937),true⟩, ⟨5296813821077703297243158,5436424809897396486307748,true⟩⟩
theorem shortNegativeR017Q00P_ok : shortNegativeR017Q00P.encloses (primalThetaParameters shortNegativeR017Q00T (Grid.ofRats (347705688766421/549755813888000) (349853172414421/549755813888000))) := by decide +kernel

def shortNegativeR017Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨555541497998474014437915,559921889962725088860677,true⟩,⟨2610188427225568742292971,2630769515142226387220095,true⟩,⟨⟨652977946045737388741077,660395821970877082060088,true⟩,⟨1011310260724018030404362,1018728136649157723728332,true⟩⟩⟩
  | 1 => ⟨⟨5231396290363749479292,5527060345050932160501,true⟩,⟨555541497998474014437915,559921889962725088860677,true⟩,⟨⟨(-1206126773917919288119064),(-1183873146142637647191699),true⟩,⟨171839666262510679715808,194093294037792320629240,true⟩⟩⟩
  | 2 => ⟨⟨2196777832754893699,2510568903864272777,true⟩,⟨5231396290363749479292,5527060345050932160501,true⟩,⟨⟨304358730166069875669608,341448109791493464199086,true⟩,⟨(-1183548989674694904923064),(-1146459610049271316381999),true⟩⟩⟩
  | 3 => ⟨⟨41101642058281,52510422847818,true⟩,⟨2196777832754893699,2510568903864272777,true⟩,⟨⟨904340264656214582479560,956265396131780118604897,true⟩,⟨746072589609316900272350,797997721084882436395510,true⟩⟩⟩
  | 4 => ⟨⟨(-34325388473),34410211648,true⟩,⟨41101642058281,52510422847818,true⟩,⟨⟨(-1118891110936116139273319),(-1052130227610408655541190),true⟩,⟨498755090156641338813419,565515973482348822537925,true⟩⟩⟩
  | _ => ⟨⟨(-34359738367),34359738371,true⟩,⟨(-34325388473),34410211648,true⟩,⟨⟨(-81263690190140612705913),332944985708818606309,true⟩,⟨(-1249046715456122492172827),(-1167450080280273060844536),true⟩⟩⟩
theorem shortNegativeR017Q00F_ok : ∀ n : Fin 6, (shortNegativeR017Q00F n).encloses (FactoredFrequency.build shortNegativeR017Q00T (Grid.ofRats (347705688766421/549755813888000) (349853172414421/549755813888000)) n) := by decide +kernel
def shortNegativeR017Q00L : ℕ → ℚ
  | 0 => (332969/1000000)
  | 1 => (627133/500000)
  | 2 => (1370849/1000000)
  | 3 => (20521/20000)
  | 4 => (182603/500000)
  | 5 => (-364059/500000)
  | 6 => (-2214963/1000000)
  | 7 => (-3923393/1000000)
  | 8 => (-5352081/1000000)
  | 9 => (-5827851/1000000)
  | 10 => (-2320791/500000)
  | 11 => (-2201409/1000000)
  | _ => 0
def shortNegativeR017Q00U : ℕ → ℚ
  | 0 => (610829/500000)
  | 1 => (441013/200000)
  | 2 => (2335023/1000000)
  | 3 => (1969009/1000000)
  | 4 => (1265757/1000000)
  | 5 => (156007/500000)
  | 6 => (-48031/50000)
  | 7 => (-2465447/1000000)
  | 8 => (-15121/4000)
  | 9 => (-963063/250000)
  | 10 => (-240249/100000)
  | 11 => (-26019/125000)
  | _ => 0
private theorem shortNegativeR017Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR017Q00L (0:Fin 12)) (shortNegativeR017Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR017Q00L (1:Fin 12)) (shortNegativeR017Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR017Q00L (2:Fin 12)) (shortNegativeR017Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR017Q00L (3:Fin 12)) (shortNegativeR017Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR017Q00L (4:Fin 12)) (shortNegativeR017Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR017Q00L (5:Fin 12)) (shortNegativeR017Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR017Q00L (6:Fin 12)) (shortNegativeR017Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR017Q00L (7:Fin 12)) (shortNegativeR017Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR017Q00L (8:Fin 12)) (shortNegativeR017Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR017Q00L (9:Fin 12)) (shortNegativeR017Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR017Q00L (10:Fin 12)) (shortNegativeR017Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR017Q00L (11:Fin 12)) (shortNegativeR017Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR017Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR017Q00P shortNegativeR017Q00F (shortNegativeNodes12 k)).re (shortNegativeR017Q00L k) (shortNegativeR017Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR017Q00Point00
  · exact shortNegativeR017Q00Point01
  · exact shortNegativeR017Q00Point02
  · exact shortNegativeR017Q00Point03
  · exact shortNegativeR017Q00Point04
  · exact shortNegativeR017Q00Point05
  · exact shortNegativeR017Q00Point06
  · exact shortNegativeR017Q00Point07
  · exact shortNegativeR017Q00Point08
  · exact shortNegativeR017Q00Point09
  · exact shortNegativeR017Q00Point10
  · exact shortNegativeR017Q00Point11

theorem shortNegativeR017Q00Bound {t a : ℝ} (tl : ((49/50):ℝ)≤t) (tu : t≤((99/100):ℝ)) (al : ((347705688766421/549755813888000):ℝ)≤a) (au : a≤((349853172414421/549755813888000):ℝ)) : (((-1157873505273372093755091993761133/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-175654714515730610334667191883117/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR017Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (347705688766421/549755813888000) (349853172414421/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR017Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR017Q00F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR017Q00L shortNegativeR017Q00U (-1157873505273372093755091993761133/649037107316853453566312041152512) (-175654714515730610334667191883117/649037107316853453566312041152512) shortNegativeR017Q00Samples (by decide +kernel)

def shortNegativeR017Q01T := Grid.ofRats (49/50) (99/100)
def shortNegativeR017Q01P : PrimalThetaParameters := ⟨⟨⟨53909718342687533260365,55630226265253888506057,true⟩,⟨0,0,true⟩⟩, ⟨⟨1208469003887178505554875,1215886879812318198826080,true⟩,⟨0,0,true⟩⟩, ⟨(-1381014465861947209941074),(-1366178714011736542878746),true⟩, ⟨5266089657906323812999890,5404252917939845960911142,true⟩⟩
theorem shortNegativeR017Q01P_ok : shortNegativeR017Q01P.encloses (primalThetaParameters shortNegativeR017Q01T (Grid.ofRats (349853172414421/549755813888000) (352000656062421/549755813888000))) := by decide +kernel

def shortNegativeR017Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨555541497998474014437915,559921889962725088860677,true⟩,⟨2610188427225568742292971,2630769515142226387220095,true⟩,⟨⟨646737543380908285173028,654155419306047978492139,true⟩,⟨1015320508245335998651767,1022738384170475691975965,true⟩⟩⟩
  | 1 => ⟨⟨5231396290363749479292,5527060345050932160501,true⟩,⟨555541497998474014437915,559921889962725088860677,true⟩,⟨⟨(-1209292133752639513632083),(-1187038505977357872704765),true⟩,⟨149812626908294239193570,172066254683575880106607,true⟩⟩⟩
  | 2 => ⟨⟨2196777832754893699,2510568903864272777,true⟩,⟨5231396290363749479292,5527060345050932160501,true⟩,⟨⟨339943055065992384576121,377032434691415973106017,true⟩,⟨(-1173095760187116680430927),(-1136006380561693091890076),true⟩⟩⟩
  | 3 => ⟨⟨41101642058281,52510422847818,true⟩,⟨2196777832754893699,2510568903864272777,true⟩,⟨⟨870332428311006031344519,922257559786571567469915,true⟩,⟨785306144970318292779714,837231276445883828903944,true⟩⟩⟩
  | 4 => ⟨⟨(-34325388473),34410211648,true⟩,⟨41101642058281,52510422847818,true⟩,⟨⟨(-1146607688089909399796516),(-1079846804764201916065523),true⟩,⟨438028865779562390677667,504789749105269874399826,true⟩⟩⟩
  | _ => ⟨⟨(-34359738367),34359738371,true⟩,⟨(-34325388473),34410211648,true⟩,⟨⟨317454525241286032905,81914089701090717343892,true⟩,⟨(-1249024757711811889962088),(-1167428122535962458635041),true⟩⟩⟩
theorem shortNegativeR017Q01F_ok : ∀ n : Fin 6, (shortNegativeR017Q01F n).encloses (FactoredFrequency.build shortNegativeR017Q01T (Grid.ofRats (349853172414421/549755813888000) (352000656062421/549755813888000)) n) := by decide +kernel
def shortNegativeR017Q01L : ℕ → ℚ
  | 0 => (260743/1000000)
  | 1 => (1200107/1000000)
  | 2 => (167293/125000)
  | 3 => (1011979/1000000)
  | 4 => (367963/1000000)
  | 5 => (-706383/1000000)
  | 6 => (-271631/125000)
  | 7 => (-3865927/1000000)
  | 8 => (-5283387/1000000)
  | 9 => (-144729/25000)
  | 10 => (-581689/125000)
  | 11 => (-1127787/500000)
  | _ => 0
def shortNegativeR017Q01U : ℕ → ℚ
  | 0 => (1137603/1000000)
  | 1 => (85659/40000)
  | 2 => (2295791/1000000)
  | 3 => (30476/15625)
  | 4 => (632763/500000)
  | 5 => (65997/200000)
  | 6 => (-462481/500000)
  | 7 => (-302017/125000)
  | 8 => (-746599/200000)
  | 9 => (-3852049/1000000)
  | 10 => (-2457359/1000000)
  | 11 => (-301073/1000000)
  | _ => 0
private theorem shortNegativeR017Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR017Q01L (0:Fin 12)) (shortNegativeR017Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR017Q01L (1:Fin 12)) (shortNegativeR017Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR017Q01L (2:Fin 12)) (shortNegativeR017Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR017Q01L (3:Fin 12)) (shortNegativeR017Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR017Q01L (4:Fin 12)) (shortNegativeR017Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR017Q01L (5:Fin 12)) (shortNegativeR017Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR017Q01L (6:Fin 12)) (shortNegativeR017Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR017Q01L (7:Fin 12)) (shortNegativeR017Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR017Q01L (8:Fin 12)) (shortNegativeR017Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR017Q01L (9:Fin 12)) (shortNegativeR017Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR017Q01L (10:Fin 12)) (shortNegativeR017Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR017Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR017Q01L (11:Fin 12)) (shortNegativeR017Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR017Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR017Q01P shortNegativeR017Q01F (shortNegativeNodes12 k)).re (shortNegativeR017Q01L k) (shortNegativeR017Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR017Q01Point00
  · exact shortNegativeR017Q01Point01
  · exact shortNegativeR017Q01Point02
  · exact shortNegativeR017Q01Point03
  · exact shortNegativeR017Q01Point04
  · exact shortNegativeR017Q01Point05
  · exact shortNegativeR017Q01Point06
  · exact shortNegativeR017Q01Point07
  · exact shortNegativeR017Q01Point08
  · exact shortNegativeR017Q01Point09
  · exact shortNegativeR017Q01Point10
  · exact shortNegativeR017Q01Point11

theorem shortNegativeR017Q01Bound {t a : ℝ} (tl : ((49/50):ℝ)≤t) (tu : t≤((99/100):ℝ)) (al : ((349853172414421/549755813888000):ℝ)≤a) (au : a≤((352000656062421/549755813888000):ℝ)) : (((-1157873505273372093755091993761133/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-175654714515730610334667191883117/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR017Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (349853172414421/549755813888000) (352000656062421/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR017Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR017Q01F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR017Q01L shortNegativeR017Q01U (-1157873505273372093755091993761133/649037107316853453566312041152512) (-175654714515730610334667191883117/649037107316853453566312041152512) shortNegativeR017Q01Samples (by decide +kernel)

theorem short_original_negative_017 {t a : ℝ} (tb : RealMem negative_017.t t) (ab : RealMem negative_017.a a) : RealMem negative_017.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((49/50):ℝ) ((99/100):ℝ) := by simpa [negative_017,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((49/50):ℝ)<((99/100):ℝ)) tB
  have aB : a∈Icc ((347705688766421/549755813888000):ℝ) ((352000656062421/549755813888000):ℝ) := by simpa [negative_017,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((347705688766421/549755813888000):ℝ)<((352000656062421/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR017Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_017,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR017Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_017,RealMem] using v

def shortNegativeR018Q00T := Grid.ofRats (99/100) 1
def shortNegativeR018Q00P : PrimalThetaParameters := ⟨⟨⟨52242421555756100267423,53909718342756252737875,true⟩,⟨0,0,true⟩⟩, ⟨⟨1208677655949820743572692,1216095531874960436843898,true⟩,⟨0,0,true⟩⟩, ⟨(-1380597161736662733905438),(-1365761409886452066843113),true⟩, ⟨5229961640296422951158945,5365392903023819215526788,true⟩⟩
theorem shortNegativeR018Q00P_ok : shortNegativeR018Q00P.encloses (primalThetaParameters shortNegativeR018Q00T (Grid.ofRats (1049740732282651/1649267441664000) (1056183183226651/1649267441664000))) := by decide +kernel

def shortNegativeR018Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨551195374803032156320458,555541497998542733934944,true⟩,⟨2630769515142157667647873,2651512882982905157532376,true⟩,⟨⟨646561656404853227152299,653979532329992920471353,true⟩,⟨1015432755538359022658506,1022850631463498715982674,true⟩⟩⟩
  | 1 => ⟨⟨4951548461322097392706,5231396290432468956301,true⟩,⟨551195374803032156320458,555541497998542733934944,true⟩,⟨⟨(-1209375304172131415562866),(-1187121676396849774636054),true⟩,⟨149192220733460756735464,171445848508742397647987,true⟩⟩⟩
  | 2 => ⟨⟨1922206942737488000,2196777901474370436,true⟩,⟨4951548461322097392706,5231396290432468956301,true⟩,⟨⟨340939258281754101386912,378028637907177689916530,true⟩,⟨(-1172785968052802403773399),(-1135696588427378815232846),true⟩⟩⟩
  | 3 => ⟨⟨32212164553757,41170361535018,true⟩,⟨1922206942737488000,2196777901474370436,true⟩,⟨⟨869351639651978772517619,921276771127544308643149,true⟩,⟨786388411954866288654457,838313543430431824778852,true⟩⟩⟩
  | 4 => ⟨⟨(-34336361339),34394088264,true⟩,⟨32212164553757,41170361535018,true⟩,⟨⟨(-1147338602037217886279774),(-1080577718711510402548679),true⟩,⟨436299081274079640369046,503059964599787124091268,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738370,true⟩,⟨(-34336361339),34394088264,true⟩,⟨⟨2611223950169688325053,84207859126019119636394,true⟩,⟨(-1248944521089121575147316),(-1167347885913272143819946),true⟩⟩⟩
theorem shortNegativeR018Q00F_ok : ∀ n : Fin 6, (shortNegativeR018Q00F n).encloses (FactoredFrequency.build shortNegativeR018Q00T (Grid.ofRats (1049740732282651/1649267441664000) (1056183183226651/1649267441664000)) n) := by decide +kernel
def shortNegativeR018Q00L : ℕ → ℚ
  | 0 => (31139/250000)
  | 1 => (1063663/1000000)
  | 2 => (1221797/1000000)
  | 3 => (14254/15625)
  | 4 => (27961/100000)
  | 5 => (-784313/1000000)
  | 6 => (-2225201/1000000)
  | 7 => (-3874667/1000000)
  | 8 => (-163679/31250)
  | 9 => (-1144319/200000)
  | 10 => (-1157153/250000)
  | 11 => (-1160397/500000)
  | _ => 0
def shortNegativeR018Q00U : ℕ → ℚ
  | 0 => (993441/1000000)
  | 1 => (399823/200000)
  | 2 => (2175441/1000000)
  | 3 => (462261/250000)
  | 4 => (294237/250000)
  | 5 => (25497/100000)
  | 6 => (-977941/1000000)
  | 7 => (-2434551/1000000)
  | 8 => (-742077/200000)
  | 9 => (-956033/250000)
  | 10 => (-621519/250000)
  | 11 => (-82559/200000)
  | _ => 0
private theorem shortNegativeR018Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR018Q00L (0:Fin 12)) (shortNegativeR018Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR018Q00L (1:Fin 12)) (shortNegativeR018Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR018Q00L (2:Fin 12)) (shortNegativeR018Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR018Q00L (3:Fin 12)) (shortNegativeR018Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR018Q00L (4:Fin 12)) (shortNegativeR018Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR018Q00L (5:Fin 12)) (shortNegativeR018Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR018Q00L (6:Fin 12)) (shortNegativeR018Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR018Q00L (7:Fin 12)) (shortNegativeR018Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR018Q00L (8:Fin 12)) (shortNegativeR018Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR018Q00L (9:Fin 12)) (shortNegativeR018Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR018Q00L (10:Fin 12)) (shortNegativeR018Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR018Q00L (11:Fin 12)) (shortNegativeR018Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR018Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR018Q00P shortNegativeR018Q00F (shortNegativeNodes12 k)).re (shortNegativeR018Q00L k) (shortNegativeR018Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR018Q00Point00
  · exact shortNegativeR018Q00Point01
  · exact shortNegativeR018Q00Point02
  · exact shortNegativeR018Q00Point03
  · exact shortNegativeR018Q00Point04
  · exact shortNegativeR018Q00Point05
  · exact shortNegativeR018Q00Point06
  · exact shortNegativeR018Q00Point07
  · exact shortNegativeR018Q00Point08
  · exact shortNegativeR018Q00Point09
  · exact shortNegativeR018Q00Point10
  · exact shortNegativeR018Q00Point11

theorem shortNegativeR018Q00Bound {t a : ℝ} (tl : ((99/100):ℝ)≤t) (tu : t≤(1:ℝ)) (al : ((1049740732282651/1649267441664000):ℝ)≤a) (au : a≤((1056183183226651/1649267441664000):ℝ)) : (((-4748687303922370955247771439666951/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-953138051009083111163906367493895/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR018Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1049740732282651/1649267441664000) (1056183183226651/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR018Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR018Q00F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR018Q00L shortNegativeR018Q00U (-4748687303922370955247771439666951/2596148429267413814265248164610048) (-953138051009083111163906367493895/2596148429267413814265248164610048) shortNegativeR018Q00Samples (by decide +kernel)

def shortNegativeR018Q01T := Grid.ofRats (99/100) 1
def shortNegativeR018Q01P : PrimalThetaParameters := ⟨⟨⟨52242421555756100267423,53909718342756252737875,true⟩,⟨0,0,true⟩⟩, ⟨⟨1216095531874891717363288,1223513407800031410634517,true⟩,⟨0,0,true⟩⟩, ⟨(-1365761409886520786324201),(-1350925658036310119261922),true⟩, ⟨5199814885010205246045175,5333850424809461290196928,true⟩⟩
theorem shortNegativeR018Q01P_ok : shortNegativeR018Q01P.encloses (primalThetaParameters shortNegativeR018Q01T (Grid.ofRats (1056183183226651/1649267441664000) (1062625634170651/1649267441664000))) := by decide +kernel

def shortNegativeR018Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨551195374803032156320458,555541497998542733934944,true⟩,⟨2630769515142157667647873,2651512882982905157532376,true⟩,⟨⟨640296079372215828621474,647713955297355521940423,true⟩,⟨1019403555841765102673403,1026821431766904795997626,true⟩⟩⟩
  | 1 => ⟨⟨4951548461322097392706,5231396290432468956301,true⟩,⟨551195374803032156320458,555541497998542733934944,true⟩,⟨⟨(-1212123248233780110273629),(-1189869620458498469346515),true⟩,⟨127109223449814916618213,149362851225096557530689,true⟩⟩⟩
  | 2 => ⟨⟨1922206942737488000,2196777901474370436,true⟩,⟨4951548461322097392706,5231396290432468956301,true⟩,⟨⟨376176215455507163019826,413265595080930751550377,true⟩,⟨(-1161215702954788761876584),(-1124126323329365173335742),true⟩⟩⟩
  | 3 => ⟨⟨32212164553757,41170361535018,true⟩,⟨1922206942737488000,2196777901474370436,true⟩,⟨⟨833644981206168097666174,885570112681733633793188,true⟩,⟨824082434581556929683099,876007566057122465809993,true⟩⟩⟩
  | 4 => ⟨⟨(-34336361339),34394088264,true⟩,⟨32212164553757,41170361535018,true⟩,⟨⟨(-1171564538611556204362319),(-1104803655285848720632002),true⟩,⟨374097899827794803755744,440858783153502287476000,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738370,true⟩,⟨(-34336361339),34394088264,true⟩,⟨⟨83994498687162080320881,165591133863011511632819,true⟩,⟨(-1243265943071885656011486),(-1161669307896036224684717),true⟩⟩⟩
theorem shortNegativeR018Q01F_ok : ∀ n : Fin 6, (shortNegativeR018Q01F n).encloses (FactoredFrequency.build shortNegativeR018Q01T (Grid.ofRats (1056183183226651/1649267441664000) (1062625634170651/1649267441664000)) n) := by decide +kernel
def shortNegativeR018Q01L : ℕ → ℚ
  | 0 => (866/15625)
  | 1 => (1010723/1000000)
  | 2 => (118951/100000)
  | 3 => (898093/1000000)
  | 4 => (14107/50000)
  | 5 => (-381523/500000)
  | 6 => (-109211/50000)
  | 7 => (-3818637/1000000)
  | 8 => (-1034123/200000)
  | 9 => (-710317/125000)
  | 10 => (-463747/100000)
  | 11 => (-94829/40000)
  | _ => 0
def shortNegativeR018Q01U : ℕ → ℚ
  | 0 => (228161/250000)
  | 1 => (1936743/1000000)
  | 2 => (2136311/1000000)
  | 3 => (1830237/1000000)
  | 4 => (1176323/1000000)
  | 5 => (272293/1000000)
  | 6 => (-943321/1000000)
  | 7 => (-1193261/500000)
  | 8 => (-3664307/1000000)
  | 9 => (-3822697/1000000)
  | 10 => (-2536893/1000000)
  | 11 => (-125171/250000)
  | _ => 0
private theorem shortNegativeR018Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR018Q01L (0:Fin 12)) (shortNegativeR018Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR018Q01L (1:Fin 12)) (shortNegativeR018Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR018Q01L (2:Fin 12)) (shortNegativeR018Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR018Q01L (3:Fin 12)) (shortNegativeR018Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR018Q01L (4:Fin 12)) (shortNegativeR018Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR018Q01L (5:Fin 12)) (shortNegativeR018Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR018Q01L (6:Fin 12)) (shortNegativeR018Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR018Q01L (7:Fin 12)) (shortNegativeR018Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR018Q01L (8:Fin 12)) (shortNegativeR018Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR018Q01L (9:Fin 12)) (shortNegativeR018Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR018Q01L (10:Fin 12)) (shortNegativeR018Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR018Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR018Q01L (11:Fin 12)) (shortNegativeR018Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR018Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR018Q01P shortNegativeR018Q01F (shortNegativeNodes12 k)).re (shortNegativeR018Q01L k) (shortNegativeR018Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR018Q01Point00
  · exact shortNegativeR018Q01Point01
  · exact shortNegativeR018Q01Point02
  · exact shortNegativeR018Q01Point03
  · exact shortNegativeR018Q01Point04
  · exact shortNegativeR018Q01Point05
  · exact shortNegativeR018Q01Point06
  · exact shortNegativeR018Q01Point07
  · exact shortNegativeR018Q01Point08
  · exact shortNegativeR018Q01Point09
  · exact shortNegativeR018Q01Point10
  · exact shortNegativeR018Q01Point11

theorem shortNegativeR018Q01Bound {t a : ℝ} (tl : ((99/100):ℝ)≤t) (tu : t≤(1:ℝ)) (al : ((1056183183226651/1649267441664000):ℝ)≤a) (au : a≤((1062625634170651/1649267441664000):ℝ)) : (((-4748687303922370955247771439666951/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-953138051009083111163906367493895/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR018Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1056183183226651/1649267441664000) (1062625634170651/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR018Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR018Q01F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR018Q01L shortNegativeR018Q01U (-4748687303922370955247771439666951/2596148429267413814265248164610048) (-953138051009083111163906367493895/2596148429267413814265248164610048) shortNegativeR018Q01Samples (by decide +kernel)

theorem short_original_negative_018 {t a : ℝ} (tb : RealMem negative_018.t t) (ab : RealMem negative_018.a a) : RealMem negative_018.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((99/100):ℝ) (1:ℝ) := by simpa [negative_018,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((99/100):ℝ)<(1:ℝ)) tB
  have aB : a∈Icc ((1049740732282651/1649267441664000):ℝ) ((1062625634170651/1649267441664000):ℝ) := by simpa [negative_018,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1049740732282651/1649267441664000):ℝ)<((1062625634170651/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR018Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_018,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR018Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_018,RealMem] using v

def shortNegativeR019Q00T := Grid.ofRats 1 (101/100)
def shortNegativeR019Q00P : PrimalThetaParameters := ⟨⟨⟨50626690213074241601716,52242421555824819744916,true⟩,⟨0,0,true⟩⟩, ⟨⟨1216438485687104455601178,1223856361612244148872409,true⟩,⟨0,0,true⟩⟩, ⟨(-1365075502262095309848417),(-1350239750411884642786140),true⟩, ⟨5164198550399340038464978,5295602891744282216733294,true⟩⟩
theorem shortNegativeR019Q00P_ok : shortNegativeR019Q00P.encloses (primalThetaParameters shortNegativeR019Q00T (Grid.ofRats (1056481039800899/1649267441664000) (1062923490744899/1649267441664000))) := by decide +kernel

def shortNegativeR019Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨546883252284223834701576,551195374803100875817353,true⟩,⟨2651512882982836437959432,2672419810309467072336906,true⟩,⟨⟨640005812055939721345634,647423687981079414664579,true⟩,⟨1019586209069561179031120,1027004084994700872355331,true⟩⟩⟩
  | 1 => ⟨⟨4686670786149894561082,4951548461390816869702,true⟩,⟨546883252284223834701576,551195374803100875817353,true⟩,⟨⟨(-1212240459647547530010133),(-1189986831872265889082733),true⟩,⟨126087060411747202838402,148340688187028843751152,true⟩⟩⟩
  | 2 => ⟨⟨1681954121366672660,1922207011456964737,true⟩,⟨4686670786149894561082,4951548461390816869702,true⟩,⟨⟨377796609509336191618022,414885989134759780148680,true⟩,⟨(-1160654672162316198151690),(-1123565292536892609610776),true⟩⟩⟩
  | 3 => ⟨⟨25243700440230,32280884030494,true⟩,⟨1681954121366672660,1922207011456964737,true⟩,⟨⟨831955273847933126767236,883880405323498662894473,true⟩,⟨825787760268307333120916,877712891743872869248073,true⟩⟩⟩
  | 4 => ⟨⟨(-34343828990),34383115398,true⟩,⟨25243700440230,32280884030494,true⟩,⟨⟨(-1172601186279844486005880),(-1105840302954137002276467),true⟩,⟨371190605701156319799779,437951489026863803519078,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34343828990),34383115398,true⟩,⟨⟨87746223930635546189087,169342859106484977500770,true⟩,⟨(-1242870669061281769872924),(-1161274033885432338546465),true⟩⟩⟩
theorem shortNegativeR019Q00F_ok : ∀ n : Fin 6, (shortNegativeR019Q00F n).encloses (FactoredFrequency.build shortNegativeR019Q00T (Grid.ofRats (1056481039800899/1649267441664000) (1062923490744899/1649267441664000)) n) := by decide +kernel
def shortNegativeR019Q00L : ℕ → ℚ
  | 0 => (-76387/1000000)
  | 1 => (877561/1000000)
  | 2 => (537003/500000)
  | 3 => (798843/1000000)
  | 4 => (2433/12500)
  | 5 => (-419683/500000)
  | 6 => (-2234567/1000000)
  | 7 => (-59789/15625)
  | 8 => (-5128897/1000000)
  | 9 => (-5616889/1000000)
  | 10 => (-4611599/1000000)
  | 11 => (-607647/250000)
  | _ => 0
def shortNegativeR019Q00U : ℕ → ℚ
  | 0 => (774703/1000000)
  | 1 => (1797493/1000000)
  | 2 => (2016761/1000000)
  | 3 => (1728979/1000000)
  | 4 => (1088259/1000000)
  | 5 => (1587/8000)
  | 6 => (-31093/31250)
  | 7 => (-1202107/500000)
  | 8 => (-3642411/1000000)
  | 9 => (-3795369/1000000)
  | 10 => (-320301/125000)
  | 11 => (-302573/500000)
  | _ => 0
private theorem shortNegativeR019Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR019Q00L (0:Fin 12)) (shortNegativeR019Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR019Q00L (1:Fin 12)) (shortNegativeR019Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR019Q00L (2:Fin 12)) (shortNegativeR019Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR019Q00L (3:Fin 12)) (shortNegativeR019Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR019Q00L (4:Fin 12)) (shortNegativeR019Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR019Q00L (5:Fin 12)) (shortNegativeR019Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR019Q00L (6:Fin 12)) (shortNegativeR019Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR019Q00L (7:Fin 12)) (shortNegativeR019Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR019Q00L (8:Fin 12)) (shortNegativeR019Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR019Q00L (9:Fin 12)) (shortNegativeR019Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR019Q00L (10:Fin 12)) (shortNegativeR019Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR019Q00L (11:Fin 12)) (shortNegativeR019Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR019Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR019Q00P shortNegativeR019Q00F (shortNegativeNodes12 k)).re (shortNegativeR019Q00L k) (shortNegativeR019Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR019Q00Point00
  · exact shortNegativeR019Q00Point01
  · exact shortNegativeR019Q00Point02
  · exact shortNegativeR019Q00Point03
  · exact shortNegativeR019Q00Point04
  · exact shortNegativeR019Q00Point05
  · exact shortNegativeR019Q00Point06
  · exact shortNegativeR019Q00Point07
  · exact shortNegativeR019Q00Point08
  · exact shortNegativeR019Q00Point09
  · exact shortNegativeR019Q00Point10
  · exact shortNegativeR019Q00Point11

theorem shortNegativeR019Q00Bound {t a : ℝ} (tl : (1:ℝ)≤t) (tu : t≤((101/100):ℝ)) (al : ((1056481039800899/1649267441664000):ℝ)≤a) (au : a≤((1062923490744899/1649267441664000):ℝ)) : (((-4886104301638048223558350070373461/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1170421775528351721115142148349013/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR019Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1056481039800899/1649267441664000) (1062923490744899/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR019Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR019Q00F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR019Q00L shortNegativeR019Q00U (-4886104301638048223558350070373461/2596148429267413814265248164610048) (-1170421775528351721115142148349013/2596148429267413814265248164610048) shortNegativeR019Q00Samples (by decide +kernel)

def shortNegativeR019Q01T := Grid.ofRats 1 (101/100)
def shortNegativeR019Q01P : PrimalThetaParameters := ⟨⟨⟨50626690213074241601716,52242421555824819744916,true⟩,⟨0,0,true⟩⟩, ⟨⟨1223856361612175429391774,1231274237537315122663028,true⟩,⟨0,0,true⟩⟩, ⟨(-1350239750411953362267179),(-1335403998561742695204950),true⟩, ⟨5134632874564720411793164,5264692051710812667024693,true⟩⟩
theorem shortNegativeR019Q01P_ok : shortNegativeR019Q01P.encloses (primalThetaParameters shortNegativeR019Q01T (Grid.ofRats (1062923490744899/1649267441664000) (1069365941688899/1649267441664000))) := by decide +kernel

def shortNegativeR019Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨546883252284223834701576,551195374803100875817353,true⟩,⟨2651512882982836437959432,2672419810309467072336906,true⟩,⟨⟨633714873323456422247119,641132749248596115566376,true⟩,⟨1023516705280675560382481,1030934581205815253707127,true⟩⟩⟩
  | 1 => ⟨⟨4686670786149894561082,4951548461390816869702,true⟩,⟨546883252284223834701576,551195374803100875817353,true⟩,⟨⟨(-1214562627854228793222166),(-1192309000078947152295407),true⟩,⟨103955239419896157133653,126208867195177798045426,true⟩⟩⟩
  | 2 => ⟨⟨1681954121366672660,1922207011456964737,true⟩,⟨4686670786149894561082,4951548461390816869702,true⟩,⟨⟨412644097144927285591863,449733476770350874122248,true⟩,⟨(-1147959523845319432548531),(-1110870144219895844008539),true⟩⟩⟩
  | 3 => ⟨⟨25243700440230,32280884030494,true⟩,⟨1681954121366672660,1922207011456964737,true⟩,⟨⟨794591365691503685497058,846516497167069221625039,true⟩,⟨861839711206157482737319,913764842681723018866231,true⟩⟩⟩
  | 4 => ⟨⟨(-34343828990),34383115398,true⟩,⟨25243700440230,32280884030494,true⟩,⟨⟨(-1193194933861511244844633),(-1126434050535803761115807),true⟩,⟨307694302369701609648617,374455185695409093366172,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34343828990),34383115398,true⟩,⟨⟨168526007558818443176117,250122642734667874487807,true⟩,⟨(-1231464082709591203161915),(-1149867447533741771836718),true⟩⟩⟩
theorem shortNegativeR019Q01F_ok : ∀ n : Fin 6, (shortNegativeR019Q01F n).encloses (FactoredFrequency.build shortNegativeR019Q01T (Grid.ofRats (1062923490744899/1649267441664000) (1069365941688899/1649267441664000)) n) := by decide +kernel
def shortNegativeR019Q01L : ℕ → ℚ
  | 0 => (-3603/25000)
  | 1 => (825919/1000000)
  | 2 => (521009/500000)
  | 3 => (784633/1000000)
  | 4 => (196961/1000000)
  | 5 => (-818559/1000000)
  | 6 => (-548627/250000)
  | 7 => (-3771811/1000000)
  | 8 => (-5075853/1000000)
  | 9 => (-5577541/1000000)
  | 10 => (-4617609/1000000)
  | 11 => (-1238247/500000)
  | _ => 0
def shortNegativeR019Q01U : ℕ → ℚ
  | 0 => (34857/50000)
  | 1 => (1736429/1000000)
  | 2 => (61807/31250)
  | 3 => (1709963/1000000)
  | 4 => (543631/500000)
  | 5 => (215059/1000000)
  | 6 => (-961381/1000000)
  | 7 => (-2357597/1000000)
  | 8 => (-3597491/1000000)
  | 9 => (-474099/125000)
  | 10 => (-1304699/500000)
  | 11 => (-688197/1000000)
  | _ => 0
private theorem shortNegativeR019Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR019Q01L (0:Fin 12)) (shortNegativeR019Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR019Q01L (1:Fin 12)) (shortNegativeR019Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR019Q01L (2:Fin 12)) (shortNegativeR019Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR019Q01L (3:Fin 12)) (shortNegativeR019Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR019Q01L (4:Fin 12)) (shortNegativeR019Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR019Q01L (5:Fin 12)) (shortNegativeR019Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR019Q01L (6:Fin 12)) (shortNegativeR019Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR019Q01L (7:Fin 12)) (shortNegativeR019Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR019Q01L (8:Fin 12)) (shortNegativeR019Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR019Q01L (9:Fin 12)) (shortNegativeR019Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR019Q01L (10:Fin 12)) (shortNegativeR019Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR019Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR019Q01L (11:Fin 12)) (shortNegativeR019Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR019Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR019Q01P shortNegativeR019Q01F (shortNegativeNodes12 k)).re (shortNegativeR019Q01L k) (shortNegativeR019Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR019Q01Point00
  · exact shortNegativeR019Q01Point01
  · exact shortNegativeR019Q01Point02
  · exact shortNegativeR019Q01Point03
  · exact shortNegativeR019Q01Point04
  · exact shortNegativeR019Q01Point05
  · exact shortNegativeR019Q01Point06
  · exact shortNegativeR019Q01Point07
  · exact shortNegativeR019Q01Point08
  · exact shortNegativeR019Q01Point09
  · exact shortNegativeR019Q01Point10
  · exact shortNegativeR019Q01Point11

theorem shortNegativeR019Q01Bound {t a : ℝ} (tl : (1:ℝ)≤t) (tu : t≤((101/100):ℝ)) (al : ((1062923490744899/1649267441664000):ℝ)≤a) (au : a≤((1069365941688899/1649267441664000):ℝ)) : (((-4886104301638048223558350070373461/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1170421775528351721115142148349013/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR019Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1062923490744899/1649267441664000) (1069365941688899/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR019Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR019Q01F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR019Q01L shortNegativeR019Q01U (-4886104301638048223558350070373461/2596148429267413814265248164610048) (-1170421775528351721115142148349013/2596148429267413814265248164610048) shortNegativeR019Q01Samples (by decide +kernel)

theorem short_original_negative_019 {t a : ℝ} (tb : RealMem negative_019.t t) (ab : RealMem negative_019.a a) : RealMem negative_019.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc (1:ℝ) ((101/100):ℝ) := by simpa [negative_019,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : (1:ℝ)<((101/100):ℝ)) tB
  have aB : a∈Icc ((1056481039800899/1649267441664000):ℝ) ((1069365941688899/1649267441664000):ℝ) := by simpa [negative_019,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1056481039800899/1649267441664000):ℝ)<((1069365941688899/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR019Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_019,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR019Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_019,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_016
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_017
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_018
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_019
