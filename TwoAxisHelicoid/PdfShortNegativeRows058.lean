import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip056

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR058Q00T := Grid.ofRats (139/100) (7/5)
def shortNegativeR058Q00P : PrimalThetaParameters := ⟨⟨⟨14868691741727495394482,15343220318930398927008,true⟩,⟨0,0,true⟩⟩, ⟨⟨1740153966354544008318078,1759934968821468657908674,true⟩,⟨0,0,true⟩⟩, ⟨(-317644540927216204411283),(-278082535993435624717022),true⟩, ⟨3275413771745658878478474,3402037533525073110022888,true⟩⟩
theorem shortNegativeR058Q00P_ok : shortNegativeR058Q00P.encloses (primalThetaParameters shortNegativeR058Q00T (Grid.ofRats (503776583148099/549755813888000) (1528509618628297/1649267441664000))) := by decide +kernel

def shortNegativeR058Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨402594585049692254360065,405769005127340645772757,true⟩,⟨3601806985904101536045025,3630206892003773110943041,true⟩,⟨⟨138664839990660866563138,158445842457585516203045,true⟩,⟨1189873203803778432471971,1209654206270703082126357,true⟩⟩⟩
  | 1 => ⟨⟨549133054212335263357,580168536269218714054,true⟩,⟨402594585049692254360065,405769005127340645772757,true⟩,⟨⟨(-466364778793091718554872),(-407021771392455208655486),true⟩,⟨(-1156969432741106565887934),(-1097626425340470055979038),true⟩⟩⟩
  | 2 => ⟨⟨9212101786035014,10528045669135493,true⟩,⟨549133054212335263357,580168536269218714054,true⟩,⟨⟨649002411430236471905783,747907423764584842043810,true⟩,⟨937290806662913965804915,1036195818997262335946912,true⟩⟩⟩
  | 3 => ⟨⟨(-32459026818),36784423679,true⟩,⟨9212101786035014,10528045669135493,true⟩,⟨⟨(-987263363645958951040113),(-848796346377898720658424),true⟩,⟨(-855822869506448626899095),(-717355852238388396519212),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738364),34359738376,true⟩,⟨(-32459026818),36784423679,true⟩,⟨⟨993141241192041354456834,1171170263393813445039619,true⟩,⟨449910868808272874821113,627939891010044965396428,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738364),34359738376,true⟩,⟨⟨(-1289714912217018057252418),(-1072123885081534106403337),true⟩,⟨(-367505797910547092299622),(-149914770775063141463234),true⟩⟩⟩
theorem shortNegativeR058Q00F_ok : ∀ n : Fin 6, (shortNegativeR058Q00F n).encloses (FactoredFrequency.build shortNegativeR058Q00T (Grid.ofRats (503776583148099/549755813888000) (1528509618628297/1649267441664000)) n) := by decide +kernel
def shortNegativeR058Q00L : ℕ → ℚ
  | 0 => (-120357/40000)
  | 1 => (-1428299/500000)
  | 2 => (-2630333/1000000)
  | 3 => (-300489/125000)
  | 4 => (-447907/200000)
  | 5 => (-553937/250000)
  | 6 => (-7208/3125)
  | 7 => (-2494053/1000000)
  | 8 => (-2736073/1000000)
  | 9 => (-3011321/1000000)
  | 10 => (-638643/200000)
  | 11 => (-401897/125000)
  | _ => 0
def shortNegativeR058Q00U : ℕ → ℚ
  | 0 => (-60613/25000)
  | 1 => (-2186639/1000000)
  | 2 => (-29472/15625)
  | 3 => (-400849/250000)
  | 4 => (-1403567/1000000)
  | 5 => (-25839/20000)
  | 6 => (-1316981/1000000)
  | 7 => (-294603/200000)
  | 8 => (-1728093/1000000)
  | 9 => (-1991403/1000000)
  | 10 => (-445891/200000)
  | 11 => (-1186799/500000)
  | _ => 0
private theorem shortNegativeR058Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR058Q00L (0:Fin 12)) (shortNegativeR058Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR058Q00L (1:Fin 12)) (shortNegativeR058Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR058Q00L (2:Fin 12)) (shortNegativeR058Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR058Q00L (3:Fin 12)) (shortNegativeR058Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR058Q00L (4:Fin 12)) (shortNegativeR058Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR058Q00L (5:Fin 12)) (shortNegativeR058Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR058Q00L (6:Fin 12)) (shortNegativeR058Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR058Q00L (7:Fin 12)) (shortNegativeR058Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR058Q00L (8:Fin 12)) (shortNegativeR058Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR058Q00L (9:Fin 12)) (shortNegativeR058Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR058Q00L (10:Fin 12)) (shortNegativeR058Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR058Q00L (11:Fin 12)) (shortNegativeR058Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR058Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR058Q00P shortNegativeR058Q00F (shortNegativeNodes12 k)).re (shortNegativeR058Q00L k) (shortNegativeR058Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR058Q00Point00
  · exact shortNegativeR058Q00Point01
  · exact shortNegativeR058Q00Point02
  · exact shortNegativeR058Q00Point03
  · exact shortNegativeR058Q00Point04
  · exact shortNegativeR058Q00Point05
  · exact shortNegativeR058Q00Point06
  · exact shortNegativeR058Q00Point07
  · exact shortNegativeR058Q00Point08
  · exact shortNegativeR058Q00Point09
  · exact shortNegativeR058Q00Point10
  · exact shortNegativeR058Q00Point11

theorem shortNegativeR058Q00Bound {t a : ℝ} (tl : ((139/100):ℝ)≤t) (tu : t≤((7/5):ℝ)) (al : ((503776583148099/549755813888000):ℝ)≤a) (au : a≤((1528509618628297/1649267441664000):ℝ)) : (((-3531374702686578796217124643266155/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2249509106577693147086060753903211/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR058Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (503776583148099/549755813888000) (1528509618628297/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR058Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR058Q00F_ok n) ts asb
  exact factored_negative_12_samples 80 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip056Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR058Q00L shortNegativeR058Q00U (-3531374702686578796217124643266155/1298074214633706907132624082305024) (-2249509106577693147086060753903211/1298074214633706907132624082305024) shortNegativeR058Q00Samples (by decide +kernel)

def shortNegativeR058Q01T := Grid.ofRats (139/100) (7/5)
def shortNegativeR058Q01P : PrimalThetaParameters := ⟨⟨⟨14868691741727495394482,15343220318930398927008,true⟩,⟨0,0,true⟩⟩, ⟨⟨1759934968821399938426333,1779715971288324588016990,true⟩,⟨0,0,true⟩⟩, ⟨(-278082535993504344194648),(-238520531059723764500516),true⟩, ⟨3264421650772797962669707,3390335517947655143227603,true⟩⟩
theorem shortNegativeR058Q01P_ok : shortNegativeR058Q01P.encloses (primalThetaParameters shortNegativeR058Q01T (Grid.ofRats (1528509618628297/1649267441664000) (1545689487812297/1649267441664000))) := by decide +kernel

def shortNegativeR058Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨402594585049692254360065,405769005127340645772757,true⟩,⟨3601806985904101536045025,3630206892003773110943041,true⟩,⟨⟨119014742305120062224244,138795744772044711863655,true⟩,⟨1192143223550980518867952,1211924226017905168522145,true⟩⟩⟩
  | 1 => ⟨⟨549133054212335263357,580168536269218714054,true⟩,⟨402594585049692254360065,405769005127340645772757,true⟩,⟨⟨(-410524874966189590024881),(-351181867565553080125456),true⟩,⟨(-1177039076418984245013993),(-1117696069018347735104016),true⟩⟩⟩
  | 2 => ⟨⟨9212101786035014,10528045669135493,true⟩,⟨549133054212335263357,580168536269218714054,true⟩,⟨⟨566028523458857948286196,664933535793206318425868,true⟩,⟨991068872518233832125059,1089973884852582202270583,true⟩⟩⟩
  | 3 => ⟨⟨(-32459026818),36784423679,true⟩,⟨9212101786035014,10528045669135493,true⟩,⟨⟨(-891351318439853177868080),(-752884301171792947485887),true⟩,⟨(-955587808071325931762999),(-817120790803265701379920),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738364),34359738376,true⟩,⟨(-32459026818),36784423679,true⟩,⟨⟨902351762500436935204909,1080380784702209025793490,true⟩,⟨602863042297639628217553,780892064499411718802022,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738364),34359738376,true⟩,⟨⟨(-1224324844167604209596391),(-1006733817032120258739165),true⟩,⟨(-574731077677551246697838),(-357140050542067295849551),true⟩⟩⟩
theorem shortNegativeR058Q01F_ok : ∀ n : Fin 6, (shortNegativeR058Q01F n).encloses (FactoredFrequency.build shortNegativeR058Q01T (Grid.ofRats (1528509618628297/1649267441664000) (1545689487812297/1649267441664000)) n) := by decide +kernel
def shortNegativeR058Q01L : ℕ → ℚ
  | 0 => (-3006459/1000000)
  | 1 => (-1434241/500000)
  | 2 => (-1324513/500000)
  | 3 => (-75639/31250)
  | 4 => (-280803/125000)
  | 5 => (-2206967/1000000)
  | 6 => (-2280419/1000000)
  | 7 => (-2452289/1000000)
  | 8 => (-671059/250000)
  | 9 => (-739247/250000)
  | 10 => (-393499/125000)
  | 11 => (-3188773/1000000)
  | _ => 0
def shortNegativeR058Q01U : ℕ → ℚ
  | 0 => (-487231/200000)
  | 1 => (-553743/250000)
  | 2 => (-15383/8000)
  | 3 => (-409739/250000)
  | 4 => (-178799/125000)
  | 5 => (-653191/500000)
  | 6 => (-329351/250000)
  | 7 => (-1460543/1000000)
  | 8 => (-213327/125000)
  | 9 => (-393723/200000)
  | 10 => (-22131/10000)
  | 11 => (-474093/200000)
  | _ => 0
private theorem shortNegativeR058Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR058Q01L (0:Fin 12)) (shortNegativeR058Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR058Q01L (1:Fin 12)) (shortNegativeR058Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR058Q01L (2:Fin 12)) (shortNegativeR058Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR058Q01L (3:Fin 12)) (shortNegativeR058Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR058Q01L (4:Fin 12)) (shortNegativeR058Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR058Q01L (5:Fin 12)) (shortNegativeR058Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR058Q01L (6:Fin 12)) (shortNegativeR058Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR058Q01L (7:Fin 12)) (shortNegativeR058Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR058Q01L (8:Fin 12)) (shortNegativeR058Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR058Q01L (9:Fin 12)) (shortNegativeR058Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR058Q01L (10:Fin 12)) (shortNegativeR058Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR058Q01L (11:Fin 12)) (shortNegativeR058Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR058Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR058Q01P shortNegativeR058Q01F (shortNegativeNodes12 k)).re (shortNegativeR058Q01L k) (shortNegativeR058Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR058Q01Point00
  · exact shortNegativeR058Q01Point01
  · exact shortNegativeR058Q01Point02
  · exact shortNegativeR058Q01Point03
  · exact shortNegativeR058Q01Point04
  · exact shortNegativeR058Q01Point05
  · exact shortNegativeR058Q01Point06
  · exact shortNegativeR058Q01Point07
  · exact shortNegativeR058Q01Point08
  · exact shortNegativeR058Q01Point09
  · exact shortNegativeR058Q01Point10
  · exact shortNegativeR058Q01Point11

theorem shortNegativeR058Q01Bound {t a : ℝ} (tl : ((139/100):ℝ)≤t) (tu : t≤((7/5):ℝ)) (al : ((1528509618628297/1649267441664000):ℝ)≤a) (au : a≤((1545689487812297/1649267441664000):ℝ)) : (((-3531374702686578796217124643266155/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2249509106577693147086060753903211/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR058Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1528509618628297/1649267441664000) (1545689487812297/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR058Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR058Q01F_ok n) ts asb
  exact factored_negative_12_samples 80 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip056Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR058Q01L shortNegativeR058Q01U (-3531374702686578796217124643266155/1298074214633706907132624082305024) (-2249509106577693147086060753903211/1298074214633706907132624082305024) shortNegativeR058Q01Samples (by decide +kernel)

def shortNegativeR058Q02T := Grid.ofRats (139/100) (7/5)
def shortNegativeR058Q02P : PrimalThetaParameters := ⟨⟨⟨14868691741727495394482,15343220318930398927008,true⟩,⟨0,0,true⟩⟩, ⟨⟨1779715971288255868534586,1799496973755180518125308,true⟩,⟨0,0,true⟩⟩, ⟨(-238520531059792483978016),(-198958526126011904284007),true⟩, ⟨3255046743923055040110204,3380336232905667534526397,true⟩⟩
theorem shortNegativeR058Q02P_ok : shortNegativeR058Q02P.encloses (primalThetaParameters shortNegativeR058Q02T (Grid.ofRats (1545689487812297/1649267441664000) (520956452332099/549755813888000))) := by decide +kernel

def shortNegativeR058Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨402594585049692254360065,405769005127340645772757,true⟩,⟨3601806985904101536045025,3630206892003773110943041,true⟩,⟨⟨99330133568842213643528,119111136035766863282850,true⟩,⟨1194091429803828841071251,1213872432270753490725643,true⟩⟩⟩
  | 1 => ⟨⟨549133054212335263357,580168536269218714054,true⟩,⟨402594585049692254360065,405769005127340645772757,true⟩,⟨⟨(-353767462009092500964237),(-294424454608455991064951),true⟩,⟨(-1194344611116652558964197),(-1135001603716016049053341),true⟩⟩⟩
  | 2 => ⟨⟨9212101786035014,10528045669135493,true⟩,⟨549133054212335263357,580168536269218714054,true⟩,⟨⟨478937361979802680396437,577842374314151050537138,true⟩,⟨1037886348362784806355921,1136791360697133176504317,true⟩⟩⟩
  | 3 => ⟨⟨(-32459026818),36784423679,true⟩,⟨9212101786035014,10528045669135493,true⟩,⟨⟨(-784665878109951132814339),(-646198860841890902432216),true⟩,⟨(-1043737568162245808089061),(-905270550894185577703369),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738364),34359738376,true⟩,⟨(-32459026818),36784423679,true⟩,⟨⟨790102197841680239203215,968131220043452329796433,true⟩,⟨740838156177405056488626,918867178379177147081172,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738364),34359738376,true⟩,⟨⟨(-1122894267728827417640020),(-905303240593343466777544),true⟩,⟨(-766902916762568001933060),(-549311889627084051075482),true⟩⟩⟩
theorem shortNegativeR058Q02F_ok : ∀ n : Fin 6, (shortNegativeR058Q02F n).encloses (FactoredFrequency.build shortNegativeR058Q02T (Grid.ofRats (1545689487812297/1649267441664000) (520956452332099/549755813888000)) n) := by decide +kernel
def shortNegativeR058Q02L : ℕ → ℚ
  | 0 => (-75089/25000)
  | 1 => (-57603/20000)
  | 2 => (-1333991/500000)
  | 3 => (-2437751/1000000)
  | 4 => (-450893/200000)
  | 5 => (-43991/20000)
  | 6 => (-2255699/1000000)
  | 7 => (-1205921/500000)
  | 8 => (-2633397/1000000)
  | 9 => (-1451539/500000)
  | 10 => (-1551259/500000)
  | 11 => (-1581051/500000)
  | _ => 0
def shortNegativeR058Q02U : ℕ → ℚ
  | 0 => (-1223439/500000)
  | 1 => (-2242807/1000000)
  | 2 => (-30621/15625)
  | 3 => (-167543/100000)
  | 4 => (-729337/500000)
  | 5 => (-661309/500000)
  | 6 => (-164971/125000)
  | 7 => (-362481/250000)
  | 8 => (-421661/250000)
  | 9 => (-121673/62500)
  | 10 => (-2196989/1000000)
  | 11 => (-2366587/1000000)
  | _ => 0
private theorem shortNegativeR058Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR058Q02L (0:Fin 12)) (shortNegativeR058Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR058Q02L (1:Fin 12)) (shortNegativeR058Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR058Q02L (2:Fin 12)) (shortNegativeR058Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR058Q02L (3:Fin 12)) (shortNegativeR058Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR058Q02L (4:Fin 12)) (shortNegativeR058Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR058Q02L (5:Fin 12)) (shortNegativeR058Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR058Q02L (6:Fin 12)) (shortNegativeR058Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR058Q02L (7:Fin 12)) (shortNegativeR058Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR058Q02L (8:Fin 12)) (shortNegativeR058Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR058Q02L (9:Fin 12)) (shortNegativeR058Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR058Q02L (10:Fin 12)) (shortNegativeR058Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR058Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR058Q02L (11:Fin 12)) (shortNegativeR058Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR058Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR058Q02P shortNegativeR058Q02F (shortNegativeNodes12 k)).re (shortNegativeR058Q02L k) (shortNegativeR058Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR058Q02Point00
  · exact shortNegativeR058Q02Point01
  · exact shortNegativeR058Q02Point02
  · exact shortNegativeR058Q02Point03
  · exact shortNegativeR058Q02Point04
  · exact shortNegativeR058Q02Point05
  · exact shortNegativeR058Q02Point06
  · exact shortNegativeR058Q02Point07
  · exact shortNegativeR058Q02Point08
  · exact shortNegativeR058Q02Point09
  · exact shortNegativeR058Q02Point10
  · exact shortNegativeR058Q02Point11

theorem shortNegativeR058Q02Bound {t a : ℝ} (tl : ((139/100):ℝ)≤t) (tu : t≤((7/5):ℝ)) (al : ((1545689487812297/1649267441664000):ℝ)≤a) (au : a≤((520956452332099/549755813888000):ℝ)) : (((-3531374702686578796217124643266155/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2249509106577693147086060753903211/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR058Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1545689487812297/1649267441664000) (520956452332099/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR058Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR058Q02F_ok n) ts asb
  exact factored_negative_12_samples 80 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip056Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR058Q02L shortNegativeR058Q02U (-3531374702686578796217124643266155/1298074214633706907132624082305024) (-2249509106577693147086060753903211/1298074214633706907132624082305024) shortNegativeR058Q02Samples (by decide +kernel)

theorem short_original_negative_058 {t a : ℝ} (tb : RealMem negative_058.t t) (ab : RealMem negative_058.a a) : RealMem negative_058.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((139/100):ℝ) ((7/5):ℝ) := by simpa [negative_058,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((139/100):ℝ)<((7/5):ℝ)) tB
  have aB : a∈Icc ((503776583148099/549755813888000):ℝ) ((520956452332099/549755813888000):ℝ) := by simpa [negative_058,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((503776583148099/549755813888000):ℝ)<((520956452332099/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR058Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_058,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR058Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_058,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR058Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_058,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_058
