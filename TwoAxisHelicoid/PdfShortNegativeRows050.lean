import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip048

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR050Q00T := Grid.ofRats (131/100) (33/25)
def shortNegativeR050Q00P : PrimalThetaParameters := ⟨⟨⟨19117137597654037731983,19727253690023595549316,true⟩,⟨0,0,true⟩⟩, ⟨⟨1554374668338376112706827,1564265169571872797242672,true⟩,⟨0,0,true⟩⟩, ⟨(-689203136959551995634968),(-669422134492627346047781),true⟩, ⟨3590820688559539950557739,3670886053254460220128059,true⟩⟩
theorem shortNegativeR050Q00P_ok : shortNegativeR050Q00P.encloses (primalThetaParameters shortNegativeR050Q00T (Grid.ofRats (1349979785388587/1649267441664000) (1358569719980587/1649267441664000))) := by decide +kernel

def shortNegativeR050Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨428701947430771083668345,432082221581953296804157,true⟩,⟨3382461865660909612950179,3409132256313836883455684,true⟩,⟨⟨330260101202188711201173,340150602435685395786259,true⟩,⟨1156579182808070126598239,1166469684041566811194740,true⟩⟩⟩
  | 1 => ⟨⟨852491928493534606494,900672415401053536539,true⟩,⟨428701947430771083668345,432082221581953296804157,true⟩,⟨⟨(-917367272194725163044746),(-887695768494372548310279),true⟩,⟨(-819160619124252394182915),(-789489115423899779449799),true⟩⟩⟩
  | 2 => ⟨⟨26806971425340449,30636192533092250,true⟩,⟨852491928493534606494,900672415401053536539,true⟩,⟨⟨1167579058731623269681224,1217031564898831814524295,true⟩,⟨175047821180540273751577,224500327347748818580985,true⟩⟩⟩
  | 3 => ⟨⟨(-21029756665),51364428435,true⟩,⟨26806971425340449,30636192533092250,true⟩,⟨⟨(-1150030355058267831694870),(-1080796846424203356700347),true⟩,⟨431595790143511415638823,500829298777575890624406,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738264),34359738523,true⟩,⟨(-21029756665),51364428435,true⟩,⟨⟨650995371845538721737321,740009882946459126837137,true⟩,⟨(-1033333697660583593029798),(-944319186559663187925946),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738264),34359738523,true⟩,⟨⟨(-116103908633002170378018),(-7308395065225835142748),true⟩,⟨1152952228992761851192268,1261747742560538186443308,true⟩⟩⟩
theorem shortNegativeR050Q00F_ok : ∀ n : Fin 6, (shortNegativeR050Q00F n).encloses (FactoredFrequency.build shortNegativeR050Q00T (Grid.ofRats (1349979785388587/1649267441664000) (1358569719980587/1649267441664000)) n) := by decide +kernel
def shortNegativeR050Q00L : ℕ → ℚ
  | 0 => (-578373/200000)
  | 1 => (-624887/250000)
  | 2 => (-1067317/500000)
  | 3 => (-472881/250000)
  | 4 => (-227011/125000)
  | 5 => (-48899/25000)
  | 6 => (-225559/100000)
  | 7 => (-665291/250000)
  | 8 => (-1539643/500000)
  | 9 => (-53548/15625)
  | 10 => (-3534837/1000000)
  | 11 => (-3351869/1000000)
  | _ => 0
def shortNegativeR050Q00U : ℕ → ℚ
  | 0 => (-1166953/500000)
  | 1 => (-937987/500000)
  | 2 => (-1461987/1000000)
  | 3 => (-296291/250000)
  | 4 => (-544281/500000)
  | 5 => (-1141987/1000000)
  | 6 => (-685789/500000)
  | 7 => (-172553/100000)
  | 8 => (-2133229/1000000)
  | 9 => (-2453653/1000000)
  | 10 => (-10463/4000)
  | 11 => (-639021/250000)
  | _ => 0
private theorem shortNegativeR050Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR050Q00L (0:Fin 12)) (shortNegativeR050Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR050Q00L (1:Fin 12)) (shortNegativeR050Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR050Q00L (2:Fin 12)) (shortNegativeR050Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR050Q00L (3:Fin 12)) (shortNegativeR050Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR050Q00L (4:Fin 12)) (shortNegativeR050Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR050Q00L (5:Fin 12)) (shortNegativeR050Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR050Q00L (6:Fin 12)) (shortNegativeR050Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR050Q00L (7:Fin 12)) (shortNegativeR050Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR050Q00L (8:Fin 12)) (shortNegativeR050Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR050Q00L (9:Fin 12)) (shortNegativeR050Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR050Q00L (10:Fin 12)) (shortNegativeR050Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR050Q00L (11:Fin 12)) (shortNegativeR050Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR050Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR050Q00P shortNegativeR050Q00F (shortNegativeNodes12 k)).re (shortNegativeR050Q00L k) (shortNegativeR050Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR050Q00Point00
  · exact shortNegativeR050Q00Point01
  · exact shortNegativeR050Q00Point02
  · exact shortNegativeR050Q00Point03
  · exact shortNegativeR050Q00Point04
  · exact shortNegativeR050Q00Point05
  · exact shortNegativeR050Q00Point06
  · exact shortNegativeR050Q00Point07
  · exact shortNegativeR050Q00Point08
  · exact shortNegativeR050Q00Point09
  · exact shortNegativeR050Q00Point10
  · exact shortNegativeR050Q00Point11

theorem shortNegativeR050Q00Bound {t a : ℝ} (tl : ((131/100):ℝ)≤t) (tu : t≤((33/25):ℝ)) (al : ((1349979785388587/1649267441664000):ℝ)≤a) (au : a≤((1358569719980587/1649267441664000):ℝ)) : (((-3467007907188669676389934626107739/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2249507730423539320447729735168347/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR050Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1349979785388587/1649267441664000) (1358569719980587/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR050Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR050Q00F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR050Q00L shortNegativeR050Q00U (-3467007907188669676389934626107739/1298074214633706907132624082305024) (-2249507730423539320447729735168347/1298074214633706907132624082305024) shortNegativeR050Q00Samples (by decide +kernel)

def shortNegativeR050Q01T := Grid.ofRats (131/100) (33/25)
def shortNegativeR050Q01P : PrimalThetaParameters := ⟨⟨⟨19117137597654037731983,19727253690023595549316,true⟩,⟨0,0,true⟩⟩, ⟨⟨1564265169571804077760954,1574155670805300762296832,true⟩,⟨0,0,true⟩⟩, ⟨(-669422134492696065526652),(-649641132025771415939524),true⟩, ⟨3576215360451860417487893,3655848839828993279986020,true⟩⟩
theorem shortNegativeR050Q01P_ok : shortNegativeR050Q01P.encloses (primalThetaParameters shortNegativeR050Q01T (Grid.ofRats (1358569719980587/1649267441664000) (455719884857529/549755813888000))) := by decide +kernel

def shortNegativeR050Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨428701947430771083668345,432082221581953296804157,true⟩,⟨3382461865660909612950179,3409132256313836883455684,true⟩,⟨⟨320746289648964728617990,330636790882461413202682,true⟩,⟨1159282672914658079881099,1169173174148154764477335,true⟩⟩⟩
  | 1 => ⟨⟨852491928493534606494,900672415401053536539,true⟩,⟨428701947430771083668345,432082221581953296804157,true⟩,⟨⟨(-897356326200276807979589),(-867684822499924193245144),true⟩,⟨(-841067603801958454687708),(-811396100101605839954028),true⟩⟩⟩
  | 2 => ⟨⟨26806971425340449,30636192533092250,true⟩,⟨852491928493534606494,900672415401053536539,true⟩,⟨⟨1158411937303341001048093,1207864443470549545892893,true⟩,⟨223639726428098088853365,273092232595306633685302,true⟩⟩⟩
  | 3 => ⟨⟨(-21029756665),51364428435,true⟩,⟨26806971425340449,30636192533092250,true⟩,⟨⟨(-1174886502380682445087701),(-1105652993746617970094466),true⟩,⟨366988199563970831318426,436221708198035306301487,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738264),34359738523,true⟩,⟨(-21029756665),51364428435,true⟩,⟨⟨721853463036167515692793,810867974137087920792227,true⟩,⟨(-979490082311620835131089),(-890475571210700430029336),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738264),34359738523,true⟩,⟨⟨(-224361299835699103237486),(-115565786267922767998798),true⟩,⟨1142520799912505494245042,1251316313480281829497863,true⟩⟩⟩
theorem shortNegativeR050Q01F_ok : ∀ n : Fin 6, (shortNegativeR050Q01F n).encloses (FactoredFrequency.build shortNegativeR050Q01T (Grid.ofRats (1358569719980587/1649267441664000) (455719884857529/549755813888000)) n) := by decide +kernel
def shortNegativeR050Q01L : ℕ → ℚ
  | 0 => (-181201/62500)
  | 1 => (-125711/50000)
  | 2 => (-2150023/1000000)
  | 3 => (-951007/500000)
  | 4 => (-181801/100000)
  | 5 => (-973549/500000)
  | 6 => (-1117883/500000)
  | 7 => (-329037/125000)
  | 8 => (-3046049/1000000)
  | 9 => (-339621/100000)
  | 10 => (-439213/125000)
  | 11 => (-3345357/1000000)
  | _ => 0
def shortNegativeR050Q01U : ℕ → ℚ
  | 0 => (-2348193/1000000)
  | 1 => (-237187/125000)
  | 2 => (-1483759/1000000)
  | 3 => (-1201559/1000000)
  | 4 => (-1096191/1000000)
  | 5 => (-285431/250000)
  | 6 => (-271923/200000)
  | 7 => (-426489/250000)
  | 8 => (-2110209/1000000)
  | 9 => (-2433541/1000000)
  | 10 => (-2605081/1000000)
  | 11 => (-2558407/1000000)
  | _ => 0
private theorem shortNegativeR050Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR050Q01L (0:Fin 12)) (shortNegativeR050Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR050Q01L (1:Fin 12)) (shortNegativeR050Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR050Q01L (2:Fin 12)) (shortNegativeR050Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR050Q01L (3:Fin 12)) (shortNegativeR050Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR050Q01L (4:Fin 12)) (shortNegativeR050Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR050Q01L (5:Fin 12)) (shortNegativeR050Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR050Q01L (6:Fin 12)) (shortNegativeR050Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR050Q01L (7:Fin 12)) (shortNegativeR050Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR050Q01L (8:Fin 12)) (shortNegativeR050Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR050Q01L (9:Fin 12)) (shortNegativeR050Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR050Q01L (10:Fin 12)) (shortNegativeR050Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR050Q01L (11:Fin 12)) (shortNegativeR050Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR050Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR050Q01P shortNegativeR050Q01F (shortNegativeNodes12 k)).re (shortNegativeR050Q01L k) (shortNegativeR050Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR050Q01Point00
  · exact shortNegativeR050Q01Point01
  · exact shortNegativeR050Q01Point02
  · exact shortNegativeR050Q01Point03
  · exact shortNegativeR050Q01Point04
  · exact shortNegativeR050Q01Point05
  · exact shortNegativeR050Q01Point06
  · exact shortNegativeR050Q01Point07
  · exact shortNegativeR050Q01Point08
  · exact shortNegativeR050Q01Point09
  · exact shortNegativeR050Q01Point10
  · exact shortNegativeR050Q01Point11

theorem shortNegativeR050Q01Bound {t a : ℝ} (tl : ((131/100):ℝ)≤t) (tu : t≤((33/25):ℝ)) (al : ((1358569719980587/1649267441664000):ℝ)≤a) (au : a≤((455719884857529/549755813888000):ℝ)) : (((-3467007907188669676389934626107739/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2249507730423539320447729735168347/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR050Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1358569719980587/1649267441664000) (455719884857529/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR050Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR050Q01F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR050Q01L shortNegativeR050Q01U (-3467007907188669676389934626107739/1298074214633706907132624082305024) (-2249507730423539320447729735168347/1298074214633706907132624082305024) shortNegativeR050Q01Samples (by decide +kernel)

def shortNegativeR050Q02T := Grid.ofRats (131/100) (33/25)
def shortNegativeR050Q02P : PrimalThetaParameters := ⟨⟨⟨19117137597654037731983,19727253690023595549316,true⟩,⟨0,0,true⟩⟩, ⟨⟨1574155670805232042815082,1584046172038728727350990,true⟩,⟨0,0,true⟩⟩, ⟨(-649641132025840135418333),(-629860129558915485831271),true⟩, ⟨3562129935976352249121256,3641346375043974162811287,true⟩⟩
theorem shortNegativeR050Q02P_ok : shortNegativeR050Q02P.encloses (primalThetaParameters shortNegativeR050Q02T (Grid.ofRats (455719884857529/549755813888000) (1375749589164587/1649267441664000))) := by decide +kernel

def shortNegativeR050Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨428701947430771083668345,432082221581953296804157,true⟩,⟨3382461865660909612950179,3409132256313836883455684,true⟩,⟨⟨311210678855764157648549,321101180089260842233265,true⟩,⟨1161908238725540345453852,1171798739959037030050282,true⟩⟩⟩
  | 1 => ⟨⟨852491928493534606494,900672415401053536539,true⟩,⟨428701947430771083668345,432082221581953296804157,true⟩,⟨⟨(-876813782811409725379887),(-847142279111057110645009),true⟩,⟨(-862476897306847636137337),(-832805393606495021402652),true⟩⟩⟩
  | 2 => ⟨⟨26806971425340449,30636192533092250,true⟩,⟨852491928493534606494,900672415401053536539,true⟩,⟨⟨1147265330860283103453546,1196717837027491648300198,true⟩,⟨271816095486715290057325,321268601653923834891928,true⟩⟩⟩
  | 3 => ⟨⟨(-21029756665),51364428435,true⟩,⟨26806971425340449,30636192533092250,true⟩,⟨⟨(-1196003935397360506756711),(-1126770426763296031763859),true⟩,⟨301063827416841240995424,370297336050905715976911,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738264),34359738523,true⟩,⟨(-21029756665),51364428435,true⟩,⟨⟨788558579093275181892097,877573090194195586989717,true⟩,⟨(-920579714015077986336159),(-831565202914157581237951),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738264),34359738523,true⟩,⟨⟨(-331243112737891720029867),(-222447599170115384787995),true⟩,⟨1122402262853095008107012,1231197776420871343361271,true⟩⟩⟩
theorem shortNegativeR050Q02F_ok : ∀ n : Fin 6, (shortNegativeR050Q02F n).encloses (FactoredFrequency.build shortNegativeR050Q02T (Grid.ofRats (455719884857529/549755813888000) (1375749589164587/1649267441664000)) n) := by decide +kernel
def shortNegativeR050Q02L : ℕ → ℚ
  | 0 => (-1453157/500000)
  | 1 => (-252877/100000)
  | 2 => (-86619/40000)
  | 3 => (-478183/250000)
  | 4 => (-1820283/1000000)
  | 5 => (-1938663/1000000)
  | 6 => (-1108203/500000)
  | 7 => (-130193/50000)
  | 8 => (-3013113/1000000)
  | 9 => (-673081/200000)
  | 10 => (-349239/100000)
  | 11 => (-3338517/1000000)
  | _ => 0
def shortNegativeR050Q02U : ℕ → ℚ
  | 0 => (-2362167/1000000)
  | 1 => (-1918899/1000000)
  | 2 => (-94103/62500)
  | 3 => (-304567/250000)
  | 4 => (-1104269/1000000)
  | 5 => (-1141729/1000000)
  | 6 => (-337057/250000)
  | 7 => (-1686921/1000000)
  | 8 => (-417519/200000)
  | 9 => (-150851/62500)
  | 10 => (-1297177/500000)
  | 11 => (-2560469/1000000)
  | _ => 0
private theorem shortNegativeR050Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR050Q02L (0:Fin 12)) (shortNegativeR050Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR050Q02L (1:Fin 12)) (shortNegativeR050Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR050Q02L (2:Fin 12)) (shortNegativeR050Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR050Q02L (3:Fin 12)) (shortNegativeR050Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR050Q02L (4:Fin 12)) (shortNegativeR050Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR050Q02L (5:Fin 12)) (shortNegativeR050Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR050Q02L (6:Fin 12)) (shortNegativeR050Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR050Q02L (7:Fin 12)) (shortNegativeR050Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR050Q02L (8:Fin 12)) (shortNegativeR050Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR050Q02L (9:Fin 12)) (shortNegativeR050Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR050Q02L (10:Fin 12)) (shortNegativeR050Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR050Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR050Q02L (11:Fin 12)) (shortNegativeR050Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR050Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR050Q02P shortNegativeR050Q02F (shortNegativeNodes12 k)).re (shortNegativeR050Q02L k) (shortNegativeR050Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR050Q02Point00
  · exact shortNegativeR050Q02Point01
  · exact shortNegativeR050Q02Point02
  · exact shortNegativeR050Q02Point03
  · exact shortNegativeR050Q02Point04
  · exact shortNegativeR050Q02Point05
  · exact shortNegativeR050Q02Point06
  · exact shortNegativeR050Q02Point07
  · exact shortNegativeR050Q02Point08
  · exact shortNegativeR050Q02Point09
  · exact shortNegativeR050Q02Point10
  · exact shortNegativeR050Q02Point11

theorem shortNegativeR050Q02Bound {t a : ℝ} (tl : ((131/100):ℝ)≤t) (tu : t≤((33/25):ℝ)) (al : ((455719884857529/549755813888000):ℝ)≤a) (au : a≤((1375749589164587/1649267441664000):ℝ)) : (((-3467007907188669676389934626107739/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2249507730423539320447729735168347/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR050Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (455719884857529/549755813888000) (1375749589164587/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR050Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR050Q02F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR050Q02L shortNegativeR050Q02U (-3467007907188669676389934626107739/1298074214633706907132624082305024) (-2249507730423539320447729735168347/1298074214633706907132624082305024) shortNegativeR050Q02Samples (by decide +kernel)

theorem short_original_negative_050 {t a : ℝ} (tb : RealMem negative_050.t t) (ab : RealMem negative_050.a a) : RealMem negative_050.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((131/100):ℝ) ((33/25):ℝ) := by simpa [negative_050,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((131/100):ℝ)<((33/25):ℝ)) tB
  have aB : a∈Icc ((1349979785388587/1649267441664000):ℝ) ((1375749589164587/1649267441664000):ℝ) := by simpa [negative_050,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1349979785388587/1649267441664000):ℝ)<((1375749589164587/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR050Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_050,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR050Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_050,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR050Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_050,RealMem] using v

def shortNegativeR051Q00T := Grid.ofRats (33/25) (133/100)
def shortNegativeR051Q00P : PrimalThetaParameters := ⟨⟨⟨18525890915760454523603,19117137597722757209060,true⟩,⟨0,0,true⟩⟩, ⟨⟨1572318154269642440326439,1582208655503139124862341,true⟩,⟨0,0,true⟩⟩, ⟨(-653316165097019340395630),(-633535162630094690808557),true⟩, ⟨3552274669328123931501086,3630735640256650846455470,true⟩⟩
theorem shortNegativeR051Q00P_ok : shortNegativeR051Q00P.encloses (primalThetaParameters shortNegativeR051Q00T (Grid.ofRats (455187921698133/549755813888000) (1374153699686399/1649267441664000))) := by decide +kernel

def shortNegativeR051Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨425348117907013126185573,428701947430839803161045,true⟩,⟨3409132256313768163852380,3436012940464693849354528,true⟩,⟨⟨312983881328121134669180,322874382561617819253774,true⟩,⟨1161426347284917254013698,1171316848518413938609990,true⟩⟩⟩
  | 1 => ⟨⟨806888804159035481438,852491928562254083279,true⟩,⟨425348117907013126185573,428701947430839803161045,true⟩,⟨⟨(-880669945070607079704257),(-850998441370254464969117),true⟩,⟨(-858537587323602706976034),(-828866083623250092241192),true⟩⟩⟩
  | 2 => ⟨⟨23456417167081094,26807040144817186,true⟩,⟨806888804159035481438,852491928562254083279,true⟩,⟨⟨1149485123734903075493857,1198937629902111620339230,true⟩,⟨262900727363099063287312,312353233530307608120485,true⟩⟩⟩
  | 3 => ⟨⟨(-23910361666),47689720072,true⟩,⟨23456417167081094,26807040144817186,true⟩,⟨⟨(-1192366724116197655385183),(-1123133215482133180393287),true⟩,⟨313401412968720936868720,382634921602785411849470,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738297),34359738473,true⟩,⟨(-23910361666),47689720072,true⟩,⟨⟨776496666915365507947119,865511178016285913045096,true⟩,⟨(-931893415362878825001547),(-842878904261958419902657),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738297),34359738473,true⟩,⟨⟨(-311529781894574531179931),(-202734268326798195938863),true⟩,⟨1126866294558308682343671,1235661808126085017597459,true⟩⟩⟩
theorem shortNegativeR051Q00F_ok : ∀ n : Fin 6, (shortNegativeR051Q00F n).encloses (FactoredFrequency.build shortNegativeR051Q00T (Grid.ofRats (455187921698133/549755813888000) (1374153699686399/1649267441664000)) n) := by decide +kernel
def shortNegativeR051Q00L : ℕ → ℚ
  | 0 => (-2905201/1000000)
  | 1 => (-317467/125000)
  | 2 => (-1094001/500000)
  | 3 => (-971797/500000)
  | 4 => (-927679/500000)
  | 5 => (-1973167/1000000)
  | 6 => (-1122921/500000)
  | 7 => (-2623841/1000000)
  | 8 => (-1510297/500000)
  | 9 => (-3359987/1000000)
  | 10 => (-695879/200000)
  | 11 => (-1663513/500000)
  | _ => 0
def shortNegativeR051Q00U : ℕ → ℚ
  | 0 => (-2362377/1000000)
  | 1 => (-482681/250000)
  | 2 => (-1528321/1000000)
  | 3 => (-1248539/1000000)
  | 4 => (-569051/500000)
  | 5 => (-1175517/1000000)
  | 6 => (-1377997/1000000)
  | 7 => (-213603/125000)
  | 8 => (-209877/100000)
  | 9 => (-2414443/1000000)
  | 10 => (-1294237/500000)
  | 11 => (-2554477/1000000)
  | _ => 0
private theorem shortNegativeR051Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR051Q00L (0:Fin 12)) (shortNegativeR051Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR051Q00L (1:Fin 12)) (shortNegativeR051Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR051Q00L (2:Fin 12)) (shortNegativeR051Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR051Q00L (3:Fin 12)) (shortNegativeR051Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR051Q00L (4:Fin 12)) (shortNegativeR051Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR051Q00L (5:Fin 12)) (shortNegativeR051Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR051Q00L (6:Fin 12)) (shortNegativeR051Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR051Q00L (7:Fin 12)) (shortNegativeR051Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR051Q00L (8:Fin 12)) (shortNegativeR051Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR051Q00L (9:Fin 12)) (shortNegativeR051Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR051Q00L (10:Fin 12)) (shortNegativeR051Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR051Q00L (11:Fin 12)) (shortNegativeR051Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR051Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR051Q00P shortNegativeR051Q00F (shortNegativeNodes12 k)).re (shortNegativeR051Q00L k) (shortNegativeR051Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR051Q00Point00
  · exact shortNegativeR051Q00Point01
  · exact shortNegativeR051Q00Point02
  · exact shortNegativeR051Q00Point03
  · exact shortNegativeR051Q00Point04
  · exact shortNegativeR051Q00Point05
  · exact shortNegativeR051Q00Point06
  · exact shortNegativeR051Q00Point07
  · exact shortNegativeR051Q00Point08
  · exact shortNegativeR051Q00Point09
  · exact shortNegativeR051Q00Point10
  · exact shortNegativeR051Q00Point11

theorem shortNegativeR051Q00Bound {t a : ℝ} (tl : ((33/25):ℝ)≤t) (tu : t≤((133/100):ℝ)) (al : ((455187921698133/549755813888000):ℝ)≤a) (au : a≤((1374153699686399/1649267441664000):ℝ)) : (((-432112157105145837704460654073495/162259276829213363391578010288128):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-284680388396734485639298903168663/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : shortNegativeR051Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (455187921698133/549755813888000) (1374153699686399/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR051Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR051Q00F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR051Q00L shortNegativeR051Q00U (-432112157105145837704460654073495/162259276829213363391578010288128) (-284680388396734485639298903168663/162259276829213363391578010288128) shortNegativeR051Q00Samples (by decide +kernel)

def shortNegativeR051Q01T := Grid.ofRats (33/25) (133/100)
def shortNegativeR051Q01P : PrimalThetaParameters := ⟨⟨⟨18525890915760454523603,19117137597722757209060,true⟩,⟨0,0,true⟩⟩, ⟨⟨1582208655503070405380565,1592099156736567089916501,true⟩,⟨0,0,true⟩⟩, ⟨(-633535162630163410287314),(-613754160163238760700301),true⟩, ⟨3538595434436374074185874,3616652353814940355411455,true⟩⟩
theorem shortNegativeR051Q01P_ok : shortNegativeR051Q01P.encloses (primalThetaParameters shortNegativeR051Q01T (Grid.ofRats (1374153699686399/1649267441664000) (1382743634278399/1649267441664000))) := by decide +kernel

def shortNegativeR051Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨425348117907013126185573,428701947430839803161045,true⟩,⟨3409132256313768163852380,3436012940464693849354528,true⟩,⟨⟨303430992613030123098341,313321493846526807683260,true⟩,⟨1163988336009280394718218,1173878837242777079314993,true⟩⟩⟩
  | 1 => ⟨⟨806888804159035481438,852491928562254083279,true⟩,⟨425348117907013126185573,428701947430839803161045,true⟩,⟨⟨(-859703692449868080745957),(-830032188749515466011083),true⟩,⟨(-879532114903553912717072),(-849860611203201297981913),true⟩⟩⟩
  | 2 => ⟨⟨23456417167081094,26807040144817186,true⟩,⟨806888804159035481438,852491928562254083279,true⟩,⟨⟨1136740416222566028797975,1186192922389774573645646,true⟩,⟨310679193237313655064497,360131699404522199900796,true⟩⟩⟩
  | 3 => ⟨⟨(-23910361666),47689720072,true⟩,⟨23456417167081094,26807040144817186,true⟩,⟨⟨(-1210388336167024263713543),(-1141154827532959788722020),true⟩,⟨246564369951419359216834,315797878585483834196038,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738297),34359738473,true⟩,⟨(-23910361666),47689720072,true⟩,⟨⟨839552296811464404339531,928566807912384809436112,true⟩,⟨(-869092208850322691875859),(-780077697749402286780099),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738297),34359738473,true⟩,⟨⟨(-416651947786085284230380),(-307856434218308948986130),true⟩,⟨1098977090536897915330351,1207772604104674250585489,true⟩⟩⟩
theorem shortNegativeR051Q01F_ok : ∀ n : Fin 6, (shortNegativeR051Q01F n).encloses (FactoredFrequency.build shortNegativeR051Q01T (Grid.ofRats (1374153699686399/1649267441664000) (1382743634278399/1649267441664000)) n) := by decide +kernel
def shortNegativeR051Q01L : ℕ → ℚ
  | 0 => (-2911347/1000000)
  | 1 => (-1276613/500000)
  | 2 => (-1101287/500000)
  | 3 => (-244219/125000)
  | 4 => (-1857419/1000000)
  | 5 => (-1964851/1000000)
  | 6 => (-222691/100000)
  | 7 => (-2596077/1000000)
  | 8 => (-747101/250000)
  | 9 => (-1664857/500000)
  | 10 => (-864529/250000)
  | 11 => (-3319609/1000000)
  | _ => 0
def shortNegativeR051Q01U : ℕ → ℚ
  | 0 => (-2375361/1000000)
  | 1 => (-390223/200000)
  | 2 => (-774729/500000)
  | 3 => (-316217/250000)
  | 4 => (-1146171/1000000)
  | 5 => (-293521/250000)
  | 6 => (-1367213/1000000)
  | 7 => (-84529/50000)
  | 8 => (-2076959/1000000)
  | 9 => (-598769/250000)
  | 10 => (-644453/250000)
  | 11 => (-2555999/1000000)
  | _ => 0
private theorem shortNegativeR051Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR051Q01L (0:Fin 12)) (shortNegativeR051Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR051Q01L (1:Fin 12)) (shortNegativeR051Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR051Q01L (2:Fin 12)) (shortNegativeR051Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR051Q01L (3:Fin 12)) (shortNegativeR051Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR051Q01L (4:Fin 12)) (shortNegativeR051Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR051Q01L (5:Fin 12)) (shortNegativeR051Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR051Q01L (6:Fin 12)) (shortNegativeR051Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR051Q01L (7:Fin 12)) (shortNegativeR051Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR051Q01L (8:Fin 12)) (shortNegativeR051Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR051Q01L (9:Fin 12)) (shortNegativeR051Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR051Q01L (10:Fin 12)) (shortNegativeR051Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR051Q01L (11:Fin 12)) (shortNegativeR051Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR051Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR051Q01P shortNegativeR051Q01F (shortNegativeNodes12 k)).re (shortNegativeR051Q01L k) (shortNegativeR051Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR051Q01Point00
  · exact shortNegativeR051Q01Point01
  · exact shortNegativeR051Q01Point02
  · exact shortNegativeR051Q01Point03
  · exact shortNegativeR051Q01Point04
  · exact shortNegativeR051Q01Point05
  · exact shortNegativeR051Q01Point06
  · exact shortNegativeR051Q01Point07
  · exact shortNegativeR051Q01Point08
  · exact shortNegativeR051Q01Point09
  · exact shortNegativeR051Q01Point10
  · exact shortNegativeR051Q01Point11

theorem shortNegativeR051Q01Bound {t a : ℝ} (tl : ((33/25):ℝ)≤t) (tu : t≤((133/100):ℝ)) (al : ((1374153699686399/1649267441664000):ℝ)≤a) (au : a≤((1382743634278399/1649267441664000):ℝ)) : (((-432112157105145837704460654073495/162259276829213363391578010288128):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-284680388396734485639298903168663/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : shortNegativeR051Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1374153699686399/1649267441664000) (1382743634278399/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR051Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR051Q01F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR051Q01L shortNegativeR051Q01U (-432112157105145837704460654073495/162259276829213363391578010288128) (-284680388396734485639298903168663/162259276829213363391578010288128) shortNegativeR051Q01Samples (by decide +kernel)

def shortNegativeR051Q02T := Grid.ofRats (33/25) (133/100)
def shortNegativeR051Q02P : PrimalThetaParameters := ⟨⟨⟨18525890915760454523603,19117137597722757209060,true⟩,⟨0,0,true⟩⟩, ⟨⟨1592099156736498370434693,1601989657969995054970659,true⟩,⟨0,0,true⟩⟩, ⟨(-613754160163307480178995),(-593973157696382830592048),true⟩, ⟨3525421200858240471078713,3603088329261109570494702,true⟩⟩
theorem shortNegativeR051Q02P_ok : shortNegativeR051Q02P.encloses (primalThetaParameters shortNegativeR051Q02T (Grid.ofRats (1382743634278399/1649267441664000) (463777856290133/549755813888000))) := by decide +kernel

def shortNegativeR051Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨425348117907013126185573,428701947430839803161045,true⟩,⟨3409132256313768163852380,3436012940464693849354528,true⟩,⟨⟨293857463608284181174244,303747964841780865759020,true⟩,⟨1166472085477718233294736,1176362586711214917891527,true⟩⟩⟩
  | 1 => ⟨⟨806888804159035481438,852491928562254083279,true⟩,⟨425348117907013126185573,428701947430839803161045,true⟩,⟨⟨(-838228522973358940425048),(-808557019273006325688688),true⟩,⟨(-900005781727481347864874),(-870334278027128733127647),true⟩⟩⟩
  | 2 => ⟨⟨23456417167081094,26807040144817186,true⟩,⟨806888804159035481438,852491928562254083279,true⟩,⟨⟨1122052481887079099128712,1171504988054287643977813,true⟩,⟨357896498918863643254486,407349005086072188093071,true⟩⟩⟩
  | 3 => ⟨⟨(-23910361666),47689720072,true⟩,⟨23456417167081094,26807040144817186,true⟩,⟨⟨(-1224554830566254908540250),(-1155321321932190433550016),true⟩,⟨178805390792612021246408,248038899426676496223198,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738297),34359738473,true⟩,⟨(-23910361666),47689720072,true⟩,⟨⟨897817131396078560776528,986831642496998965871801,true⟩,⟨(-801822505031634193886804),(-712807993930713788794072),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738297),34359738473,true⟩,⟨⟨(-518842255495177082298113),(-410046741927400747051185),true⟩,⟨1061753194005350943469260,1170548707573127278725156,true⟩⟩⟩
theorem shortNegativeR051Q02F_ok : ∀ n : Fin 6, (shortNegativeR051Q02F n).encloses (FactoredFrequency.build shortNegativeR051Q02T (Grid.ofRats (1382743634278399/1649267441664000) (463777856290133/549755813888000)) n) := by decide +kernel
def shortNegativeR051Q02L : ℕ → ℚ
  | 0 => (-2917261/1000000)
  | 1 => (-2566603/1000000)
  | 2 => (-2217211/1000000)
  | 3 => (-982067/500000)
  | 4 => (-929911/500000)
  | 5 => (-1956951/1000000)
  | 6 => (-88337/40000)
  | 7 => (-642183/250000)
  | 8 => (-2956509/1000000)
  | 9 => (-824877/250000)
  | 10 => (-3436681/1000000)
  | 11 => (-3311891/1000000)
  | _ => 0
def shortNegativeR051Q02U : ℕ → ℚ
  | 0 => (-477609/200000)
  | 1 => (-492847/250000)
  | 2 => (-98169/62500)
  | 3 => (-1281503/1000000)
  | 4 => (-28867/25000)
  | 5 => (-586589/500000)
  | 6 => (-1356993/1000000)
  | 7 => (-52277/31250)
  | 8 => (-41111/20000)
  | 9 => (-2375901/1000000)
  | 10 => (-513421/200000)
  | 11 => (-1278639/500000)
  | _ => 0
private theorem shortNegativeR051Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR051Q02L (0:Fin 12)) (shortNegativeR051Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR051Q02L (1:Fin 12)) (shortNegativeR051Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR051Q02L (2:Fin 12)) (shortNegativeR051Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR051Q02L (3:Fin 12)) (shortNegativeR051Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR051Q02L (4:Fin 12)) (shortNegativeR051Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR051Q02L (5:Fin 12)) (shortNegativeR051Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR051Q02L (6:Fin 12)) (shortNegativeR051Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR051Q02L (7:Fin 12)) (shortNegativeR051Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR051Q02L (8:Fin 12)) (shortNegativeR051Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR051Q02L (9:Fin 12)) (shortNegativeR051Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR051Q02L (10:Fin 12)) (shortNegativeR051Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR051Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR051Q02L (11:Fin 12)) (shortNegativeR051Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR051Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR051Q02P shortNegativeR051Q02F (shortNegativeNodes12 k)).re (shortNegativeR051Q02L k) (shortNegativeR051Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR051Q02Point00
  · exact shortNegativeR051Q02Point01
  · exact shortNegativeR051Q02Point02
  · exact shortNegativeR051Q02Point03
  · exact shortNegativeR051Q02Point04
  · exact shortNegativeR051Q02Point05
  · exact shortNegativeR051Q02Point06
  · exact shortNegativeR051Q02Point07
  · exact shortNegativeR051Q02Point08
  · exact shortNegativeR051Q02Point09
  · exact shortNegativeR051Q02Point10
  · exact shortNegativeR051Q02Point11

theorem shortNegativeR051Q02Bound {t a : ℝ} (tl : ((33/25):ℝ)≤t) (tu : t≤((133/100):ℝ)) (al : ((1382743634278399/1649267441664000):ℝ)≤a) (au : a≤((463777856290133/549755813888000):ℝ)) : (((-432112157105145837704460654073495/162259276829213363391578010288128):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-284680388396734485639298903168663/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : shortNegativeR051Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1382743634278399/1649267441664000) (463777856290133/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR051Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR051Q02F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR051Q02L shortNegativeR051Q02U (-432112157105145837704460654073495/162259276829213363391578010288128) (-284680388396734485639298903168663/162259276829213363391578010288128) shortNegativeR051Q02Samples (by decide +kernel)

theorem short_original_negative_051 {t a : ℝ} (tb : RealMem negative_051.t t) (ab : RealMem negative_051.a a) : RealMem negative_051.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((33/25):ℝ) ((133/100):ℝ) := by simpa [negative_051,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((33/25):ℝ)<((133/100):ℝ)) tB
  have aB : a∈Icc ((455187921698133/549755813888000):ℝ) ((463777856290133/549755813888000):ℝ) := by simpa [negative_051,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((455187921698133/549755813888000):ℝ)<((463777856290133/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR051Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_051,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR051Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_051,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR051Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_051,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_050
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_051
