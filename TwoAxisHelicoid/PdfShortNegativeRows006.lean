import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip000

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR006Q00T := Grid.ofRats (183/200) (23/25)
def shortNegativeR006Q00P : PrimalThetaParameters := ⟨⟨⟨67169699840695898513540,68233129308286847394888,true⟩,⟨0,0,true⟩⟩, ⟨⟨1156613251247922405769287,1160322189210526612145017,true⟩,⟨0,0,true⟩⟩, ⟨(-1484725971140459409512581),(-1477308095215319716240519),true⟩, ⟨5811075813971240123592536,5896990861800628533049579,true⟩⟩
theorem shortNegativeR006Q00P_ok : shortNegativeR006Q00P.encloses (primalThetaParameters shortNegativeR006Q00T (Grid.ofRats (1004522616394937/1649267441664000) (1007743841866937/1649267441664000))) := by decide +kernel

def shortNegativeR006Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨586939167509485986564338,589248603830239803374928,true⟩,⟨2480280187056702379215863,2490039374152376784657962,true⟩,⟨⟨693208778299292356500474,696917716261896562923810,true⟩,⟨987280870398834550394230,990989808361438756821632,true⟩⟩⟩
  | 1 => ⟨⟨7686944110098852849976,7901181105824950878129,true⟩,⟨586939167509485986564338,589248603830239803374928,true⟩,⟨⟨(-1171714743855506272367824),(-1160587929967831092126177),true⟩,⟨313172685693991422017100,324299499581666602247083,true⟩⟩⟩
  | 2 => ⟨⟨5593557501023196641,5979723593081411664,true⟩,⟨7686944110098852849976,7901181105824950878129,true⟩,⟨⟨86038532291328478233046,104583222104074632283425,true⟩,⟨(-1214435186193270526624309),(-1195890496380524372558659),true⟩⟩⟩
  | 3 => ⟨⟨226115462247276,255460790025559,true⟩,⟨5593557501023196641,5979723593081411664,true⟩,⟨⟨1088571876487270340201936,1114534442225087468051079,true⟩,⟨485097299729584264566863,511059865467401392407706,true⟩⟩⟩
  | 4 => ⟨⟨(-33851721486),34975547603,true⟩,⟨226115462247276,255460790025559,true⟩,⟨⟨(-858592973658396148156749),(-825212531995508046480544),true⟩,⟨850893430532101941903393,884273872194990043579948,true⟩⟩⟩
  | _ => ⟨⟨(-34359738305),34359738452,true⟩,⟨(-33851721486),34975547603,true⟩,⟨⟨(-551341857827140955957898),(-510543540239181880486309),true⟩,⟨(-1106493762258283972829773),(-1065695444670324897350541),true⟩⟩⟩
theorem shortNegativeR006Q00F_ok : ∀ n : Fin 6, (shortNegativeR006Q00F n).encloses (FactoredFrequency.build shortNegativeR006Q00T (Grid.ofRats (1004522616394937/1649267441664000) (1007743841866937/1649267441664000)) n) := by decide +kernel
def shortNegativeR006Q00L : ℕ → ℚ
  | 0 => (2218421/1000000)
  | 1 => (1435783/500000)
  | 2 => (655251/250000)
  | 3 => (2017319/1000000)
  | 4 => (11723/10000)
  | 5 => (-55621/1000000)
  | 6 => (-886023/500000)
  | 7 => (-3827879/1000000)
  | 8 => (-87784/15625)
  | 9 => (-117911/20000)
  | 10 => (-1915597/500000)
  | 11 => (-457061/1000000)
  | _ => 0
def shortNegativeR006Q00U : ℕ → ℚ
  | 0 => (1364229/500000)
  | 1 => (3394211/1000000)
  | 2 => (1566147/500000)
  | 3 => (1251049/500000)
  | 4 => (1625927/1000000)
  | 5 => (113389/250000)
  | 6 => (-1130749/1000000)
  | 7 => (-3044401/1000000)
  | 8 => (-4631789/1000000)
  | 9 => (-184837/40000)
  | 10 => (-1174127/500000)
  | 11 => (17431/20000)
  | _ => 0
private theorem shortNegativeR006Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR006Q00L (0:Fin 12)) (shortNegativeR006Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR006Q00L (1:Fin 12)) (shortNegativeR006Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR006Q00L (2:Fin 12)) (shortNegativeR006Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR006Q00L (3:Fin 12)) (shortNegativeR006Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR006Q00L (4:Fin 12)) (shortNegativeR006Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR006Q00L (5:Fin 12)) (shortNegativeR006Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR006Q00L (6:Fin 12)) (shortNegativeR006Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR006Q00L (7:Fin 12)) (shortNegativeR006Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR006Q00L (8:Fin 12)) (shortNegativeR006Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR006Q00L (9:Fin 12)) (shortNegativeR006Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR006Q00L (10:Fin 12)) (shortNegativeR006Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR006Q00L (11:Fin 12)) (shortNegativeR006Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR006Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR006Q00P shortNegativeR006Q00F (shortNegativeNodes12 k)).re (shortNegativeR006Q00L k) (shortNegativeR006Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR006Q00Point00
  · exact shortNegativeR006Q00Point01
  · exact shortNegativeR006Q00Point02
  · exact shortNegativeR006Q00Point03
  · exact shortNegativeR006Q00Point04
  · exact shortNegativeR006Q00Point05
  · exact shortNegativeR006Q00Point06
  · exact shortNegativeR006Q00Point07
  · exact shortNegativeR006Q00Point08
  · exact shortNegativeR006Q00Point09
  · exact shortNegativeR006Q00Point10
  · exact shortNegativeR006Q00Point11

theorem shortNegativeR006Q00Bound {t a : ℝ} (tl : ((183/200):ℝ)≤t) (tu : t≤((23/25):ℝ)) (al : ((1004522616394937/1649267441664000):ℝ)≤a) (au : a≤((1007743841866937/1649267441664000):ℝ)) : (((-4791420127552020153915395681810415/5192296858534827628530496329220096):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-238070159187588210339310175778799/5192296858534827628530496329220096):ℚ):ℝ) := by
  have ts : shortNegativeR006Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1004522616394937/1649267441664000) (1007743841866937/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR006Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR006Q00F_ok n) ts asb
  exact factored_negative_12_samples 17310 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR006Q00L shortNegativeR006Q00U (-4791420127552020153915395681810415/5192296858534827628530496329220096) (-238070159187588210339310175778799/5192296858534827628530496329220096) shortNegativeR006Q00Samples (by decide +kernel)

def shortNegativeR006Q01T := Grid.ofRats (183/200) (23/25)
def shortNegativeR006Q01P : PrimalThetaParameters := ⟨⟨⟨67169699840695898513540,68233129308286847394888,true⟩,⟨0,0,true⟩⟩, ⟨⟨1160322189210457892664584,1164031127173062099040327,true⟩,⟨0,0,true⟩⟩, ⟨(-1477308095215388435721962),(-1469890219290248742449924),true⟩, ⟨5793609883585595990765333,5879065411885267050777545,true⟩⟩
theorem shortNegativeR006Q01P_ok : shortNegativeR006Q01P.encloses (primalThetaParameters shortNegativeR006Q01T (Grid.ofRats (1007743841866937/1649267441664000) (1010965067338937/1649267441664000))) := by decide +kernel

def shortNegativeR006Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨586939167509485986564338,589248603830239803374928,true⟩,⟨2480280187056702379215863,2490039374152376784657962,true⟩,⟨⟨690170882745354113033213,693879820707958319456647,true⟩,⟨989408639329756081740062,993117577292360288167623,true⟩⟩⟩
  | 1 => ⟨⟨7686944110098852849976,7901181105824950878129,true⟩,⟨586939167509485986564338,589248603830239803374928,true⟩,⟨⟨(-1174598919829983922719820),(-1163472105942308742477913),true⟩,⟨302426214540276238043449,313553028427951418273494,true⟩⟩⟩
  | 2 => ⟨⟨5593557501023196641,5979723593081411664,true⟩,⟨7686944110098852849976,7901181105824950878129,true⟩,⟨⟨104513560153487025971768,123058249966233180022339,true⟩,⟨(-1212831402510365944434825),(-1194286712697619790369257),true⟩⟩⟩
  | 3 => ⟨⟨226115462247276,255460790025559,true⟩,⟨5593557501023196641,5979723593081411664,true⟩,⟨⟨1077622084757158844630631,1103584650494975972480724,true⟩,⟨508637286445474435194827,534599852183291563037094,true⟩⟩⟩
  | 4 => ⟨⟨(-33851721486),34975547603,true⟩,⟨226115462247276,255460790025559,true⟩,⟨⟨(-882224435190063468141303),(-848843993527175366465077),true⟩,⟨827319353228892287900862,860699794891780389576787,true⟩⟩⟩
  | _ => ⟨⟨(-34359738305),34359738452,true⟩,⟨(-33851721486),34975547603,true⟩,⟨⟨(-514393436810657753685707),(-473595119222698678213804),true⟩,⟨(-1123789973790045991633224),(-1082991656202086916152934),true⟩⟩⟩
theorem shortNegativeR006Q01F_ok : ∀ n : Fin 6, (shortNegativeR006Q01F n).encloses (FactoredFrequency.build shortNegativeR006Q01T (Grid.ofRats (1007743841866937/1649267441664000) (1010965067338937/1649267441664000)) n) := by decide +kernel
def shortNegativeR006Q01L : ℕ → ℚ
  | 0 => (1085223/500000)
  | 1 => (1420433/500000)
  | 2 => (1302339/500000)
  | 3 => (2010949/1000000)
  | 4 => (587267/500000)
  | 5 => (-43503/1000000)
  | 6 => (-1748597/1000000)
  | 7 => (-3795321/1000000)
  | 8 => (-1395961/250000)
  | 9 => (-1471121/250000)
  | 10 => (-3857223/1000000)
  | 11 => (-50679/100000)
  | _ => 0
def shortNegativeR006Q01U : ℕ → ℚ
  | 0 => (2677279/1000000)
  | 1 => (52519/15625)
  | 2 => (3114547/1000000)
  | 3 => (1247473/500000)
  | 4 => (65109/40000)
  | 5 => (465053/1000000)
  | 6 => (-11087/10000)
  | 7 => (-3013743/1000000)
  | 8 => (-921507/200000)
  | 9 => (-4620979/1000000)
  | 10 => (-2386587/1000000)
  | 11 => (405021/500000)
  | _ => 0
private theorem shortNegativeR006Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR006Q01L (0:Fin 12)) (shortNegativeR006Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR006Q01L (1:Fin 12)) (shortNegativeR006Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR006Q01L (2:Fin 12)) (shortNegativeR006Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR006Q01L (3:Fin 12)) (shortNegativeR006Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR006Q01L (4:Fin 12)) (shortNegativeR006Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR006Q01L (5:Fin 12)) (shortNegativeR006Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR006Q01L (6:Fin 12)) (shortNegativeR006Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR006Q01L (7:Fin 12)) (shortNegativeR006Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR006Q01L (8:Fin 12)) (shortNegativeR006Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR006Q01L (9:Fin 12)) (shortNegativeR006Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR006Q01L (10:Fin 12)) (shortNegativeR006Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR006Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR006Q01L (11:Fin 12)) (shortNegativeR006Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR006Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR006Q01P shortNegativeR006Q01F (shortNegativeNodes12 k)).re (shortNegativeR006Q01L k) (shortNegativeR006Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR006Q01Point00
  · exact shortNegativeR006Q01Point01
  · exact shortNegativeR006Q01Point02
  · exact shortNegativeR006Q01Point03
  · exact shortNegativeR006Q01Point04
  · exact shortNegativeR006Q01Point05
  · exact shortNegativeR006Q01Point06
  · exact shortNegativeR006Q01Point07
  · exact shortNegativeR006Q01Point08
  · exact shortNegativeR006Q01Point09
  · exact shortNegativeR006Q01Point10
  · exact shortNegativeR006Q01Point11

theorem shortNegativeR006Q01Bound {t a : ℝ} (tl : ((183/200):ℝ)≤t) (tu : t≤((23/25):ℝ)) (al : ((1007743841866937/1649267441664000):ℝ)≤a) (au : a≤((1010965067338937/1649267441664000):ℝ)) : (((-4791420127552020153915395681810415/5192296858534827628530496329220096):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-238070159187588210339310175778799/5192296858534827628530496329220096):ℚ):ℝ) := by
  have ts : shortNegativeR006Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1007743841866937/1649267441664000) (1010965067338937/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR006Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR006Q01F_ok n) ts asb
  exact factored_negative_12_samples 17310 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR006Q01L shortNegativeR006Q01U (-4791420127552020153915395681810415/5192296858534827628530496329220096) (-238070159187588210339310175778799/5192296858534827628530496329220096) shortNegativeR006Q01Samples (by decide +kernel)

theorem short_original_negative_006 {t a : ℝ} (tb : RealMem negative_006.t t) (ab : RealMem negative_006.a a) : RealMem negative_006.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((183/200):ℝ) ((23/25):ℝ) := by simpa [negative_006,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((183/200):ℝ)<((23/25):ℝ)) tB
  have aB : a∈Icc ((1004522616394937/1649267441664000):ℝ) ((1010965067338937/1649267441664000):ℝ) := by simpa [negative_006,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1004522616394937/1649267441664000):ℝ)<((1010965067338937/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR006Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_006,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR006Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_006,RealMem] using v

def shortNegativeR007Q00T := Grid.ofRats (23/25) (37/40)
def shortNegativeR007Q00P : PrimalThetaParameters := ⟨⟨⟨66122844173083764062562,67169699840764617991196,true⟩,⟨0,0,true⟩⟩, ⟨⟨1159988158493753859932140,1163697096456358066307881,true⟩,⟨0,0,true⟩⟩, ⟨(-1477976156648796501186853),(-1470558280723656807914813),true⟩, ⟨5773100942909721730606845,5857662765622898712738933,true⟩⟩
theorem shortNegativeR007Q00P_ok : shortNegativeR007Q00P.encloses (primalThetaParameters shortNegativeR007Q00T (Grid.ofRats (1007453735032057/1649267441664000) (1010674960504057/1649267441664000))) := by decide +kernel

def shortNegativeR007Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨584638782540105976755628,586939167509554706062404,true⟩,⟨2490039374152308065090766,2499836960834151828532951,true⟩,⟨⟨690444746023030697968372,694153683985634904391852,true⟩,⟨989217392305904205840071,992926330268508412267687,true⟩⟩⟩
  | 1 => ⟨⟨7478516054863642629860,7686944110167572327099,true⟩,⟨584638782540105976755628,586939167509554706062404,true⟩,⟨⟨(-1174343222194440650616153),(-1163216408306765470373863),true⟩,⟨303395135248588440519639,314521949136263620750091,true⟩⟩⟩
  | 2 => ⟨⟨5232329787309783955,5593557569742673378,true⟩,⟨7478516054863642629860,7686944110167572327099,true⟩,⟨⟨102850712795246566126747,121395402607992720176558,true⟩,⟨(-1212987451259426282840200),(-1194442761446680128775368),true⟩⟩⟩
  | 3 => ⟨⟨200194496479193,226184181724013,true⟩,⟨5232329787309783955,5593557569742673378,true⟩,⟨⟨1078628920345112073968814,1104591486082929201818819,true⟩,⟨506526947643320650369481,532489513381137778211617,true⟩⟩⟩
  | 4 => ⟨⟨(-33940645671),34867755251,true⟩,⟨200194496479193,226184181724013,true⟩,⟨⟨(-880122934227407265373759),(-846742492564519163698184),true⟩,⟨829469094409242384694592,862849536072130486369928,true⟩⟩⟩
  | _ => ⟨⟨(-34359738321),34359738432,true⟩,⟨(-33940645671),34867755251,true⟩,⟨⟨(-517744731000727463678122),(-476946413412768388207663),true⟩,⟨(-1122283462674039988791779),(-1081485145086080913312998),true⟩⟩⟩
theorem shortNegativeR007Q00F_ok : ∀ n : Fin 6, (shortNegativeR007Q00F n).encloses (FactoredFrequency.build shortNegativeR007Q00T (Grid.ofRats (1007453735032057/1649267441664000) (1010674960504057/1649267441664000)) n) := by decide +kernel
def shortNegativeR007Q00L : ℕ → ℚ
  | 0 => (2078283/1000000)
  | 1 => (691031/250000)
  | 2 => (636699/250000)
  | 3 => (981353/500000)
  | 4 => (1129619/1000000)
  | 5 => (-10771/125000)
  | 6 => (-89047/50000)
  | 7 => (-3804453/1000000)
  | 8 => (-5560547/1000000)
  | 9 => (-182787/31250)
  | 10 => (-3859179/1000000)
  | 11 => (-285281/500000)
  | _ => 0
def shortNegativeR007Q00U : ℕ → ℚ
  | 0 => (2583313/1000000)
  | 1 => (328337/100000)
  | 2 => (3056169/1000000)
  | 3 => (2446859/1000000)
  | 4 => (1583381/1000000)
  | 5 => (424041/1000000)
  | 6 => (-285091/250000)
  | 7 => (-756269/250000)
  | 8 => (-4592033/1000000)
  | 9 => (-4598559/1000000)
  | 10 => (-37609/15625)
  | 11 => (145821/200000)
  | _ => 0
private theorem shortNegativeR007Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR007Q00L (0:Fin 12)) (shortNegativeR007Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR007Q00L (1:Fin 12)) (shortNegativeR007Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR007Q00L (2:Fin 12)) (shortNegativeR007Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR007Q00L (3:Fin 12)) (shortNegativeR007Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR007Q00L (4:Fin 12)) (shortNegativeR007Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR007Q00L (5:Fin 12)) (shortNegativeR007Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR007Q00L (6:Fin 12)) (shortNegativeR007Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR007Q00L (7:Fin 12)) (shortNegativeR007Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR007Q00L (8:Fin 12)) (shortNegativeR007Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR007Q00L (9:Fin 12)) (shortNegativeR007Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR007Q00L (10:Fin 12)) (shortNegativeR007Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR007Q00L (11:Fin 12)) (shortNegativeR007Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR007Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR007Q00P shortNegativeR007Q00F (shortNegativeNodes12 k)).re (shortNegativeR007Q00L k) (shortNegativeR007Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR007Q00Point00
  · exact shortNegativeR007Q00Point01
  · exact shortNegativeR007Q00Point02
  · exact shortNegativeR007Q00Point03
  · exact shortNegativeR007Q00Point04
  · exact shortNegativeR007Q00Point05
  · exact shortNegativeR007Q00Point06
  · exact shortNegativeR007Q00Point07
  · exact shortNegativeR007Q00Point08
  · exact shortNegativeR007Q00Point09
  · exact shortNegativeR007Q00Point10
  · exact shortNegativeR007Q00Point11

theorem shortNegativeR007Q00Bound {t a : ℝ} (tl : ((23/25):ℝ)≤t) (tu : t≤((37/40):ℝ)) (al : ((1007453735032057/1649267441664000):ℝ)≤a) (au : a≤((1010674960504057/1649267441664000):ℝ)) : (((-4986035917771420188247822980486157/5192296858534827628530496329220096):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-500782032832044369313585026700301/5192296858534827628530496329220096):ℚ):ℝ) := by
  have ts : shortNegativeR007Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1007453735032057/1649267441664000) (1010674960504057/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR007Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR007Q00F_ok n) ts asb
  exact factored_negative_12_samples 17310 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR007Q00L shortNegativeR007Q00U (-4986035917771420188247822980486157/5192296858534827628530496329220096) (-500782032832044369313585026700301/5192296858534827628530496329220096) shortNegativeR007Q00Samples (by decide +kernel)

def shortNegativeR007Q01T := Grid.ofRats (23/25) (37/40)
def shortNegativeR007Q01P : PrimalThetaParameters := ⟨⟨⟨66122844173083764062562,67169699840764617991196,true⟩,⟨0,0,true⟩⟩, ⟨⟨1163697096456289346827438,1167406034418893553203191,true⟩,⟨0,0,true⟩⟩, ⟨(-1470558280723725527396234),(-1463140404798585834124217),true⟩, ⟨5755772418763703869729885,5839882556312094795634756,true⟩⟩
theorem shortNegativeR007Q01P_ok : shortNegativeR007Q01P.encloses (primalThetaParameters shortNegativeR007Q01T (Grid.ofRats (1010674960504057/1649267441664000) (1013896185976057/1649267441664000))) := by decide +kernel

def shortNegativeR007Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨584638782540105976755628,586939167509554706062404,true⟩,⟨2490039374152308065090766,2499836960834151828532951,true⟩,⟨⟨687400922311673258077398,691109860274277464500990,true⟩,⟨991336672191669869403793,995045610154274075831662,true⟩⟩⟩
  | 1 => ⟨⟨7478516054863642629860,7686944110167572327099,true⟩,⟨584638782540105976755628,586939167509554706062404,true⟩,⟨⟨(-1177137296661871893322823),(-1166010482774196713080789),true⟩,⟨292624886357321559554022,303751700244996739784032,true⟩⟩⟩
  | 2 => ⟨⟨5232329787309783955,5593557569742673378,true⟩,⟨7478516054863642629860,7686944110167572327099,true⟩,⟨⟨121301555556772368901357,139846245369518522951657,true⟩,⟨(-1211125952401372238132947),(-1192581262588626084067902),true⟩⟩⟩
  | 3 => ⟨⟨200194496479193,226184181724013,true⟩,⟨5232329787309783955,5593557569742673378,true⟩,⟨⟨1067221239427905438041121,1093183805165722565891535,true⟩,⟨529848476958704394428581,555811042696521522271596,true⟩⟩⟩
  | 4 => ⟨⟨(-33940645671),34867755251,true⟩,⟨200194496479193,226184181724013,true⟩,⟨⟨(-903154702827528518162373),(-869774261164640416486168),true⟩,⟨805308781291013854214472,838689222953901955889784,true⟩⟩⟩
  | _ => ⟨⟨(-34359738321),34359738432,true⟩,⟨(-33940645671),34867755251,true⟩,⟨⟨(-480282677039999002506444),(-439484359452039927036318),true⟩,⟨(-1138437077192352107100752),(-1097638759604393031621567),true⟩⟩⟩
theorem shortNegativeR007Q01F_ok : ∀ n : Fin 6, (shortNegativeR007Q01F n).encloses (FactoredFrequency.build shortNegativeR007Q01T (Grid.ofRats (1010674960504057/1649267441664000) (1013896185976057/1649267441664000)) n) := by decide +kernel
def shortNegativeR007Q01L : ℕ → ℚ
  | 0 => (2031047/1000000)
  | 1 => (1366743/500000)
  | 2 => (632581/250000)
  | 3 => (1956199/1000000)
  | 4 => (1131741/1000000)
  | 5 => (-37097/500000)
  | 6 => (-1757753/1000000)
  | 7 => (-1886147/500000)
  | 8 => (-552659/100000)
  | 9 => (-5837791/1000000)
  | 10 => (-3883889/1000000)
  | 11 => (-61879/100000)
  | _ => 0
def shortNegativeR007Q01U : ℕ → ℚ
  | 0 => (2532889/1000000)
  | 1 => (325043/100000)
  | 2 => (759563/250000)
  | 3 => (2439541/1000000)
  | 4 => (1585043/1000000)
  | 5 => (435373/1000000)
  | 6 => (-559293/500000)
  | 7 => (-119793/40000)
  | 8 => (-913603/200000)
  | 9 => (-574771/125000)
  | 10 => (-2443877/1000000)
  | 11 => (83651/125000)
  | _ => 0
private theorem shortNegativeR007Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR007Q01L (0:Fin 12)) (shortNegativeR007Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR007Q01L (1:Fin 12)) (shortNegativeR007Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR007Q01L (2:Fin 12)) (shortNegativeR007Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR007Q01L (3:Fin 12)) (shortNegativeR007Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR007Q01L (4:Fin 12)) (shortNegativeR007Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR007Q01L (5:Fin 12)) (shortNegativeR007Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR007Q01L (6:Fin 12)) (shortNegativeR007Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR007Q01L (7:Fin 12)) (shortNegativeR007Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR007Q01L (8:Fin 12)) (shortNegativeR007Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR007Q01L (9:Fin 12)) (shortNegativeR007Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR007Q01L (10:Fin 12)) (shortNegativeR007Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR007Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR007Q01L (11:Fin 12)) (shortNegativeR007Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR007Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR007Q01P shortNegativeR007Q01F (shortNegativeNodes12 k)).re (shortNegativeR007Q01L k) (shortNegativeR007Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR007Q01Point00
  · exact shortNegativeR007Q01Point01
  · exact shortNegativeR007Q01Point02
  · exact shortNegativeR007Q01Point03
  · exact shortNegativeR007Q01Point04
  · exact shortNegativeR007Q01Point05
  · exact shortNegativeR007Q01Point06
  · exact shortNegativeR007Q01Point07
  · exact shortNegativeR007Q01Point08
  · exact shortNegativeR007Q01Point09
  · exact shortNegativeR007Q01Point10
  · exact shortNegativeR007Q01Point11

theorem shortNegativeR007Q01Bound {t a : ℝ} (tl : ((23/25):ℝ)≤t) (tu : t≤((37/40):ℝ)) (al : ((1010674960504057/1649267441664000):ℝ)≤a) (au : a≤((1013896185976057/1649267441664000):ℝ)) : (((-4986035917771420188247822980486157/5192296858534827628530496329220096):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-500782032832044369313585026700301/5192296858534827628530496329220096):ℚ):ℝ) := by
  have ts : shortNegativeR007Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1010674960504057/1649267441664000) (1013896185976057/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR007Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR007Q01F_ok n) ts asb
  exact factored_negative_12_samples 17310 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR007Q01L shortNegativeR007Q01U (-4986035917771420188247822980486157/5192296858534827628530496329220096) (-500782032832044369313585026700301/5192296858534827628530496329220096) shortNegativeR007Q01Samples (by decide +kernel)

theorem short_original_negative_007 {t a : ℝ} (tb : RealMem negative_007.t t) (ab : RealMem negative_007.a a) : RealMem negative_007.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((23/25):ℝ) ((37/40):ℝ) := by simpa [negative_007,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((23/25):ℝ)<((37/40):ℝ)) tB
  have aB : a∈Icc ((1007453735032057/1649267441664000):ℝ) ((1013896185976057/1649267441664000):ℝ) := by simpa [negative_007,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1007453735032057/1649267441664000):ℝ)<((1013896185976057/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR007Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_007,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR007Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_007,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_006
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_007
