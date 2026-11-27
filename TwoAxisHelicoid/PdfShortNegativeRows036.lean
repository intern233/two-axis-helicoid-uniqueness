import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip032

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR036Q00T := Grid.ofRats (117/100) (47/40)
def shortNegativeR036Q00P : PrimalThetaParameters := ⟨⟨⟨30147925774819831177995,30625227188020849301106,true⟩,⟨0,0,true⟩⟩, ⟨⟨1373007114523412119247563,1387842866373622786309911,true⟩,⟨0,0,true⟩⟩, ⟨(-1051938244589479982554650),(-1022266740889127367912180),true⟩, ⟨4166819612039443613916170,4306732134467849805454825,true⟩⟩
theorem shortNegativeR036Q00P_ok : shortNegativeR036Q00P.encloses (primalThetaParameters shortNegativeR036Q00T (Grid.ofRats (1192461436458397/1649267441664000) (1205346338346397/1649267441664000))) := by decide +kernel

def shortNegativeR036Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨480412279047739506419319,482302562790233776321684,true⟩,⟨3030258908175523075656264,3042182102896630217970744,true⟩,⟨⟨495378007191569109971328,510213759041779777082309,true⟩,⟨1091990118066127372301900,1106825869916338039421152,true⟩⟩⟩
  | 1 => ⟨⟨1891911318984473561684,1944639346111758328292,true⟩,⟨480412279047739506419319,482302562790233776321684,true⟩,⟨⟨(-1182756180346160686620467),(-1138248924795666124313849),true⟩,⟨(-360979863557622552781180),(-316472608007127990485864),true⟩⟩⟩
  | 2 => ⟨⟨185799763051701718,198627011691945471,true⟩,⟨1891911318984473561684,1944639346111758328292,true⟩,⟨⟨978166683135624532623038,1052345442386402990105714,true⟩,⟨(-693410005811940983254321),(-619231246561162525776587),true⟩⟩⟩
  | 3 => ⟨⟨420678067854,548305234626,true⟩,⟨185799763051701718,198627011691945471,true⟩,⟨⟨(-219477772082920035262799),(-115627509131857682587517),true⟩,⟨1145333299255442671825589,1249183562206505024515042,true⟩⟩⟩
  | 4 => ⟨⟨(-34359710577),34359772057,true⟩,⟨420678067854,548305234626,true⟩,⟨⟨(-862841545267868659595329),(-729319778616522411739997),true⟩,⟨(-976572521530295513373396),(-843050754878949265516493),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359710577),34359772057,true⟩,⟨⟨1127308129353853736250138,1290501399705483879232033,true⟩,⟨(-88731593365526619028553),74461676986103523937830,true⟩⟩⟩
theorem shortNegativeR036Q00F_ok : ∀ n : Fin 6, (shortNegativeR036Q00F n).encloses (FactoredFrequency.build shortNegativeR036Q00T (Grid.ofRats (1192461436458397/1649267441664000) (1205346338346397/1649267441664000)) n) := by decide +kernel
def shortNegativeR036Q00L : ℕ → ℚ
  | 0 => (-567327/250000)
  | 1 => (-1493719/1000000)
  | 2 => (-1021381/1000000)
  | 3 => (-884563/1000000)
  | 4 => (-1052893/1000000)
  | 5 => (-1538617/1000000)
  | 6 => (-2241277/1000000)
  | 7 => (-190797/62500)
  | 8 => (-1896513/500000)
  | 9 => (-169837/40000)
  | 10 => (-163713/40000)
  | 11 => (-209047/62500)
  | _ => 0
def shortNegativeR036Q00U : ℕ → ℚ
  | 0 => (-104349/62500)
  | 1 => (-857489/1000000)
  | 2 => (-167559/500000)
  | 3 => (-6257/40000)
  | 4 => (-72201/250000)
  | 5 => (-647861/1000000)
  | 6 => (-619851/500000)
  | 7 => (-992127/500000)
  | 8 => (-679541/250000)
  | 9 => (-385607/125000)
  | 10 => (-744013/250000)
  | 11 => (-2410891/1000000)
  | _ => 0
private theorem shortNegativeR036Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR036Q00L (0:Fin 12)) (shortNegativeR036Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR036Q00L (1:Fin 12)) (shortNegativeR036Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR036Q00L (2:Fin 12)) (shortNegativeR036Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR036Q00L (3:Fin 12)) (shortNegativeR036Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR036Q00L (4:Fin 12)) (shortNegativeR036Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR036Q00L (5:Fin 12)) (shortNegativeR036Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR036Q00L (6:Fin 12)) (shortNegativeR036Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR036Q00L (7:Fin 12)) (shortNegativeR036Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR036Q00L (8:Fin 12)) (shortNegativeR036Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR036Q00L (9:Fin 12)) (shortNegativeR036Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR036Q00L (10:Fin 12)) (shortNegativeR036Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR036Q00L (11:Fin 12)) (shortNegativeR036Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR036Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR036Q00P shortNegativeR036Q00F (shortNegativeNodes12 k)).re (shortNegativeR036Q00L k) (shortNegativeR036Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR036Q00Point00
  · exact shortNegativeR036Q00Point01
  · exact shortNegativeR036Q00Point02
  · exact shortNegativeR036Q00Point03
  · exact shortNegativeR036Q00Point04
  · exact shortNegativeR036Q00Point05
  · exact shortNegativeR036Q00Point06
  · exact shortNegativeR036Q00Point07
  · exact shortNegativeR036Q00Point08
  · exact shortNegativeR036Q00Point09
  · exact shortNegativeR036Q00Point10
  · exact shortNegativeR036Q00Point11

theorem shortNegativeR036Q00Bound {t a : ℝ} (tl : ((117/100):ℝ)≤t) (tu : t≤((47/40):ℝ)) (al : ((1192461436458397/1649267441664000):ℝ)≤a) (au : a≤((1205346338346397/1649267441664000):ℝ)) : (((-3164482854585307430050175420975623/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1932825149437282027486058678831623/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR036Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1192461436458397/1649267441664000) (1205346338346397/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR036Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR036Q00F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR036Q00L shortNegativeR036Q00U (-3164482854585307430050175420975623/1298074214633706907132624082305024) (-1932825149437282027486058678831623/1298074214633706907132624082305024) shortNegativeR036Q00Samples (by decide +kernel)

def shortNegativeR036Q10T := Grid.ofRats (47/40) (59/50)
def shortNegativeR036Q10P : PrimalThetaParameters := ⟨⟨⟨29678063217163760835761,30147925774888550655224,true⟩,⟨0,0,true⟩⟩, ⟨⟨1373007114523412119247563,1387842866373622786309911,true⟩,⟨0,0,true⟩⟩, ⟨(-1051938244589479982554650),(-1022266740889127367912180),true⟩, ⟨4156928195950081112920156,4296111006081099679946281,true⟩⟩
theorem shortNegativeR036Q10P_ok : shortNegativeR036Q10P.encloses (primalThetaParameters shortNegativeR036Q10T (Grid.ofRats (1192461436458397/1649267441664000) (1205346338346397/1649267441664000))) := by decide +kernel

def shortNegativeR036Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨478529403875996655591072,480412279047808225913846,true⟩,⟨3042182102896561498381527,3054152211949632898827814,true⟩,⟨⟨495378007191569109971328,510213759041779777082309,true⟩,⟨1091990118066127372301900,1106825869916338039421152,true⟩⟩⟩
  | 1 => ⟨⟨1840612988822197511579,1891911319053193038525,true⟩,⟨478529403875996655591072,480412279047808225913846,true⟩,⟨⟨(-1182756180346160686620467),(-1138248924795666124313849),true⟩,⟨(-360979863557622552781180),(-316472608007127990485864),true⟩⟩⟩
  | 2 => ⟨⟨173800952705549627,185799831771178455,true⟩,⟨1840612988822197511579,1891911319053193038525,true⟩,⟨⟨978166683135624532623038,1052345442386402990105714,true⟩,⟨(-693410005811940983254321),(-619231246561162525776587),true⟩⟩⟩
  | 3 => ⟨⟨368522292117,489397544591,true⟩,⟨173800952705549627,185799831771178455,true⟩,⟨⟨(-219477772082920035262799),(-115627509131857682587517),true⟩,⟨1145333299255442671825589,1249183562206505024515042,true⟩⟩⟩
  | 4 => ⟨⟨(-34359715442),34359766160,true⟩,⟨368522292117,489397544591,true⟩,⟨⟨(-862841545267868659595329),(-729319778616522411739997),true⟩,⟨(-976572521530295513373396),(-843050754878949265516493),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359715442),34359766160,true⟩,⟨⟨1127308129353853736250138,1290501399705483879232033,true⟩,⟨(-88731593365526619028553),74461676986103523937830,true⟩⟩⟩
theorem shortNegativeR036Q10F_ok : ∀ n : Fin 6, (shortNegativeR036Q10F n).encloses (FactoredFrequency.build shortNegativeR036Q10T (Grid.ofRats (1192461436458397/1649267441664000) (1205346338346397/1649267441664000)) n) := by decide +kernel
def shortNegativeR036Q10L : ℕ → ℚ
  | 0 => (-457393/200000)
  | 1 => (-1522593/1000000)
  | 2 => (-1054623/1000000)
  | 3 => (-918153/1000000)
  | 4 => (-108397/100000)
  | 5 => (-1564359/1000000)
  | 6 => (-2258661/1000000)
  | 7 => (-764673/250000)
  | 8 => (-757551/200000)
  | 9 => (-846393/200000)
  | 10 => (-816163/200000)
  | 11 => (-334559/100000)
  | _ => 0
def shortNegativeR036Q10U : ℕ → ℚ
  | 0 => (-1687927/1000000)
  | 1 => (-886633/1000000)
  | 2 => (-368713/1000000)
  | 3 => (-190037/1000000)
  | 4 => (-63963/200000)
  | 5 => (-84323/125000)
  | 6 => (-3149/2500)
  | 7 => (-1994547/1000000)
  | 8 => (-2717629/1000000)
  | 9 => (-48076/15625)
  | 10 => (-14851/5000)
  | 11 => (-1207951/500000)
  | _ => 0
private theorem shortNegativeR036Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR036Q10L (0:Fin 12)) (shortNegativeR036Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR036Q10L (1:Fin 12)) (shortNegativeR036Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR036Q10L (2:Fin 12)) (shortNegativeR036Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR036Q10L (3:Fin 12)) (shortNegativeR036Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR036Q10L (4:Fin 12)) (shortNegativeR036Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR036Q10L (5:Fin 12)) (shortNegativeR036Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR036Q10L (6:Fin 12)) (shortNegativeR036Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR036Q10L (7:Fin 12)) (shortNegativeR036Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR036Q10L (8:Fin 12)) (shortNegativeR036Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR036Q10L (9:Fin 12)) (shortNegativeR036Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR036Q10L (10:Fin 12)) (shortNegativeR036Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR036Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR036Q10L (11:Fin 12)) (shortNegativeR036Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR036Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR036Q10P shortNegativeR036Q10F (shortNegativeNodes12 k)).re (shortNegativeR036Q10L k) (shortNegativeR036Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR036Q10Point00
  · exact shortNegativeR036Q10Point01
  · exact shortNegativeR036Q10Point02
  · exact shortNegativeR036Q10Point03
  · exact shortNegativeR036Q10Point04
  · exact shortNegativeR036Q10Point05
  · exact shortNegativeR036Q10Point06
  · exact shortNegativeR036Q10Point07
  · exact shortNegativeR036Q10Point08
  · exact shortNegativeR036Q10Point09
  · exact shortNegativeR036Q10Point10
  · exact shortNegativeR036Q10Point11

theorem shortNegativeR036Q10Bound {t a : ℝ} (tl : ((47/40):ℝ)≤t) (tu : t≤((59/50):ℝ)) (al : ((1192461436458397/1649267441664000):ℝ)≤a) (au : a≤((1205346338346397/1649267441664000):ℝ)) : (((-3164482854585307430050175420975623/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1932825149437282027486058678831623/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR036Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1192461436458397/1649267441664000) (1205346338346397/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR036Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR036Q10F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR036Q10L shortNegativeR036Q10U (-3164482854585307430050175420975623/1298074214633706907132624082305024) (-1932825149437282027486058678831623/1298074214633706907132624082305024) shortNegativeR036Q10Samples (by decide +kernel)

theorem short_original_negative_036 {t a : ℝ} (tb : RealMem negative_036.t t) (ab : RealMem negative_036.a a) : RealMem negative_036.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((117/100):ℝ) ((59/50):ℝ) := by simpa [negative_036,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((117/100):ℝ)<((59/50):ℝ)) tB
  have aB : a∈Icc ((1192461436458397/1649267441664000):ℝ) ((1205346338346397/1649267441664000):ℝ) := by simpa [negative_036,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((1192461436458397/1649267441664000):ℝ)<((1205346338346397/1649267441664000):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR036Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_036,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR036Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_036,RealMem] using v

def shortNegativeR037Q00T := Grid.ofRats (59/50) (119/100)
def shortNegativeR037Q00P : PrimalThetaParameters := ⟨⟨⟨28760192729883377312379,29678063217232480312982,true⟩,⟨0,0,true⟩⟩, ⟨⟨1384045492017146068169422,1388990742633928770177646,true⟩,⟨0,0,true⟩⟩, ⟨(-1029861489602012084710862),(-1019970988368515400176718),true⟩, ⟨4163496044033920942672358,4225904118469017108482934,true⟩⟩
theorem shortNegativeR037Q00P_ok : shortNegativeR037Q00P.encloses (primalThetaParameters shortNegativeR037Q00T (Grid.ofRats (240409661111977/329853488332800) (80422884857059/109951162777600))) := by decide +kernel

def shortNegativeR037Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨474785763213004873988652,478529403876065375085465,true⟩,⟨3054152211949564179238713,3078233912155311695482748,true⟩,⟨⟨494775750791324194987837,499721001408106897044470,true⟩,⟨1099455543764846723413571,1104400794381629425478547,true⟩⟩⟩
  | 1 => ⟨⟨1742151407927859329553,1840612988890916988418,true⟩,⟨474785763213004873988652,478529403876065375085465,true⟩,⟨⟨(-1162666307260665465437018),(-1147830555410454798292961),true⟩,⟨(-363651927115654108995731),(-348816175265443441862670),true⟩⟩⟩
  | 2 => ⟨⟨152077913513107880,173801021425026364,true⟩,⟨1742151407927859329553,1840612988890916988418,true⟩,⟨⟨1019108485530903592936763,1043834738614542225149435,true⟩,⟨(-642893023389701654295190),(-618166770306063022088042),true⟩⟩⟩
  | 3 => ⟨⟨281459607594,437241768854,true⟩,⟨152077913513107880,173801021425026364,true⟩,⟨⟨(-226988239891353921433078),(-192371485574287324134906),true⟩,⟨1173294828151803676482416,1207911582468870273794087,true⟩⟩⟩
  | 4 => ⟨⟨(-34359722766),34359761295,true⟩,⟨281459607594,437241768854,true⟩,⟨⟨(-776259554907507683398548),(-731752299357013121030342),true⟩,⟨(-967228071440430924353573),(-922720815889936361982735),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359722766),34359761295,true⟩,⟨⟨1180243803784816855711946,1234641560568739383100189,true⟩,⟨32666024419710459132064,87063781203632986504515,true⟩⟩⟩
theorem shortNegativeR037Q00F_ok : ∀ n : Fin 6, (shortNegativeR037Q00F n).encloses (FactoredFrequency.build shortNegativeR037Q00T (Grid.ofRats (240409661111977/329853488332800) (80422884857059/109951162777600)) n) := by decide +kernel
def shortNegativeR037Q00L : ℕ → ℚ
  | 0 => (-1166637/500000)
  | 1 => (-1582917/1000000)
  | 2 => (-55539/50000)
  | 3 => (-120081/125000)
  | 4 => (-69301/62500)
  | 5 => (-311799/200000)
  | 6 => (-1110739/500000)
  | 7 => (-597929/200000)
  | 8 => (-3701053/1000000)
  | 9 => (-2067181/500000)
  | 10 => (-4004783/1000000)
  | 11 => (-3309983/1000000)
  | _ => 0
def shortNegativeR037Q00U : ℕ → ℚ
  | 0 => (-347279/200000)
  | 1 => (-95701/100000)
  | 2 => (-88699/200000)
  | 3 => (-4097/15625)
  | 4 => (-382769/1000000)
  | 5 => (-146469/200000)
  | 6 => (-653731/500000)
  | 7 => (-81197/40000)
  | 8 => (-2736777/1000000)
  | 9 => (-773701/250000)
  | 10 => (-3001353/1000000)
  | 11 => (-247393/100000)
  | _ => 0
private theorem shortNegativeR037Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR037Q00L (0:Fin 12)) (shortNegativeR037Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR037Q00L (1:Fin 12)) (shortNegativeR037Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR037Q00L (2:Fin 12)) (shortNegativeR037Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR037Q00L (3:Fin 12)) (shortNegativeR037Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR037Q00L (4:Fin 12)) (shortNegativeR037Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR037Q00L (5:Fin 12)) (shortNegativeR037Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR037Q00L (6:Fin 12)) (shortNegativeR037Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR037Q00L (7:Fin 12)) (shortNegativeR037Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR037Q00L (8:Fin 12)) (shortNegativeR037Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR037Q00L (9:Fin 12)) (shortNegativeR037Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR037Q00L (10:Fin 12)) (shortNegativeR037Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR037Q00L (11:Fin 12)) (shortNegativeR037Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR037Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR037Q00P shortNegativeR037Q00F (shortNegativeNodes12 k)).re (shortNegativeR037Q00L k) (shortNegativeR037Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR037Q00Point00
  · exact shortNegativeR037Q00Point01
  · exact shortNegativeR037Q00Point02
  · exact shortNegativeR037Q00Point03
  · exact shortNegativeR037Q00Point04
  · exact shortNegativeR037Q00Point05
  · exact shortNegativeR037Q00Point06
  · exact shortNegativeR037Q00Point07
  · exact shortNegativeR037Q00Point08
  · exact shortNegativeR037Q00Point09
  · exact shortNegativeR037Q00Point10
  · exact shortNegativeR037Q00Point11

theorem shortNegativeR037Q00Bound {t a : ℝ} (tl : ((59/50):ℝ)≤t) (tu : t≤((119/100):ℝ)) (al : ((240409661111977/329853488332800):ℝ)≤a) (au : a≤((80422884857059/109951162777600):ℝ)) : (((-3186656703240284414177190315337757/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-3964557350351086868317473739984953/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR037Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (240409661111977/329853488332800) (80422884857059/109951162777600)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR037Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR037Q00F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR037Q00L shortNegativeR037Q00U (-3186656703240284414177190315337757/1298074214633706907132624082305024) (-3964557350351086868317473739984953/2596148429267413814265248164610048) shortNegativeR037Q00Samples (by decide +kernel)

def shortNegativeR037Q01T := Grid.ofRats (59/50) (119/100)
def shortNegativeR037Q01P : PrimalThetaParameters := ⟨⟨⟨28760192729883377312379,29678063217232480312982,true⟩,⟨0,0,true⟩⟩, ⟨⟨1388990742633860050696485,1393935993250642752704726,true⟩,⟨0,0,true⟩⟩, ⟨(-1019970988368584119656705),(-1010080487135087435122590),true⟩, ⟨4150708822755531388983863,4212929561208493430450503,true⟩⟩
theorem shortNegativeR037Q01P_ok : shortNegativeR037Q01P.encloses (primalThetaParameters shortNegativeR037Q01T (Grid.ofRats (80422884857059/109951162777600) (242127648030377/329853488332800))) := by decide +kernel

def shortNegativeR037Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨474785763213004873988652,478529403876065375085465,true⟩,⟨3054152211949564179238713,3078233912155311695482748,true⟩,⟨⟨490264038730081489750922,495209289346864191807635,true⟩,⟨1101480370630810792207421,1106425621247593494272568,true⟩⟩⟩
  | 1 => ⟨⟨1742151407927859329553,1840612988890916988418,true⟩,⟨474785763213004873988652,478529403876065375085465,true⟩,⟨⟨(-1158207779380592812346898),(-1143372027530382145202014),true⟩,⟨(-377801778701417584525149),(-362966026851206917390997),true⟩⟩⟩
  | 2 => ⟨⟨152077913513107880,173801021425026364,true⟩,⟨1742151407927859329553,1840612988890916988418,true⟩,⟨⟨1031788123646745388488349,1056514376730384020700769,true⟩,⟨(-621665846099643277529479),(-596939593016004645323039),true⟩⟩⟩
  | 3 => ⟨⟨281459607594,437241768854,true⟩,⟨152077913513107880,173801021425026364,true⟩,⟨⟨(-260989725337491779825371),(-226372971020425182526706),true⟩,⟨1166803542332436155504870,1201420296649502752816480,true⟩⟩⟩
  | 4 => ⟨⟨(-34359722766),34359761295,true⟩,⟨281459607594,437241768854,true⟩,⟨⟨(-740966743848936093645026),(-696459488298441531277067),true⟩,⟨(-994340606452850610681349),(-949833350902356048309900),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359722766),34359761295,true⟩,⟨⟨1176328831467238977193647,1230726588251161504584487,true⟩,⟨86918118291143052431876,141315875075065579807733,true⟩⟩⟩
theorem shortNegativeR037Q01F_ok : ∀ n : Fin 6, (shortNegativeR037Q01F n).encloses (FactoredFrequency.build shortNegativeR037Q01T (Grid.ofRats (80422884857059/109951162777600) (242127648030377/329853488332800)) n) := by decide +kernel
def shortNegativeR037Q01L : ℕ → ℚ
  | 0 => (-2349077/1000000)
  | 1 => (-800433/500000)
  | 2 => (-562137/500000)
  | 3 => (-967867/1000000)
  | 4 => (-554219/500000)
  | 5 => (-310073/200000)
  | 6 => (-1102459/500000)
  | 7 => (-185447/62500)
  | 8 => (-459739/125000)
  | 9 => (-257257/62500)
  | 10 => (-799699/200000)
  | 11 => (-3317219/1000000)
  | _ => 0
def shortNegativeR037Q01U : ℕ → ℚ
  | 0 => (-877627/500000)
  | 1 => (-195657/200000)
  | 2 => (-460967/1000000)
  | 3 => (-17063/62500)
  | 4 => (-24119/62500)
  | 5 => (-181933/250000)
  | 6 => (-1295567/1000000)
  | 7 => (-2012629/1000000)
  | 8 => (-2717517/1000000)
  | 9 => (-308139/100000)
  | 10 => (-599801/200000)
  | 11 => (-621001/250000)
  | _ => 0
private theorem shortNegativeR037Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR037Q01L (0:Fin 12)) (shortNegativeR037Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR037Q01L (1:Fin 12)) (shortNegativeR037Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR037Q01L (2:Fin 12)) (shortNegativeR037Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR037Q01L (3:Fin 12)) (shortNegativeR037Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR037Q01L (4:Fin 12)) (shortNegativeR037Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR037Q01L (5:Fin 12)) (shortNegativeR037Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR037Q01L (6:Fin 12)) (shortNegativeR037Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR037Q01L (7:Fin 12)) (shortNegativeR037Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR037Q01L (8:Fin 12)) (shortNegativeR037Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR037Q01L (9:Fin 12)) (shortNegativeR037Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR037Q01L (10:Fin 12)) (shortNegativeR037Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR037Q01L (11:Fin 12)) (shortNegativeR037Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR037Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR037Q01P shortNegativeR037Q01F (shortNegativeNodes12 k)).re (shortNegativeR037Q01L k) (shortNegativeR037Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR037Q01Point00
  · exact shortNegativeR037Q01Point01
  · exact shortNegativeR037Q01Point02
  · exact shortNegativeR037Q01Point03
  · exact shortNegativeR037Q01Point04
  · exact shortNegativeR037Q01Point05
  · exact shortNegativeR037Q01Point06
  · exact shortNegativeR037Q01Point07
  · exact shortNegativeR037Q01Point08
  · exact shortNegativeR037Q01Point09
  · exact shortNegativeR037Q01Point10
  · exact shortNegativeR037Q01Point11

theorem shortNegativeR037Q01Bound {t a : ℝ} (tl : ((59/50):ℝ)≤t) (tu : t≤((119/100):ℝ)) (al : ((80422884857059/109951162777600):ℝ)≤a) (au : a≤((242127648030377/329853488332800):ℝ)) : (((-3186656703240284414177190315337757/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-3964557350351086868317473739984953/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR037Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (80422884857059/109951162777600) (242127648030377/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR037Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR037Q01F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR037Q01L shortNegativeR037Q01U (-3186656703240284414177190315337757/1298074214633706907132624082305024) (-3964557350351086868317473739984953/2596148429267413814265248164610048) shortNegativeR037Q01Samples (by decide +kernel)

def shortNegativeR037Q02T := Grid.ofRats (59/50) (119/100)
def shortNegativeR037Q02P : PrimalThetaParameters := ⟨⟨⟨28760192729883377312379,29678063217232480312982,true⟩,⟨0,0,true⟩⟩, ⟨⟨1393935993250574033223549,1398881243867356735231805,true⟩,⟨0,0,true⟩⟩, ⟨(-1010080487135156154602546),(-1000189985901659470068462),true⟩, ⟨4138109582110188796844979,4200145953862342996962033,true⟩⟩
theorem shortNegativeR037Q02P_ok : shortNegativeR037Q02P.encloses (primalThetaParameters shortNegativeR037Q02T (Grid.ofRats (242127648030377/329853488332800) (242986641489577/329853488332800))) := by decide +kernel

def shortNegativeR037Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨474785763213004873988652,478529403876065375085465,true⟩,⟨3054152211949564179238713,3078233912155311695482748,true⟩,⟨⟨485744081651398477758052,490689332268181179814700,true⟩,⟨1103486724928425275139968,1108431975545207977205149,true⟩⟩⟩
  | 1 => ⟨⟨1742151407927859329553,1840612988890916988418,true⟩,⟨474785763213004873988652,478529403876065375085465,true⟩,⟨⟨(-1153575946773997700218360),(-1138740194923787033073186),true⟩,⟨(-391895851833802013101715),(-377060099983591345967016),true⟩⟩⟩
  | 2 => ⟨⟨152077913513107880,173801021425026364,true⟩,⟨1742151407927859329553,1840612988890916988418,true⟩,⟨⟨1044030978903325464516102,1068757231986964096728035,true⟩,⟨(-600183789084108015433499),(-575457536000469383228023),true⟩⟩⟩
  | 3 => ⟨⟨281459607594,437241768854,true⟩,⟨152077913513107880,173801021425026364,true⟩,⟨⟨(-294791424347479428031760),(-260174670030412830732642),true⟩,⟨1159341441544397541076256,1193958195861464138387746,true⟩⟩⟩
  | 4 => ⟨⟨(-34359722766),34359761295,true⟩,⟨281459607594,437241768854,true⟩,⟨⟨(-704699910622350732713646),(-660192655071856170345756),true⟩,⟨(-1020135739228836868758874),(-975628483678342306386636),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359722766),34359761295,true⟩,⟨⟨1169977476536354204600134,1224375233320276731992602,true⟩,⟨140939197401283574875336,195336954185206102253635,true⟩⟩⟩
theorem shortNegativeR037Q02F_ok : ∀ n : Fin 6, (shortNegativeR037Q02F n).encloses (FactoredFrequency.build shortNegativeR037Q02T (Grid.ofRats (242127648030377/329853488332800) (242986641489577/329853488332800)) n) := by decide +kernel
def shortNegativeR037Q02L : ℕ → ℚ
  | 0 => (-118237/50000)
  | 1 => (-809379/500000)
  | 2 => (-1137809/1000000)
  | 3 => (-487589/500000)
  | 4 => (-1108187/1000000)
  | 5 => (-1541893/1000000)
  | 6 => (-437707/200000)
  | 7 => (-1472413/500000)
  | 8 => (-3654863/1000000)
  | 9 => (-4097829/1000000)
  | 10 => (-3992047/1000000)
  | 11 => (-1662127/500000)
  | _ => 0
def shortNegativeR037Q02U : ℕ → ℚ
  | 0 => (-221747/125000)
  | 1 => (-1999/2000)
  | 2 => (-119617/250000)
  | 3 => (-283897/1000000)
  | 4 => (-194583/500000)
  | 5 => (-723279/1000000)
  | 6 => (-320963/250000)
  | 7 => (-1995503/1000000)
  | 8 => (-269837/100000)
  | 9 => (-1533991/500000)
  | 10 => (-2996549/1000000)
  | 11 => (-623479/250000)
  | _ => 0
private theorem shortNegativeR037Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR037Q02L (0:Fin 12)) (shortNegativeR037Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR037Q02L (1:Fin 12)) (shortNegativeR037Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR037Q02L (2:Fin 12)) (shortNegativeR037Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR037Q02L (3:Fin 12)) (shortNegativeR037Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR037Q02L (4:Fin 12)) (shortNegativeR037Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR037Q02L (5:Fin 12)) (shortNegativeR037Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR037Q02L (6:Fin 12)) (shortNegativeR037Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR037Q02L (7:Fin 12)) (shortNegativeR037Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR037Q02L (8:Fin 12)) (shortNegativeR037Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR037Q02L (9:Fin 12)) (shortNegativeR037Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR037Q02L (10:Fin 12)) (shortNegativeR037Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR037Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR037Q02L (11:Fin 12)) (shortNegativeR037Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR037Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR037Q02P shortNegativeR037Q02F (shortNegativeNodes12 k)).re (shortNegativeR037Q02L k) (shortNegativeR037Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR037Q02Point00
  · exact shortNegativeR037Q02Point01
  · exact shortNegativeR037Q02Point02
  · exact shortNegativeR037Q02Point03
  · exact shortNegativeR037Q02Point04
  · exact shortNegativeR037Q02Point05
  · exact shortNegativeR037Q02Point06
  · exact shortNegativeR037Q02Point07
  · exact shortNegativeR037Q02Point08
  · exact shortNegativeR037Q02Point09
  · exact shortNegativeR037Q02Point10
  · exact shortNegativeR037Q02Point11

theorem shortNegativeR037Q02Bound {t a : ℝ} (tl : ((59/50):ℝ)≤t) (tu : t≤((119/100):ℝ)) (al : ((242127648030377/329853488332800):ℝ)≤a) (au : a≤((242986641489577/329853488332800):ℝ)) : (((-3186656703240284414177190315337757/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-3964557350351086868317473739984953/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR037Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (242127648030377/329853488332800) (242986641489577/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR037Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR037Q02F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR037Q02L shortNegativeR037Q02U (-3186656703240284414177190315337757/1298074214633706907132624082305024) (-3964557350351086868317473739984953/2596148429267413814265248164610048) shortNegativeR037Q02Samples (by decide +kernel)

theorem short_original_negative_037 {t a : ℝ} (tb : RealMem negative_037.t t) (ab : RealMem negative_037.a a) : RealMem negative_037.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((59/50):ℝ) ((119/100):ℝ) := by simpa [negative_037,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((59/50):ℝ)<((119/100):ℝ)) tB
  have aB : a∈Icc ((240409661111977/329853488332800):ℝ) ((242986641489577/329853488332800):ℝ) := by simpa [negative_037,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((240409661111977/329853488332800):ℝ)<((242986641489577/329853488332800):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR037Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_037,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR037Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_037,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR037Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_037,RealMem] using v

def shortNegativeR038Q00T := Grid.ofRats (119/100) (6/5)
def shortNegativeR038Q00P : PrimalThetaParameters := ⟨⟨⟨27870709749740997219117,28760192729952096789587,true⟩,⟨0,0,true⟩⟩, ⟨⟨1395353923812661135316221,1400299174429443837324480,true⟩,⟨0,0,true⟩⟩, ⟨(-1007244626010981950417193),(-997354124777485265883121),true⟩, ⟨4115496217963874564146220,4176457831527765900924593,true⟩⟩
theorem shortNegativeR038Q00P_ok : shortNegativeR038Q00P.encloses (primalThetaParameters shortNegativeR038Q00T (Grid.ofRats (403956572586071/549755813888000) (1216164685054213/1649267441664000))) := by decide +kernel

def shortNegativeR038Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨471071409873425377968809,474785763213073593482964,true⟩,⟨3078233912155242975893074,3102505494280603790217243,true⟩,⟨⟨484446583370589620744663,489391833987372322801227,true⟩,⟨1104058585977733148810126,1109003836594515850875251,true⟩⟩⟩
  | 1 => ⟨⟨1648956921730182460863,1742151407996578806386,true⟩,⟨471071409873425377968809,474785763213073593482964,true⟩,⟨⟨(-1152216009350999044639088),(-1137380257500788377493848),true⟩,⟨(-395926397112855575236227),(-381090645262644908101387),true⟩⟩⟩
  | 2 => ⟨⟨133069993720874691,152077982232584617,true⟩,⟨1648956921730182460863,1742151407996578806386,true⟩,⟨⟨1047460022949409889406895,1072186276033048521618897,true⟩,⟨(-593978574353682846585106),(-569252321270044214379691),true⟩⟩⟩
  | 3 => ⟨⟨213211142775,350179084331,true⟩,⟨133069993720874691,152077982232584617,true⟩,⟨⟨(-304442485429955590637248),(-269825731112888993338279),true⟩,⟨1157023620701559951868398,1191640375018626549179576,true⟩⟩⟩
  | 4 => ⟨⟨(-34359727750),34359753971,true⟩,⟨213211142775,350179084331,true⟩,⟨⟨(-694128478984603391661788),(-649621223434108829294347),true⟩,⟨(-1027283886843753390259334),(-982776631293258827887308),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359727750),34359753971,true⟩,⟨⟨1167708628011132839973227,1222106384795055367366382,true⟩,⟨156370423160456649961968,210768179944379177341203,true⟩⟩⟩
theorem shortNegativeR038Q00F_ok : ∀ n : Fin 6, (shortNegativeR038Q00F n).encloses (FactoredFrequency.build shortNegativeR038Q00T (Grid.ofRats (403956572586071/549755813888000) (1216164685054213/1649267441664000)) n) := by decide +kernel
def shortNegativeR038Q00L : ℕ → ℚ
  | 0 => (-74961/31250)
  | 1 => (-167541/100000)
  | 2 => (-1202663/1000000)
  | 3 => (-1040353/1000000)
  | 4 => (-1167131/1000000)
  | 5 => (-317757/200000)
  | 6 => (-2217609/1000000)
  | 7 => (-2950889/1000000)
  | 8 => (-3639887/1000000)
  | 9 => (-813447/200000)
  | 10 => (-1983477/500000)
  | 11 => (-3325479/1000000)
  | _ => 0
def shortNegativeR038Q00U : ℕ → ℚ
  | 0 => (-1811313/1000000)
  | 1 => (-211793/200000)
  | 2 => (-546719/1000000)
  | 3 => (-87747/250000)
  | 4 => (-89947/200000)
  | 5 => (-193399/250000)
  | 6 => (-1319131/1000000)
  | 7 => (-1005489/500000)
  | 8 => (-3363/1250)
  | 9 => (-762293/250000)
  | 10 => (-1491819/500000)
  | 11 => (-2503519/1000000)
  | _ => 0
private theorem shortNegativeR038Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR038Q00L (0:Fin 12)) (shortNegativeR038Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR038Q00L (1:Fin 12)) (shortNegativeR038Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR038Q00L (2:Fin 12)) (shortNegativeR038Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR038Q00L (3:Fin 12)) (shortNegativeR038Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR038Q00L (4:Fin 12)) (shortNegativeR038Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR038Q00L (5:Fin 12)) (shortNegativeR038Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR038Q00L (6:Fin 12)) (shortNegativeR038Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR038Q00L (7:Fin 12)) (shortNegativeR038Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR038Q00L (8:Fin 12)) (shortNegativeR038Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR038Q00L (9:Fin 12)) (shortNegativeR038Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR038Q00L (10:Fin 12)) (shortNegativeR038Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR038Q00L (11:Fin 12)) (shortNegativeR038Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR038Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR038Q00P shortNegativeR038Q00F (shortNegativeNodes12 k)).re (shortNegativeR038Q00L k) (shortNegativeR038Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR038Q00Point00
  · exact shortNegativeR038Q00Point01
  · exact shortNegativeR038Q00Point02
  · exact shortNegativeR038Q00Point03
  · exact shortNegativeR038Q00Point04
  · exact shortNegativeR038Q00Point05
  · exact shortNegativeR038Q00Point06
  · exact shortNegativeR038Q00Point07
  · exact shortNegativeR038Q00Point08
  · exact shortNegativeR038Q00Point09
  · exact shortNegativeR038Q00Point10
  · exact shortNegativeR038Q00Point11

theorem shortNegativeR038Q00Bound {t a : ℝ} (tl : ((119/100):ℝ)≤t) (tu : t≤((6/5):ℝ)) (al : ((403956572586071/549755813888000):ℝ)≤a) (au : a≤((1216164685054213/1649267441664000):ℝ)) : (((-3206711777523596625803299229006235/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2029088992103739602965263191898523/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR038Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (403956572586071/549755813888000) (1216164685054213/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR038Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR038Q00F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR038Q00L shortNegativeR038Q00U (-3206711777523596625803299229006235/1298074214633706907132624082305024) (-2029088992103739602965263191898523/1298074214633706907132624082305024) shortNegativeR038Q00Samples (by decide +kernel)

def shortNegativeR038Q01T := Grid.ofRats (119/100) (6/5)
def shortNegativeR038Q01P : PrimalThetaParameters := ⟨⟨⟨27870709749740997219117,28760192729952096789587,true⟩,⟨0,0,true⟩⟩, ⟨⟨1400299174429375117843283,1405244425046157819851560,true⟩,⟨0,0,true⟩⟩, ⟨(-997354124777553985363037),(-987463623544057300828993),true⟩, ⟨4103118370857126767391143,4163899034242832450909750,true⟩⟩
theorem shortNegativeR038Q01P_ok : shortNegativeR038Q01P.encloses (primalThetaParameters shortNegativeR038Q01T (Grid.ofRats (1216164685054213/1649267441664000) (1220459652350213/1649267441664000))) := by decide +kernel

def shortNegativeR038Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨471071409873425377968809,474785763213073593482964,true⟩,⟨3078233912155242975893074,3102505494280603790217243,true⟩,⟨⟨479916128505891990637924,484861379122674692694809,true⟩,⟨1106041121798249477111683,1110986372415032179177235,true⟩⟩⟩
  | 1 => ⟨⟨1648956921730182460863,1742151407996578806386,true⟩,⟨471071409873425377968809,474785763213073593482964,true⟩,⟨⟨(-1147362210964917404210506),(-1132526459114706737064901),true⟩,⟨(-409945577259490026404783),(-395109825409279359269318),true⟩⟩⟩
  | 2 => ⟨⟨133069993720874691,152077982232584617,true⟩,⟨1648956921730182460863,1742151407996578806386,true⟩,⟨⟨1059133349896248651426384,1083859602979887283637870,true⟩,⟨(-572181792103899136876941),(-547455539020260504672503),true⟩⟩⟩
  | 3 => ⟨⟨213211142775,350179084331,true⟩,⟨133069993720874691,152077982232584617,true⟩,⟨⟨(-337946368663992016482740),(-303329614346925419182664),true⟩,⟨1148321459339421270285609,1182938213656487867597313,true⟩⟩⟩
  | 4 => ⟨⟨(-34359727750),34359753971,true⟩,⟨213211142775,350179084331,true⟩,⟨⟨(-656680833422377417293157),(-612173577871882854924689),true⟩,⟨(-1051332710288188540971070),(-1006825454737693978597169),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359727750),34359753971,true⟩,⟨⟨1158241923411174889193593,1212639680195097416588576,true⟩,⟨209933453337055789317241,264331210120978316699183,true⟩⟩⟩
theorem shortNegativeR038Q01F_ok : ∀ n : Fin 6, (shortNegativeR038Q01F n).encloses (FactoredFrequency.build shortNegativeR038Q01T (Grid.ofRats (1216164685054213/1649267441664000) (1220459652350213/1649267441664000)) n) := by decide +kernel
def shortNegativeR038Q01L : ℕ → ℚ
  | 0 => (-482667/200000)
  | 1 => (-84619/50000)
  | 2 => (-1215619/1000000)
  | 3 => (-1047349/1000000)
  | 4 => (-291697/250000)
  | 5 => (-1580423/1000000)
  | 6 => (-2201543/1000000)
  | 7 => (-732261/250000)
  | 8 => (-1808651/500000)
  | 9 => (-4049263/1000000)
  | 10 => (-158403/40000)
  | 11 => (-666313/200000)
  | _ => 0
def shortNegativeR038Q01U : ℕ → ℚ
  | 0 => (-1828987/1000000)
  | 1 => (-26961/25000)
  | 2 => (-563663/1000000)
  | 3 => (-45203/125000)
  | 4 => (-452973/1000000)
  | 5 => (-384657/500000)
  | 6 => (-326943/250000)
  | 7 => (-398869/200000)
  | 8 => (-1335867/500000)
  | 9 => (-3035819/1000000)
  | 10 => (-1490419/500000)
  | 11 => (-314073/125000)
  | _ => 0
private theorem shortNegativeR038Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR038Q01L (0:Fin 12)) (shortNegativeR038Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR038Q01L (1:Fin 12)) (shortNegativeR038Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR038Q01L (2:Fin 12)) (shortNegativeR038Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR038Q01L (3:Fin 12)) (shortNegativeR038Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR038Q01L (4:Fin 12)) (shortNegativeR038Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR038Q01L (5:Fin 12)) (shortNegativeR038Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR038Q01L (6:Fin 12)) (shortNegativeR038Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR038Q01L (7:Fin 12)) (shortNegativeR038Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR038Q01L (8:Fin 12)) (shortNegativeR038Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR038Q01L (9:Fin 12)) (shortNegativeR038Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR038Q01L (10:Fin 12)) (shortNegativeR038Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR038Q01L (11:Fin 12)) (shortNegativeR038Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR038Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR038Q01P shortNegativeR038Q01F (shortNegativeNodes12 k)).re (shortNegativeR038Q01L k) (shortNegativeR038Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR038Q01Point00
  · exact shortNegativeR038Q01Point01
  · exact shortNegativeR038Q01Point02
  · exact shortNegativeR038Q01Point03
  · exact shortNegativeR038Q01Point04
  · exact shortNegativeR038Q01Point05
  · exact shortNegativeR038Q01Point06
  · exact shortNegativeR038Q01Point07
  · exact shortNegativeR038Q01Point08
  · exact shortNegativeR038Q01Point09
  · exact shortNegativeR038Q01Point10
  · exact shortNegativeR038Q01Point11

theorem shortNegativeR038Q01Bound {t a : ℝ} (tl : ((119/100):ℝ)≤t) (tu : t≤((6/5):ℝ)) (al : ((1216164685054213/1649267441664000):ℝ)≤a) (au : a≤((1220459652350213/1649267441664000):ℝ)) : (((-3206711777523596625803299229006235/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2029088992103739602965263191898523/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR038Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1216164685054213/1649267441664000) (1220459652350213/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR038Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR038Q01F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR038Q01L shortNegativeR038Q01U (-3206711777523596625803299229006235/1298074214633706907132624082305024) (-2029088992103739602965263191898523/1298074214633706907132624082305024) shortNegativeR038Q01Samples (by decide +kernel)

def shortNegativeR038Q02T := Grid.ofRats (119/100) (6/5)
def shortNegativeR038Q02P : PrimalThetaParameters := ⟨⟨⟨27870709749740997219117,28760192729952096789587,true⟩,⟨0,0,true⟩⟩, ⟨⟨1405244425046089100370347,1410189675662871802378640,true⟩,⟨0,0,true⟩⟩, ⟨(-987463623544126020308877),(-977573122310629335774865),true⟩, ⟨4090923536334624980155464,4151526114436592765275528,true⟩⟩
theorem shortNegativeR038Q02P_ok : shortNegativeR038Q02P.encloses (primalThetaParameters shortNegativeR038Q02T (Grid.ofRats (1220459652350213/1649267441664000) (408251539882071/549755813888000))) := by decide +kernel

def shortNegativeR038Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨471071409873425377968809,474785763213073593482964,true⟩,⟨3078233912155242975893074,3102505494280603790217243,true⟩,⟨⟨475377601776487544111858,480322852393270246168841,true⟩,⟨1108005108734859329116979,1112950359351642031182693,true⟩⟩⟩
  | 1 => ⟨⟨1648956921730182460863,1742151407996578806386,true⟩,⟨471071409873425377968809,474785763213073593482964,true⟩,⟨⟨(-1142336741155023569569734),(-1127500989304812902423558),true⟩,⟨(-423904138214916768196256),(-409068386364706101059958),true⟩⟩⟩
  | 2 => ⟨⟨133069993720874691,152077982232584617,true⟩,⟨1648956921730182460863,1742151407996578806386,true⟩,⟨⟨1070358455098792266347025,1095084708182430898558126,true⟩,⟨(-550150829990452832804140),(-525424576906814200600552),true⟩⟩⟩
  | 3 => ⟨⟨213211142775,350179084331,true⟩,⟨133069993720874691,152077982232584617,true⟩,⟨⟨(-371187371205287887418102),(-336570616888221290117305),true⟩,⟨1138663635869187000280685,1173280390186253597592521,true⟩⟩⟩
  | 4 => ⟨⟨(-34359727750),34359753971,true⟩,⟨213211142775,350179084331,true⟩,⟨⟨(-618373392555917731050270),(-573866137005423168682795),true⟩,⟨(-1073986894040387842430773),(-1029479638489893280057025),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359727750),34359753971,true⟩,⟨⟨1146375450750242562097728,1200773207534165089495192,true⟩,⟨263016440482368935408839,317414197266291462794138,true⟩⟩⟩
theorem shortNegativeR038Q02F_ok : ∀ n : Fin 6, (shortNegativeR038Q02F n).encloses (FactoredFrequency.build shortNegativeR038Q02T (Grid.ofRats (1220459652350213/1649267441664000) (408251539882071/549755813888000)) n) := by decide +kernel
def shortNegativeR038Q02L : ℕ → ℚ
  | 0 => (-303473/125000)
  | 1 => (-106831/62500)
  | 2 => (-245723/200000)
  | 3 => (-263609/250000)
  | 4 => (-291643/250000)
  | 5 => (-1572217/1000000)
  | 6 => (-2185651/1000000)
  | 7 => (-726841/250000)
  | 8 => (-359481/100000)
  | 9 => (-1007833/250000)
  | 10 => (-3953049/1000000)
  | 11 => (-3337461/1000000)
  | _ => 0
def shortNegativeR038Q02U : ℕ → ℚ
  | 0 => (-1846529/1000000)
  | 1 => (-548849/500000)
  | 2 => (-290317/500000)
  | 3 => (-372347/1000000)
  | 4 => (-28521/62500)
  | 5 => (-191297/250000)
  | 6 => (-129659/100000)
  | 7 => (-1977877/1000000)
  | 8 => (-2653181/1000000)
  | 9 => (-1511213/500000)
  | 10 => (-148897/50000)
  | 11 => (-504299/200000)
  | _ => 0
private theorem shortNegativeR038Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR038Q02L (0:Fin 12)) (shortNegativeR038Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR038Q02L (1:Fin 12)) (shortNegativeR038Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR038Q02L (2:Fin 12)) (shortNegativeR038Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR038Q02L (3:Fin 12)) (shortNegativeR038Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR038Q02L (4:Fin 12)) (shortNegativeR038Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR038Q02L (5:Fin 12)) (shortNegativeR038Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR038Q02L (6:Fin 12)) (shortNegativeR038Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR038Q02L (7:Fin 12)) (shortNegativeR038Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR038Q02L (8:Fin 12)) (shortNegativeR038Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR038Q02L (9:Fin 12)) (shortNegativeR038Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR038Q02L (10:Fin 12)) (shortNegativeR038Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR038Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR038Q02L (11:Fin 12)) (shortNegativeR038Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR038Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR038Q02P shortNegativeR038Q02F (shortNegativeNodes12 k)).re (shortNegativeR038Q02L k) (shortNegativeR038Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR038Q02Point00
  · exact shortNegativeR038Q02Point01
  · exact shortNegativeR038Q02Point02
  · exact shortNegativeR038Q02Point03
  · exact shortNegativeR038Q02Point04
  · exact shortNegativeR038Q02Point05
  · exact shortNegativeR038Q02Point06
  · exact shortNegativeR038Q02Point07
  · exact shortNegativeR038Q02Point08
  · exact shortNegativeR038Q02Point09
  · exact shortNegativeR038Q02Point10
  · exact shortNegativeR038Q02Point11

theorem shortNegativeR038Q02Bound {t a : ℝ} (tl : ((119/100):ℝ)≤t) (tu : t≤((6/5):ℝ)) (al : ((1220459652350213/1649267441664000):ℝ)≤a) (au : a≤((408251539882071/549755813888000):ℝ)) : (((-3206711777523596625803299229006235/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2029088992103739602965263191898523/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR038Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1220459652350213/1649267441664000) (408251539882071/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR038Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR038Q02F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR038Q02L shortNegativeR038Q02U (-3206711777523596625803299229006235/1298074214633706907132624082305024) (-2029088992103739602965263191898523/1298074214633706907132624082305024) shortNegativeR038Q02Samples (by decide +kernel)

theorem short_original_negative_038 {t a : ℝ} (tb : RealMem negative_038.t t) (ab : RealMem negative_038.a a) : RealMem negative_038.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((119/100):ℝ) ((6/5):ℝ) := by simpa [negative_038,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((119/100):ℝ)<((6/5):ℝ)) tB
  have aB : a∈Icc ((403956572586071/549755813888000):ℝ) ((408251539882071/549755813888000):ℝ) := by simpa [negative_038,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((403956572586071/549755813888000):ℝ)<((408251539882071/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR038Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_038,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR038Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_038,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR038Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_038,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_036
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_037
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_038
