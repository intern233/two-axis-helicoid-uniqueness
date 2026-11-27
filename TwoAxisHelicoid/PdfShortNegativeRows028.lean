import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip024

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR028Q00T := Grid.ofRats (109/100) (11/10)
def shortNegativeR028Q00P : PrimalThetaParameters := ⟨⟨⟨38158005291212763392007,39375803351232961830587,true⟩,⟨0,0,true⟩⟩, ⟨⟨1292895901798827742626927,1300313777723967435898401,true⟩,⟨0,0,true⟩⟩, ⟨(-1212160670038648735796432),(-1197324918188438068734643),true⟩, ⟨4618629325082508993271655,4721417033109717261157555,true⟩⟩
theorem shortNegativeR028Q00P_ok : shortNegativeR028Q00P.encloses (primalThetaParameters shortNegativeR028Q00T (Grid.ofRats (1122884570620277/1649267441664000) (1129327021564277/1649267441664000))) := by decide +kernel

def shortNegativeR028Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨509560970173516715721002,513578810041625645747725,true⟩,⟨2845720284317275678730715,2868158518563830410918664,true⟩,⟨⟨574044632650416055468029,581462508575555748787643,true⟩,⟨1058224416337429730857632,1065642292262569424183923,true⟩⟩⟩
  | 1 => ⟨⟨2857427183430916036842,3018921067721522013498,true⟩,⟨509560970173516715721002,513578810041625645747725,true⟩,⟨⟨(-1216564174689838693792637),(-1194310546914557052864462),true⟩,⟨(-102900483930495401256837),(-80646856155213760343987),true⟩⟩⟩
  | 2 => ⟨⟨505754981847790963,577997845742516338,true⟩,⟨2857427183430916036842,3018921067721522013498,true⟩,⟨⟨713314574439571895344609,750403954064995483876862,true⟩,⟨(-980773173416792655788450),(-943683793791369067253038),true⟩⟩⟩
  | 3 => ⟨⟨2791113749881,3638738350962,true⟩,⟨505754981847790963,577997845742516338,true⟩,⟨⟨384367295540748313212720,436292427016313849348141,true⟩,⟨1111196632560346620714452,1163121764035912156859875,true⟩⟩⟩
  | 4 => ⟨⟨(-34359240140),34360470458,true⟩,⟨2791113749881,3638738350962,true⟩,⟨⟨(-1211030810731431849317072),(-1144269927405724365588676),true⟩,⟨(-306585942272824422780194),(-239825058947116939064247),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359240140),34360470458,true⟩,⟨⟨828296276079656038246760,909892911255505469552875,true⟩,⟨(-881141238417680751951121),(-799544603241831320645400),true⟩⟩⟩
theorem shortNegativeR028Q00F_ok : ∀ n : Fin 6, (shortNegativeR028Q00F n).encloses (FactoredFrequency.build shortNegativeR028Q00T (Grid.ofRats (1122884570620277/1649267441664000) (1129327021564277/1649267441664000)) n) := by decide +kernel
def shortNegativeR028Q00L : ℕ → ℚ
  | 0 => (-1514631/1000000)
  | 1 => (-9076/15625)
  | 2 => (-7999/50000)
  | 3 => (-87773/500000)
  | 4 => (-541211/1000000)
  | 5 => (-1278499/1000000)
  | 6 => (-2283419/1000000)
  | 7 => (-3416811/1000000)
  | 8 => (-4366809/1000000)
  | 9 => (-4837643/1000000)
  | 10 => (-4335329/1000000)
  | 11 => (-3062407/1000000)
  | _ => 0
def shortNegativeR028Q00U : ℕ → ℚ
  | 0 => (-779339/1000000)
  | 1 => (1303/6250)
  | 2 => (67649/100000)
  | 3 => (340543/500000)
  | 4 => (323089/1000000)
  | 5 => (-34543/125000)
  | 6 => (-226941/200000)
  | 7 => (-270211/125000)
  | 8 => (-1553307/500000)
  | 9 => (-434079/125000)
  | 10 => (-2986051/1000000)
  | 11 => (-1871083/1000000)
  | _ => 0
private theorem shortNegativeR028Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR028Q00L (0:Fin 12)) (shortNegativeR028Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR028Q00L (1:Fin 12)) (shortNegativeR028Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR028Q00L (2:Fin 12)) (shortNegativeR028Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR028Q00L (3:Fin 12)) (shortNegativeR028Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR028Q00L (4:Fin 12)) (shortNegativeR028Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR028Q00L (5:Fin 12)) (shortNegativeR028Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR028Q00L (6:Fin 12)) (shortNegativeR028Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR028Q00L (7:Fin 12)) (shortNegativeR028Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR028Q00L (8:Fin 12)) (shortNegativeR028Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR028Q00L (9:Fin 12)) (shortNegativeR028Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR028Q00L (10:Fin 12)) (shortNegativeR028Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR028Q00L (11:Fin 12)) (shortNegativeR028Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR028Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR028Q00P shortNegativeR028Q00F (shortNegativeNodes12 k)).re (shortNegativeR028Q00L k) (shortNegativeR028Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR028Q00Point00
  · exact shortNegativeR028Q00Point01
  · exact shortNegativeR028Q00Point02
  · exact shortNegativeR028Q00Point03
  · exact shortNegativeR028Q00Point04
  · exact shortNegativeR028Q00Point05
  · exact shortNegativeR028Q00Point06
  · exact shortNegativeR028Q00Point07
  · exact shortNegativeR028Q00Point08
  · exact shortNegativeR028Q00Point09
  · exact shortNegativeR028Q00Point10
  · exact shortNegativeR028Q00Point11

theorem shortNegativeR028Q00Bound {t a : ℝ} (tl : ((109/100):ℝ)≤t) (tu : t≤((11/10):ℝ)) (al : ((1122884570620277/1649267441664000):ℝ)≤a) (au : a≤((1129327021564277/1649267441664000):ℝ)) : (((-1449684918013385255022663137575341/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-718582415340510612194172522807725/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR028Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1122884570620277/1649267441664000) (1129327021564277/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR028Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR028Q00F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR028Q00L shortNegativeR028Q00U (-1449684918013385255022663137575341/649037107316853453566312041152512) (-718582415340510612194172522807725/649037107316853453566312041152512) shortNegativeR028Q00Samples (by decide +kernel)

def shortNegativeR028Q01T := Grid.ofRats (109/100) (11/10)
def shortNegativeR028Q01P : PrimalThetaParameters := ⟨⟨⟨38158005291212763392007,39375803351232961830587,true⟩,⟨0,0,true⟩⟩, ⟨⟨1300313777723898716417523,1307731653649038409689020,true⟩,⟨0,0,true⟩⟩, ⟨(-1197324918188506788215194),(-1182489166338296121153452),true⟩, ⟨4594201858852606842208593,4696417179310712758809565,true⟩⟩
theorem shortNegativeR028Q01P_ok : shortNegativeR028Q01P.encloses (primalThetaParameters shortNegativeR028Q01T (Grid.ofRats (1129327021564277/1649267441664000) (1135769472508277/1649267441664000))) := by decide +kernel

def shortNegativeR028Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨509560970173516715721002,513578810041625645747725,true⟩,⟨2845720284317275678730715,2868158518563830410918664,true⟩,⟨⟨567517856035648597152376,574935731960788290472138,true⟩,⟨1061749455007057019123176,1069167330932196712449756,true⟩⟩⟩
  | 1 => ⟨⟨2857427183430916036842,3018921067721522013498,true⟩,⟨509560970173516715721002,513578810041625645747725,true⟩,⟨⟨(-1214670698499980956316748),(-1192417070724699315387588),true⟩,⟨(-125073095718778298621115),(-102819467943496657706950),true⟩⟩⟩
  | 2 => ⟨⟨505754981847790963,577997845742516338,true⟩,⟨2857427183430916036842,3018921067721522013498,true⟩,⟨⟨742486343623660639726997,779575723249084228259291,true⟩,⟨(-957870726648522015483669),(-920781347023098426948932),true⟩⟩⟩
  | 3 => ⟨⟨2791113749881,3638738350962,true⟩,⟨505754981847790963,577997845742516338,true⟩,⟨⟨335161225864973853225723,387086357340539389361564,true⟩,⟨1127766711202588423345103,1179691842678153959491853,true⟩⟩⟩
  | 4 => ⟨⟨(-34359240140),34360470458,true⟩,⟨2791113749881,3638738350962,true⟩,⟨⟨(-1194155933267110408372666),(-1127395049941402924642365),true⟩,⟨(-371170162379454559100553),(-304409279053747075381576),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359240140),34360470458,true⟩,⟨⟨882993425968318164018282,964590061144167595323716,true⟩,⟨(-820612687722394416557549),(-739016052546544985254101),true⟩⟩⟩
theorem shortNegativeR028Q01F_ok : ∀ n : Fin 6, (shortNegativeR028Q01F n).encloses (FactoredFrequency.build shortNegativeR028Q01T (Grid.ofRats (1129327021564277/1649267441664000) (1135769472508277/1649267441664000)) n) := by decide +kernel
def shortNegativeR028Q01L : ℕ → ℚ
  | 0 => (-1558373/1000000)
  | 1 => (-619949/1000000)
  | 2 => (-23443/125000)
  | 3 => (-1891/10000)
  | 4 => (-540137/1000000)
  | 5 => (-19717/15625)
  | 6 => (-2251551/1000000)
  | 7 => (-3373599/1000000)
  | 8 => (-4323911/1000000)
  | 9 => (-962067/200000)
  | 10 => (-2169191/500000)
  | 11 => (-770183/250000)
  | _ => 0
def shortNegativeR028Q01U : ℕ → ℚ
  | 0 => (-33157/40000)
  | 1 => (80821/500000)
  | 2 => (64251/100000)
  | 3 => (662397/1000000)
  | 4 => (159871/500000)
  | 5 => (-265007/1000000)
  | 6 => (-221887/200000)
  | 7 => (-1063117/500000)
  | 8 => (-47984/15625)
  | 9 => (-1725449/500000)
  | 10 => (-3006601/1000000)
  | 11 => (-479599/250000)
  | _ => 0
private theorem shortNegativeR028Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR028Q01L (0:Fin 12)) (shortNegativeR028Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR028Q01L (1:Fin 12)) (shortNegativeR028Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR028Q01L (2:Fin 12)) (shortNegativeR028Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR028Q01L (3:Fin 12)) (shortNegativeR028Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR028Q01L (4:Fin 12)) (shortNegativeR028Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR028Q01L (5:Fin 12)) (shortNegativeR028Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR028Q01L (6:Fin 12)) (shortNegativeR028Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR028Q01L (7:Fin 12)) (shortNegativeR028Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR028Q01L (8:Fin 12)) (shortNegativeR028Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR028Q01L (9:Fin 12)) (shortNegativeR028Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR028Q01L (10:Fin 12)) (shortNegativeR028Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR028Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR028Q01L (11:Fin 12)) (shortNegativeR028Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR028Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR028Q01P shortNegativeR028Q01F (shortNegativeNodes12 k)).re (shortNegativeR028Q01L k) (shortNegativeR028Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR028Q01Point00
  · exact shortNegativeR028Q01Point01
  · exact shortNegativeR028Q01Point02
  · exact shortNegativeR028Q01Point03
  · exact shortNegativeR028Q01Point04
  · exact shortNegativeR028Q01Point05
  · exact shortNegativeR028Q01Point06
  · exact shortNegativeR028Q01Point07
  · exact shortNegativeR028Q01Point08
  · exact shortNegativeR028Q01Point09
  · exact shortNegativeR028Q01Point10
  · exact shortNegativeR028Q01Point11

theorem shortNegativeR028Q01Bound {t a : ℝ} (tl : ((109/100):ℝ)≤t) (tu : t≤((11/10):ℝ)) (al : ((1129327021564277/1649267441664000):ℝ)≤a) (au : a≤((1135769472508277/1649267441664000):ℝ)) : (((-1449684918013385255022663137575341/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-718582415340510612194172522807725/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR028Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1129327021564277/1649267441664000) (1135769472508277/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR028Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR028Q01F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR028Q01L shortNegativeR028Q01U (-1449684918013385255022663137575341/649037107316853453566312041152512) (-718582415340510612194172522807725/649037107316853453566312041152512) shortNegativeR028Q01Samples (by decide +kernel)

theorem short_original_negative_028 {t a : ℝ} (tb : RealMem negative_028.t t) (ab : RealMem negative_028.a a) : RealMem negative_028.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((109/100):ℝ) ((11/10):ℝ) := by simpa [negative_028,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((109/100):ℝ)<((11/10):ℝ)) tB
  have aB : a∈Icc ((1122884570620277/1649267441664000):ℝ) ((1135769472508277/1649267441664000):ℝ) := by simpa [negative_028,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1122884570620277/1649267441664000):ℝ)<((1135769472508277/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR028Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_028,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR028Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_028,RealMem] using v

def shortNegativeR029Q00T := Grid.ofRats (11/10) (111/100)
def shortNegativeR029Q00P : PrimalThetaParameters := ⟨⟨⟨36977870770506292427522,38158005291281482869335,true⟩,⟨0,0,true⟩⟩, ⟨⟨1302206829016465924604206,1309624704941605617875710,true⟩,⟨0,0,true⟩⟩, ⟨(-1193538815603372371841815),(-1178703063753161704780084),true⟩, ⟨4562847003064127523355935,4663246832758349984134074,true⟩⟩
theorem shortNegativeR029Q00P_ok : shortNegativeR029Q00P.encloses (primalThetaParameters shortNegativeR029Q00T (Grid.ofRats (1130971143171329/1649267441664000) (1137413594115329/1649267441664000))) := by decide +kernel

def shortNegativeR029Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨505574562749513489621665,509560970173585435216588,true⟩,⟨2868158518563761691336768,2890773676156885238353973,true⟩,⟨⟨565848760066024909898601,573266635991164603218205,true⟩,⟨1062642629742598853700997,1070060505667738547027483,true⟩⟩⟩
  | 1 => ⟨⟨2704572238106843299781,2857427183499635513733,true⟩,⟨505574562749513489621665,509560970173585435216588,true⟩,⟨⟨(-1214122136586354822970256),(-1191868508811073182041311),true⟩,⟨(-130725688865292181537322),(-108472061090010540623288),true⟩⟩⟩
  | 2 => ⟨⟨442541669746616876,505755050567267700,true⟩,⟨2704572238106843299781,2857427183499635513733,true⟩,⟨⟨749817373996904078090176,786906753622327666622401,true⟩,⟨(-951883522300212393871866),(-914794142674788805337380),true⟩⟩⟩
  | 3 => ⟨⟨2180529786530,2859833226618,true⟩,⟨442541669746616876,505755050567267700,true⟩,⟨⟨322493449932272076716061,374418581407837612852256,true⟩,⟨1131655697108071530461418,1183580828583637066608753,true⟩⟩⟩
  | 4 => ⟨⟨(-34359399296),34360236597,true⟩,⟨2180529786530,2859833226618,true⟩,⟨⟨(-1189280329352381147900117),(-1122519446026673664168600),true⟩,⟨(-387494952760945918436680),(-320734069435238434716196),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359399296),34360236597,true⟩,⟨⟨896287907236419100958374,977884542412268532262899,true⟩,⟨(-804585620817928842665096),(-722988985642079411362956),true⟩⟩⟩
theorem shortNegativeR029Q00F_ok : ∀ n : Fin 6, (shortNegativeR029Q00F n).encloses (FactoredFrequency.build shortNegativeR029Q00T (Grid.ofRats (1130971143171329/1649267441664000) (1137413594115329/1649267441664000)) n) := by decide +kernel
def shortNegativeR029Q00L : ℕ → ℚ
  | 0 => (-409121/250000)
  | 1 => (-11209/15625)
  | 2 => (-284749/1000000)
  | 3 => (-55401/200000)
  | 4 => (-123277/200000)
  | 5 => (-1320649/1000000)
  | 6 => (-1142609/500000)
  | 7 => (-843479/250000)
  | 8 => (-2147057/500000)
  | 9 => (-952903/200000)
  | 10 => (-172613/40000)
  | 11 => (-775049/250000)
  | _ => 0
def shortNegativeR029Q00U : ℕ → ℚ
  | 0 => (-56937/62500)
  | 1 => (58693/1000000)
  | 2 => (67641/125000)
  | 3 => (571507/1000000)
  | 4 => (121529/500000)
  | 5 => (-324977/1000000)
  | 6 => (-1148739/1000000)
  | 7 => (-66811/31250)
  | 8 => (-95457/31250)
  | 9 => (-3421539/1000000)
  | 10 => (-120393/40000)
  | 11 => (-1968709/1000000)
  | _ => 0
private theorem shortNegativeR029Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR029Q00L (0:Fin 12)) (shortNegativeR029Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR029Q00L (1:Fin 12)) (shortNegativeR029Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR029Q00L (2:Fin 12)) (shortNegativeR029Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR029Q00L (3:Fin 12)) (shortNegativeR029Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR029Q00L (4:Fin 12)) (shortNegativeR029Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR029Q00L (5:Fin 12)) (shortNegativeR029Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR029Q00L (6:Fin 12)) (shortNegativeR029Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR029Q00L (7:Fin 12)) (shortNegativeR029Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR029Q00L (8:Fin 12)) (shortNegativeR029Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR029Q00L (9:Fin 12)) (shortNegativeR029Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR029Q00L (10:Fin 12)) (shortNegativeR029Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR029Q00L (11:Fin 12)) (shortNegativeR029Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR029Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR029Q00P shortNegativeR029Q00F (shortNegativeNodes12 k)).re (shortNegativeR029Q00L k) (shortNegativeR029Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR029Q00Point00
  · exact shortNegativeR029Q00Point01
  · exact shortNegativeR029Q00Point02
  · exact shortNegativeR029Q00Point03
  · exact shortNegativeR029Q00Point04
  · exact shortNegativeR029Q00Point05
  · exact shortNegativeR029Q00Point06
  · exact shortNegativeR029Q00Point07
  · exact shortNegativeR029Q00Point08
  · exact shortNegativeR029Q00Point09
  · exact shortNegativeR029Q00Point10
  · exact shortNegativeR029Q00Point11

theorem shortNegativeR029Q00Bound {t a : ℝ} (tl : ((11/10):ℝ)≤t) (tu : t≤((111/100):ℝ)) (al : ((1130971143171329/1649267441664000):ℝ)≤a) (au : a≤((1137413594115329/1649267441664000):ℝ)) : (((-733002110038912304953629479550945/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-379780610325305942890113993818081/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR029Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1130971143171329/1649267441664000) (1137413594115329/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR029Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR029Q00F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR029Q00L shortNegativeR029Q00U (-733002110038912304953629479550945/324518553658426726783156020576256) (-379780610325305942890113993818081/324518553658426726783156020576256) shortNegativeR029Q00Samples (by decide +kernel)

def shortNegativeR029Q01T := Grid.ofRats (11/10) (111/100)
def shortNegativeR029Q01P : PrimalThetaParameters := ⟨⟨⟨36977870770506292427522,38158005291281482869335,true⟩,⟨0,0,true⟩⟩, ⟨⟨1309624704941536898394802,1317042580866676591666329,true⟩,⟨0,0,true⟩⟩, ⟨(-1178703063753230424260577),(-1163867311903019757198894),true⟩, ⟨4539027228059563356753176,4638870661753292596454139,true⟩⟩
theorem shortNegativeR029Q01P_ok : shortNegativeR029Q01P.encloses (primalThetaParameters shortNegativeR029Q01T (Grid.ofRats (1137413594115329/1649267441664000) (1143856045059329/1649267441664000))) := by decide +kernel

def shortNegativeR029Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨505574562749513489621665,509560970173585435216588,true⟩,⟨2868158518563761691336768,2890773676156885238353973,true⟩,⟨⟨559295028088433224045548,566712904013572917365308,true⟩,⟨1066117296311830390167461,1073535172236970083494221,true⟩⟩⟩
  | 1 => ⟨⟨2704572238106843299781,2857427183499635513733,true⟩,⟨505574562749513489621665,509560970173585435216588,true⟩,⟨⟨(-1211716903090398636729475),(-1189463275315116995799977),true⟩,⟨(-152848636621533668922230),(-130595008846252028007305),true⟩⟩⟩
  | 2 => ⟨⟨442541669746616876,505755050567267700,true⟩,⟨2704572238106843299781,2857427183499635513733,true⟩,⟨⟨778085781240517237648046,815175160865940826179861,true⟩,⟨(-927874954304339357335794),(-890785574678915768802427),true⟩⟩⟩
  | 3 => ⟨⟨2180529786530,2859833226618,true⟩,⟨442541669746616876,505755050567267700,true⟩,⟨⟨272465968216940667674632,324391099692506203810556,true⟩,⟨1145550151842584517114285,1197475283318150053262227,true⟩⟩⟩
  | 4 => ⟨⟨(-34359399296),34360236597,true⟩,⟨2180529786530,2859833226618,true⟩,⟨⟨(-1167972816140430630531170),(-1101211932814723146798066),true⟩,⟨(-450755310465752379228776),(-383994427140044895505545),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359399296),34360236597,true⟩,⟨⟨945667033796640279653315,1027263668972489710956411,true⟩,⟨(-739645760059190851215347),(-658049124883341419916206),true⟩⟩⟩
theorem shortNegativeR029Q01F_ok : ∀ n : Fin 6, (shortNegativeR029Q01F n).encloses (FactoredFrequency.build shortNegativeR029Q01T (Grid.ofRats (1137413594115329/1649267441664000) (1143856045059329/1649267441664000)) n) := by decide +kernel
def shortNegativeR029Q01L : ℕ → ℚ
  | 0 => (-1677633/1000000)
  | 1 => (-754829/1000000)
  | 2 => (-311511/1000000)
  | 3 => (-290281/1000000)
  | 4 => (-615369/1000000)
  | 5 => (-1304437/1000000)
  | 6 => (-1127073/500000)
  | 7 => (-16659/5000)
  | 8 => (-4252227/1000000)
  | 9 => (-1184249/250000)
  | 10 => (-1079121/250000)
  | 11 => (-3116197/1000000)
  | _ => 0
def shortNegativeR029Q01U : ℕ → ℚ
  | 0 => (-191607/200000)
  | 1 => (13489/1000000)
  | 2 => (507871/1000000)
  | 3 => (552969/1000000)
  | 4 => (119743/500000)
  | 5 => (-314189/1000000)
  | 6 => (-1124381/1000000)
  | 7 => (-525919/250000)
  | 8 => (-754961/250000)
  | 9 => (-212491/62500)
  | 10 => (-75707/25000)
  | 11 => (-2012913/1000000)
  | _ => 0
private theorem shortNegativeR029Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR029Q01L (0:Fin 12)) (shortNegativeR029Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR029Q01L (1:Fin 12)) (shortNegativeR029Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR029Q01L (2:Fin 12)) (shortNegativeR029Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR029Q01L (3:Fin 12)) (shortNegativeR029Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR029Q01L (4:Fin 12)) (shortNegativeR029Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR029Q01L (5:Fin 12)) (shortNegativeR029Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR029Q01L (6:Fin 12)) (shortNegativeR029Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR029Q01L (7:Fin 12)) (shortNegativeR029Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR029Q01L (8:Fin 12)) (shortNegativeR029Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR029Q01L (9:Fin 12)) (shortNegativeR029Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR029Q01L (10:Fin 12)) (shortNegativeR029Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR029Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR029Q01L (11:Fin 12)) (shortNegativeR029Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR029Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR029Q01P shortNegativeR029Q01F (shortNegativeNodes12 k)).re (shortNegativeR029Q01L k) (shortNegativeR029Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR029Q01Point00
  · exact shortNegativeR029Q01Point01
  · exact shortNegativeR029Q01Point02
  · exact shortNegativeR029Q01Point03
  · exact shortNegativeR029Q01Point04
  · exact shortNegativeR029Q01Point05
  · exact shortNegativeR029Q01Point06
  · exact shortNegativeR029Q01Point07
  · exact shortNegativeR029Q01Point08
  · exact shortNegativeR029Q01Point09
  · exact shortNegativeR029Q01Point10
  · exact shortNegativeR029Q01Point11

theorem shortNegativeR029Q01Bound {t a : ℝ} (tl : ((11/10):ℝ)≤t) (tu : t≤((111/100):ℝ)) (al : ((1137413594115329/1649267441664000):ℝ)≤a) (au : a≤((1143856045059329/1649267441664000):ℝ)) : (((-733002110038912304953629479550945/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-379780610325305942890113993818081/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR029Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1137413594115329/1649267441664000) (1143856045059329/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR029Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR029Q01F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR029Q01L shortNegativeR029Q01U (-733002110038912304953629479550945/324518553658426726783156020576256) (-379780610325305942890113993818081/324518553658426726783156020576256) shortNegativeR029Q01Samples (by decide +kernel)

theorem short_original_negative_029 {t a : ℝ} (tb : RealMem negative_029.t t) (ab : RealMem negative_029.a a) : RealMem negative_029.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((11/10):ℝ) ((111/100):ℝ) := by simpa [negative_029,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((11/10):ℝ)<((111/100):ℝ)) tB
  have aB : a∈Icc ((1130971143171329/1649267441664000):ℝ) ((1143856045059329/1649267441664000):ℝ) := by simpa [negative_029,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1130971143171329/1649267441664000):ℝ)<((1143856045059329/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR029Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_029,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR029Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_029,RealMem] using v

def shortNegativeR030Q00T := Grid.ofRats (111/100) (28/25)
def shortNegativeR030Q00P : PrimalThetaParameters := ⟨⟨⟨35834234947159207818315,36977870770575011904837,true⟩,⟨0,0,true⟩⟩, ⟨⟨1311701828902286991357881,1319119704827426684629414,true⟩,⟨0,0,true⟩⟩, ⟨(-1174548815831730238334406),(-1159713063981519571272736),true⟩, ⟨4508023267618441813578293,4606102737045154291841157,true⟩⟩
theorem shortNegativeR030Q00P_ok : shortNegativeR030Q00P.encloses (primalThetaParameters shortNegativeR030Q00T (Grid.ofRats (1139217583472513/1649267441664000) (1145660034416513/1649267441664000))) := by decide +kernel

def shortNegativeR030Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨501619341866631604858968,505574562749582209116881,true⟩,⟨2890773676156816518772326,2913567152120298063636459,true⟩,⟨⟨557456068901236990392334,564873944826376683712371,true⟩,⟨1067083045759033545347838,1074500921684173238674959,true⟩⟩⟩
  | 1 => ⟨⟨2559894101082637847593,2704572238175562776664,true⟩,⟨501619341866631604858968,505574562749582209116881,true⟩,⟨⟨(-1210970456499737463937557),(-1188716828724455823007734),true⟩,⟨(-159035132160272877006356),(-136781504384991236091011),true⟩⟩⟩
  | 2 => ⟨⟨387229263615223170,442541738466093613,true⟩,⟨2559894101082637847593,2704572238175562776664,true⟩,⟨⟨785868148345337572504274,822957527970761161037147,true⟩,⟨(-920997803906410733419947),(-883908424280987144885743),true⟩⟩⟩
  | 3 => ⟨⟨1701892832362,2249249263267,true⟩,⟨387229263615223170,442541738466093613,true⟩,⟨⟨258354827430393673066519,310279958905959209202477,true⟩,⟨1149054564891790434047895,1200979696367355970196116,true⟩⟩⟩
  | 4 => ⟨⟨(-34359507611),34360077441,true⟩,⟨1701892832362,2249249263267,true⟩,⟨⟨(-1161383387128203227177108),(-1094622503802495743443765),true⟩,⟨(-468249378645479247507503),(-401488495319771763783698),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359507611),34360077441,true⟩,⟨⟨958698093593799473120497,1040294728769648904423826,true⟩,⟨(-720878137436857336683919),(-639281502261007905384990),true⟩⟩⟩
theorem shortNegativeR030Q00F_ok : ∀ n : Fin 6, (shortNegativeR030Q00F n).encloses (FactoredFrequency.build shortNegativeR030Q00T (Grid.ofRats (1139217583472513/1649267441664000) (1145660034416513/1649267441664000)) n) := by decide +kernel
def shortNegativeR030Q00L : ℕ → ℚ
  | 0 => (-1751031/1000000)
  | 1 => (-848243/1000000)
  | 2 => (-202971/500000)
  | 3 => (-94043/250000)
  | 4 => (-344883/500000)
  | 5 => (-272273/200000)
  | 6 => (-2286267/1000000)
  | 7 => (-832859/250000)
  | 8 => (-4223001/1000000)
  | 9 => (-469197/100000)
  | 10 => (-53657/12500)
  | 11 => (-62709/20000)
  | _ => 0
def shortNegativeR030Q00U : ℕ → ℚ
  | 0 => (-64731/62500)
  | 1 => (-83889/1000000)
  | 2 => (81787/200000)
  | 3 => (46373/100000)
  | 4 => (164171/1000000)
  | 5 => (-372857/1000000)
  | 6 => (-581279/500000)
  | 7 => (-2114899/1000000)
  | 8 => (-3003743/1000000)
  | 9 => (-1685547/500000)
  | 10 => (-94637/31250)
  | 11 => (-2059311/1000000)
  | _ => 0
private theorem shortNegativeR030Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR030Q00L (0:Fin 12)) (shortNegativeR030Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR030Q00L (1:Fin 12)) (shortNegativeR030Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR030Q00L (2:Fin 12)) (shortNegativeR030Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR030Q00L (3:Fin 12)) (shortNegativeR030Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR030Q00L (4:Fin 12)) (shortNegativeR030Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR030Q00L (5:Fin 12)) (shortNegativeR030Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR030Q00L (6:Fin 12)) (shortNegativeR030Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR030Q00L (7:Fin 12)) (shortNegativeR030Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR030Q00L (8:Fin 12)) (shortNegativeR030Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR030Q00L (9:Fin 12)) (shortNegativeR030Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR030Q00L (10:Fin 12)) (shortNegativeR030Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR030Q00L (11:Fin 12)) (shortNegativeR030Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR030Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR030Q00P shortNegativeR030Q00F (shortNegativeNodes12 k)).re (shortNegativeR030Q00L k) (shortNegativeR030Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR030Q00Point00
  · exact shortNegativeR030Q00Point01
  · exact shortNegativeR030Q00Point02
  · exact shortNegativeR030Q00Point03
  · exact shortNegativeR030Q00Point04
  · exact shortNegativeR030Q00Point05
  · exact shortNegativeR030Q00Point06
  · exact shortNegativeR030Q00Point07
  · exact shortNegativeR030Q00Point08
  · exact shortNegativeR030Q00Point09
  · exact shortNegativeR030Q00Point10
  · exact shortNegativeR030Q00Point11

theorem shortNegativeR030Q00Bound {t a : ℝ} (tl : ((111/100):ℝ)≤t) (tu : t≤((28/25):ℝ)) (al : ((1139217583472513/1649267441664000):ℝ)≤a) (au : a≤((1145660034416513/1649267441664000):ℝ)) : (((-186135106815808931958911068027009/81129638414606681695789005144064):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-98860077753915864277137772525697/81129638414606681695789005144064):ℚ):ℝ) := by
  have ts : shortNegativeR030Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1139217583472513/1649267441664000) (1145660034416513/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR030Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR030Q00F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR030Q00L shortNegativeR030Q00U (-186135106815808931958911068027009/81129638414606681695789005144064) (-98860077753915864277137772525697/81129638414606681695789005144064) shortNegativeR030Q00Samples (by decide +kernel)

def shortNegativeR030Q01T := Grid.ofRats (111/100) (28/25)
def shortNegativeR030Q01P : PrimalThetaParameters := ⟨⟨⟨35834234947159207818315,36977870770575011904837,true⟩,⟨0,0,true⟩⟩, ⟨⟨1319119704827357965148476,1326537580752497658420033,true⟩,⟨0,0,true⟩⟩, ⟨(-1159713063981588290753168),(-1144877312131377623691545),true⟩, ⟨4484811000923501539221132,4582350008773350160747935,true⟩⟩
theorem shortNegativeR030Q01P_ok : shortNegativeR030Q01P.encloses (primalThetaParameters shortNegativeR030Q01T (Grid.ofRats (1145660034416513/1649267441664000) (1152102485360513/1649267441664000))) := by decide +kernel

def shortNegativeR030Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨501619341866631604858968,505574562749582209116881,true⟩,⟨2890773676156816518772326,2913567152120298063636459,true⟩,⟨⟨550875249033213596267764,558293124958353289587668,true⟩,⟨1070506132153805322483024,1077924008078945015810089,true⟩⟩⟩
  | 1 => ⟨⟨2559894101082637847593,2704572238175562776664,true⟩,⟨501619341866631604858968,505574562749582209116881,true⟩,⟨⟨(-1208044672679247284555875),(-1185791044903965643625721),true⟩,⟨(-181095271657366220823649),(-158841643882084579907632),true⟩⟩⟩
  | 2 => ⟨⟨387229263615223170,442541738466093613,true⟩,⟨2559894101082637847593,2704572238175562776664,true⟩,⟨⟨813172177392771428291333,850261557018195016822956,true⟩,⟨(-895897919781576446983314),(-858808540156152858451064),true⟩⟩⟩
  | 3 => ⟨⟨1701892832362,2249249263267,true⟩,⟨387229263615223170,442541738466093613,true⟩,⟨⟨207639421931304914154694,259564553406870450290920,true⟩,⟨1160178972480972272531516,1212104103956537808680852,true⟩⟩⟩
  | 4 => ⟨⟨(-34359507611),34360077441,true⟩,⟨1701892832362,2249249263267,true⟩,⟨⟨(-1135661140287909177283506),(-1068900256962201693548863),true⟩,⟨(-529846854192002213497702),(-463085970866294729771397),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359507611),34360077441,true⟩,⟨⟨1002289555542931582174291,1083886190718781013475612,true⟩,⟨(-651919685450520037658561),(-570323050274670606363192),true⟩⟩⟩
theorem shortNegativeR030Q01F_ok : ∀ n : Fin 6, (shortNegativeR030Q01F n).encloses (FactoredFrequency.build shortNegativeR030Q01T (Grid.ofRats (1145660034416513/1649267441664000) (1152102485360513/1649267441664000)) n) := by decide +kernel
def shortNegativeR030Q01L : ℕ → ℚ
  | 0 => (-1789671/1000000)
  | 1 => (-442039/500000)
  | 2 => (-215943/500000)
  | 3 => (-194579/500000)
  | 4 => (-344401/500000)
  | 5 => (-26911/20000)
  | 6 => (-1127991/500000)
  | 7 => (-4113/1250)
  | 8 => (-4182119/1000000)
  | 9 => (-4664291/1000000)
  | 10 => (-4291961/1000000)
  | 11 => (-3161717/1000000)
  | _ => 0
def shortNegativeR030Q01U : ℕ → ℚ
  | 0 => (-1079149/1000000)
  | 1 => (-63269/500000)
  | 2 => (376427/1000000)
  | 3 => (222683/500000)
  | 4 => (80193/500000)
  | 5 => (-90653/250000)
  | 6 => (-1139099/1000000)
  | 7 => (-2081779/1000000)
  | 8 => (-2969789/1000000)
  | 9 => (-3349499/1000000)
  | 10 => (-189461/62500)
  | 11 => (-262569/125000)
  | _ => 0
private theorem shortNegativeR030Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR030Q01L (0:Fin 12)) (shortNegativeR030Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR030Q01L (1:Fin 12)) (shortNegativeR030Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR030Q01L (2:Fin 12)) (shortNegativeR030Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR030Q01L (3:Fin 12)) (shortNegativeR030Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR030Q01L (4:Fin 12)) (shortNegativeR030Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR030Q01L (5:Fin 12)) (shortNegativeR030Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR030Q01L (6:Fin 12)) (shortNegativeR030Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR030Q01L (7:Fin 12)) (shortNegativeR030Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR030Q01L (8:Fin 12)) (shortNegativeR030Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR030Q01L (9:Fin 12)) (shortNegativeR030Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR030Q01L (10:Fin 12)) (shortNegativeR030Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR030Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR030Q01L (11:Fin 12)) (shortNegativeR030Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR030Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR030Q01P shortNegativeR030Q01F (shortNegativeNodes12 k)).re (shortNegativeR030Q01L k) (shortNegativeR030Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR030Q01Point00
  · exact shortNegativeR030Q01Point01
  · exact shortNegativeR030Q01Point02
  · exact shortNegativeR030Q01Point03
  · exact shortNegativeR030Q01Point04
  · exact shortNegativeR030Q01Point05
  · exact shortNegativeR030Q01Point06
  · exact shortNegativeR030Q01Point07
  · exact shortNegativeR030Q01Point08
  · exact shortNegativeR030Q01Point09
  · exact shortNegativeR030Q01Point10
  · exact shortNegativeR030Q01Point11

theorem shortNegativeR030Q01Bound {t a : ℝ} (tl : ((111/100):ℝ)≤t) (tu : t≤((28/25):ℝ)) (al : ((1145660034416513/1649267441664000):ℝ)≤a) (au : a≤((1152102485360513/1649267441664000):ℝ)) : (((-186135106815808931958911068027009/81129638414606681695789005144064):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-98860077753915864277137772525697/81129638414606681695789005144064):ℚ):ℝ) := by
  have ts : shortNegativeR030Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1145660034416513/1649267441664000) (1152102485360513/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR030Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR030Q01F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR030Q01L shortNegativeR030Q01U (-186135106815808931958911068027009/81129638414606681695789005144064) (-98860077753915864277137772525697/81129638414606681695789005144064) shortNegativeR030Q01Samples (by decide +kernel)

theorem short_original_negative_030 {t a : ℝ} (tb : RealMem negative_030.t t) (ab : RealMem negative_030.a a) : RealMem negative_030.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((111/100):ℝ) ((28/25):ℝ) := by simpa [negative_030,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((111/100):ℝ)<((28/25):ℝ)) tB
  have aB : a∈Icc ((1139217583472513/1649267441664000):ℝ) ((1152102485360513/1649267441664000):ℝ) := by simpa [negative_030,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1139217583472513/1649267441664000):ℝ)<((1152102485360513/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR030Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_030,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR030Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_030,RealMem] using v

def shortNegativeR031Q00T := Grid.ofRats (28/25) (9/8)
def shortNegativeR031Q00P : PrimalThetaParameters := ⟨⟨⟨35275749915396907726800,35834234947227927295616,true⟩,⟨0,0,true⟩⟩, ⟨⟨1321388276733010034619904,1336224028583220701682087,true⟩,⟨0,0,true⟩⟩, ⟨(-1155175920170284151810297),(-1125504416469931537167498),true⟩, ⟨4419564402565150257636159,4574738570516667941631514,true⟩⟩
theorem shortNegativeR031Q00P_ok : shortNegativeR031Q00P.encloses (primalThetaParameters shortNegativeR031Q00T (Grid.ofRats (229526059395443/329853488332800) (232103039773043/329853488332800))) := by decide +kernel

def shortNegativeR031Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨499653350059888439888068,501619341866700324354139,true⟩,⟨2913567152120229344052830,2925031198441167316819644,true⟩,⟨⟨541848118296869462726610,556683870147080129837147,true⟩,⟨1069526182474516679003198,1084361934324727346121009,true⟩⟩⟩
  | 1 => ⟨⟨2490483716219743865622,2559894101151357324468,true⟩,⟨499653350059888439888068,501619341866700324354139,true⟩,⟨⟨(-1216518684881095461043882),(-1172011429330600898741208),true⟩,⟨(-209957145874584204592622),(-165449890324089642303798),true⟩⟩⟩
  | 2 => ⟨⟨362222288518332684,387229332334699907,true⟩,⟨2490483716219743865622,2559894101151357324468,true⟩,⟨⟨816061398302062779647204,890240157552841237131712,true⟩,⟨(-893614561656067405095449),(-819435802405288947610894),true⟩⟩⟩
  | 3 => ⟨⟨1502886071908,1770612309099,true⟩,⟨362222288518332684,387229332334699907,true⟩,⟨⟨140491171018596145652308,244341433969658498323336,true⟩,⟨1141589679436085206994089,1245439942387147559678896,true⟩⟩⟩
  | 4 => ⟨⟨(-34359548003),34359969126,true⟩,⟨1502886071908,1770612309099,true⟩,⟨⟨(-1145864726066629945807166),(-1012342959415283697956122),true⟩,⟨(-611771464794146309344635),(-478249698142800061500943),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359548003),34359969126,true⟩,⟨⟨993170857875610639567145,1156364128227240782564055,true⟩,⟨(-635109483455650852297718),(-471916213104020709307980),true⟩⟩⟩
theorem shortNegativeR031Q00F_ok : ∀ n : Fin 6, (shortNegativeR031Q00F n).encloses (FactoredFrequency.build shortNegativeR031Q00T (Grid.ofRats (229526059395443/329853488332800) (232103039773043/329853488332800)) n) := by decide +kernel
def shortNegativeR031Q00L : ℕ → ℚ
  | 0 => (-910679/500000)
  | 1 => (-932133/1000000)
  | 2 => (-239019/500000)
  | 3 => (-21413/50000)
  | 4 => (-143351/200000)
  | 5 => (-1356343/1000000)
  | 6 => (-140089/62500)
  | 7 => (-3246933/1000000)
  | 8 => (-2057537/500000)
  | 9 => (-2292197/500000)
  | 10 => (-530063/125000)
  | 11 => (-3170971/1000000)
  | _ => 0
def shortNegativeR031Q00U : ℕ → ℚ
  | 0 => (-1194683/1000000)
  | 1 => (-10487/40000)
  | 2 => (123573/500000)
  | 3 => (337459/1000000)
  | 4 => (7299/100000)
  | 5 => (-53239/125000)
  | 6 => (-117729/100000)
  | 7 => (-2091067/1000000)
  | 8 => (-369457/125000)
  | 9 => (-3335067/1000000)
  | 10 => (-1523583/500000)
  | 11 => (-217691/100000)
  | _ => 0
private theorem shortNegativeR031Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR031Q00L (0:Fin 12)) (shortNegativeR031Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR031Q00L (1:Fin 12)) (shortNegativeR031Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR031Q00L (2:Fin 12)) (shortNegativeR031Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR031Q00L (3:Fin 12)) (shortNegativeR031Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR031Q00L (4:Fin 12)) (shortNegativeR031Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR031Q00L (5:Fin 12)) (shortNegativeR031Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR031Q00L (6:Fin 12)) (shortNegativeR031Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR031Q00L (7:Fin 12)) (shortNegativeR031Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR031Q00L (8:Fin 12)) (shortNegativeR031Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR031Q00L (9:Fin 12)) (shortNegativeR031Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR031Q00L (10:Fin 12)) (shortNegativeR031Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR031Q00L (11:Fin 12)) (shortNegativeR031Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR031Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR031Q00P shortNegativeR031Q00F (shortNegativeNodes12 k)).re (shortNegativeR031Q00L k) (shortNegativeR031Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR031Q00Point00
  · exact shortNegativeR031Q00Point01
  · exact shortNegativeR031Q00Point02
  · exact shortNegativeR031Q00Point03
  · exact shortNegativeR031Q00Point04
  · exact shortNegativeR031Q00Point05
  · exact shortNegativeR031Q00Point06
  · exact shortNegativeR031Q00Point07
  · exact shortNegativeR031Q00Point08
  · exact shortNegativeR031Q00Point09
  · exact shortNegativeR031Q00Point10
  · exact shortNegativeR031Q00Point11

theorem shortNegativeR031Q00Bound {t a : ℝ} (tl : ((28/25):ℝ)≤t) (tu : t≤((9/8):ℝ)) (al : ((229526059395443/329853488332800):ℝ)≤a) (au : a≤((232103039773043/329853488332800):ℝ)) : (((-3011097093740113115739402564069499/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1651975420747651704763246842800251/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR031Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (229526059395443/329853488332800) (232103039773043/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR031Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR031Q00F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR031Q00L shortNegativeR031Q00U (-3011097093740113115739402564069499/1298074214633706907132624082305024) (-1651975420747651704763246842800251/1298074214633706907132624082305024) shortNegativeR031Q00Samples (by decide +kernel)

def shortNegativeR031Q10T := Grid.ofRats (9/8) (113/100)
def shortNegativeR031Q10P : PrimalThetaParameters := ⟨⟨⟨34725969005019148729570,35275749915465627204092,true⟩,⟨0,0,true⟩⟩, ⟨⟨1321388276733010034619904,1336224028583220701682087,true⟩,⟨0,0,true⟩⟩, ⟨(-1155175920170284151810297),(-1125504416469931537167498),true⟩, ⟨4407980676845477555278463,4562263693355855645284789,true⟩⟩
theorem shortNegativeR031Q10P_ok : shortNegativeR031Q10P.encloses (primalThetaParameters shortNegativeR031Q10T (Grid.ofRats (229526059395443/329853488332800) (232103039773043/329853488332800))) := by decide +kernel

def shortNegativeR031Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨497695063545707954112456,499653350059957159383282,true⟩,⟨2925031198441098597234931,2936540352477488192805440,true⟩,⟨⟨541848118296869462726610,556683870147080129837147,true⟩,⟨1069526182474516679003198,1084361934324727346121009,true⟩⟩⟩
  | 1 => ⟨⟨2422955362931793877356,2490483716288463342495,true⟩,⟨497695063545707954112456,499653350059957159383282,true⟩,⟨⟨(-1216518684881095461043882),(-1172011429330600898741208),true⟩,⟨(-209957145874584204592622),(-165449890324089642303798),true⟩⟩⟩
  | 2 => ⟨⟨338830244953655280,362222357237809421,true⟩,⟨2422955362931793877356,2490483716288463342495,true⟩,⟨⟨816061398302062779647204,890240157552841237131712,true⟩,⟨(-893614561656067405095449),(-819435802405288947610894),true⟩⟩⟩
  | 3 => ⟨⟨1326689178736,1571605548645,true⟩,⟨338830244953655280,362222357237809421,true⟩,⟨⟨140491171018596145652308,244341433969658498323336,true⟩,⟨1141589679436085206994089,1245439942387147559678896,true⟩⟩⟩
  | 4 => ⟨⟨(-34359581325),34359928734,true⟩,⟨1326689178736,1571605548645,true⟩,⟨⟨(-1145864726066629945807166),(-1012342959415283697956122),true⟩,⟨(-611771464794146309344635),(-478249698142800061500943),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359581325),34359928734,true⟩,⟨⟨993170857875610639567145,1156364128227240782564055,true⟩,⟨(-635109483455650852297718),(-471916213104020709307980),true⟩⟩⟩
theorem shortNegativeR031Q10F_ok : ∀ n : Fin 6, (shortNegativeR031Q10F n).encloses (FactoredFrequency.build shortNegativeR031Q10T (Grid.ofRats (229526059395443/329853488332800) (232103039773043/329853488332800)) n) := by decide +kernel
def shortNegativeR031Q10L : ℕ → ℚ
  | 0 => (-462307/250000)
  | 1 => (-485421/500000)
  | 2 => (-259759/500000)
  | 3 => (-467929/1000000)
  | 4 => (-188177/250000)
  | 5 => (-1385871/1000000)
  | 6 => (-2261047/1000000)
  | 7 => (-50823/15625)
  | 8 => (-513389/125000)
  | 9 => (-1141771/250000)
  | 10 => (-4228621/1000000)
  | 11 => (-3178029/1000000)
  | _ => 0
def shortNegativeR031Q10U : ℕ → ℚ
  | 0 => (-1222877/1000000)
  | 1 => (-30103/100000)
  | 2 => (20451/100000)
  | 3 => (59373/200000)
  | 4 => (36623/1000000)
  | 5 => (-455787/1000000)
  | 6 => (-18736/15625)
  | 7 => (-2101339/1000000)
  | 8 => (-738241/250000)
  | 9 => (-3324419/1000000)
  | 10 => (-760483/250000)
  | 11 => (-2190673/1000000)
  | _ => 0
private theorem shortNegativeR031Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR031Q10L (0:Fin 12)) (shortNegativeR031Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR031Q10L (1:Fin 12)) (shortNegativeR031Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR031Q10L (2:Fin 12)) (shortNegativeR031Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR031Q10L (3:Fin 12)) (shortNegativeR031Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR031Q10L (4:Fin 12)) (shortNegativeR031Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR031Q10L (5:Fin 12)) (shortNegativeR031Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR031Q10L (6:Fin 12)) (shortNegativeR031Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR031Q10L (7:Fin 12)) (shortNegativeR031Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR031Q10L (8:Fin 12)) (shortNegativeR031Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR031Q10L (9:Fin 12)) (shortNegativeR031Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR031Q10L (10:Fin 12)) (shortNegativeR031Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR031Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR031Q10L (11:Fin 12)) (shortNegativeR031Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR031Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR031Q10P shortNegativeR031Q10F (shortNegativeNodes12 k)).re (shortNegativeR031Q10L k) (shortNegativeR031Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR031Q10Point00
  · exact shortNegativeR031Q10Point01
  · exact shortNegativeR031Q10Point02
  · exact shortNegativeR031Q10Point03
  · exact shortNegativeR031Q10Point04
  · exact shortNegativeR031Q10Point05
  · exact shortNegativeR031Q10Point06
  · exact shortNegativeR031Q10Point07
  · exact shortNegativeR031Q10Point08
  · exact shortNegativeR031Q10Point09
  · exact shortNegativeR031Q10Point10
  · exact shortNegativeR031Q10Point11

theorem shortNegativeR031Q10Bound {t a : ℝ} (tl : ((9/8):ℝ)≤t) (tu : t≤((113/100):ℝ)) (al : ((229526059395443/329853488332800):ℝ)≤a) (au : a≤((232103039773043/329853488332800):ℝ)) : (((-3011097093740113115739402564069499/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1651975420747651704763246842800251/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR031Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (229526059395443/329853488332800) (232103039773043/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR031Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR031Q10F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR031Q10L shortNegativeR031Q10U (-3011097093740113115739402564069499/1298074214633706907132624082305024) (-1651975420747651704763246842800251/1298074214633706907132624082305024) shortNegativeR031Q10Samples (by decide +kernel)

theorem short_original_negative_031 {t a : ℝ} (tb : RealMem negative_031.t t) (ab : RealMem negative_031.a a) : RealMem negative_031.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((28/25):ℝ) ((113/100):ℝ) := by simpa [negative_031,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((28/25):ℝ)<((113/100):ℝ)) tB
  have aB : a∈Icc ((229526059395443/329853488332800):ℝ) ((232103039773043/329853488332800):ℝ) := by simpa [negative_031,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((229526059395443/329853488332800):ℝ)<((232103039773043/329853488332800):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR031Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_031,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR031Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_031,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_028
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_029
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_030
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_031
