import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR012Q00T := Grid.ofRats (431/500) (863/1000)
def factoredHeatR012Q00P : HeatGridParameters := ⟨⟨⟨⟨80342040898211077498120,80594839751331238200334,true⟩,⟨0,0,true⟩⟩, ⟨⟨1124191818014897193893034,1126046286996233656821007,true⟩,⟨0,0,true⟩⟩, ⟨(-1549568837606509833265292),(-1545859899643905626888321),true⟩, ⟨6270728118494015121875999,6310089208552623349750518,true⟩⟩, ⟨375257780705568722607293,399997076083503534398500,true⟩, ⟨596868164717203638210193,603886935317195053031605,true⟩, ⟨(-1493628290931997042690210),(-1479365043302509591138380),true⟩, ⟨(-2788733592274998510295462),(-2781195414815795021297041),true⟩, ⟨(-608514259557056694215993),(-607057763025022752058603),true⟩⟩
theorem factoredHeatR012Q00P_ok : factoredHeatR012Q00P.encloses (heatGridParameters factoredHeatR012Q00T (Grid.ofRats (195272897858239/329853488332800) (195595020405439/329853488332800))) := by decide +kernel
def factoredHeatR012Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨613812113292488340810541,614294389563665883007005,true⟩,⟨2379155112207796824309255,2381024430246817746037338,true⟩,⟨⟨721153779738717102981964,723008248720053565957493,true⟩,⟨968660639928337243899768,970515108909673706878822,true⟩⟩⟩
  | 1 => ⟨⟨10515992428122847382694,10573966334239966057836,true⟩,⟨613812113292488340810541,614294389563665883007005,true⟩,⟨⟨(-1138594818845379613764595),(-1133031411901507663865658),true⟩,⟨411259603980080613947211,416823010923952563836211,true⟩⟩⟩
  | 2 => ⟨⟨11973146048674986335,12134080785870472233,true⟩,⟨10515992428122847382694,10573966334239966057836,true⟩,⟨⟨(-75928234376536443864191),(-66655889470129007052951),true⟩,⟨(-1211458064547319904022502),(-1202185719640912467195630),true⟩⟩⟩
  | 3 => ⟨⟨905926644552534,928323823736652,true⟩,⟨11973146048674986335,12134080785870472233,true⟩,⟨⟨1170170819198279537229207,1183152102067222460937479,true⟩,⟨270943034229648103967053,283924317098591027662953,true⟩⟩⟩
  | 4 => ⟨⟨(-29804050778),39094166678,true⟩,⟨905926644552534,928323823736652,true⟩,⟨⟨(-611246953122856326807049),(-594556732291377916162718),true⟩,⟨1039515092756070122645187,1056205313587548533295640,true⟩⟩⟩
  | _ => ⟨⟨(-34359736846),34359739978,true⟩,⟨(-29804050778),39094166678,true⟩,⟨⟨(-841415250358850032991473),(-821016091564836135443097),true⟩,⟨(-888027663749721156190023),(-867628504955707258641006),true⟩⟩⟩
theorem factoredHeatR012Q00F_ok : ∀ n : Fin 6, (factoredHeatR012Q00F n).encloses (FactoredFrequency.build factoredHeatR012Q00T (Grid.ofRats (195272897858239/329853488332800) (195595020405439/329853488332800)) n) := by decide +kernel
def factoredHeatR012Q00U : ℕ → ℚ
  | 0 => (-716112/15625)
  | 1 => (-129269/4000)
  | 2 => (-19436649/1000000)
  | 3 => (-224843/20000)
  | 4 => (-1353477/200000)
  | 5 => (-282647/62500)
  | 6 => (-1687853/500000)
  | 7 => (-734513/250000)
  | 8 => (-611891/200000)
  | 9 => (-393373/100000)
  | 10 => (-6364377/1000000)
  | 11 => (-2733959/250000)
  | 12 => (-17052969/1000000)
  | 13 => (-2317743/100000)
  | 14 => (-13045733/500000)
  | 15 => (-5926503/250000)
  | 16 => (-18728293/1000000)
  | 17 => (-3496769/250000)
  | 18 => (-5649469/500000)
  | 19 => (-10294871/1000000)
  | 20 => (-5084433/500000)
  | 21 => (-1265067/125000)
  | 22 => (-2300071/250000)
  | 23 => (-253077/40000)
  | 24 => (131793/1000000)
  | 25 => (11029859/1000000)
  | 26 => (25311423/1000000)
  | 27 => (37019653/1000000)
  | 28 => (17568573/500000)
  | 29 => (10995057/1000000)
  | 30 => (-4957237/200000)
  | 31 => (-1466299/31250)
  | _ => 0
theorem factoredHeatR012Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR012Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR012Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR012Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR012Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR012Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR012Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR012Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR012Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR012Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR012Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR012Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR012Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR012Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR012Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR012Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR012Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR012Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR012Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR012Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR012Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR012Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR012Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR012Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR012Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR012Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR012Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR012Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR012Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR012Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR012Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR012Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR012Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR012Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR012Q00P factoredHeatR012Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR012Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR012Q00Point00
  · exact factoredHeatR012Q00Point01
  · exact factoredHeatR012Q00Point02
  · exact factoredHeatR012Q00Point03
  · exact factoredHeatR012Q00Point04
  · exact factoredHeatR012Q00Point05
  · exact factoredHeatR012Q00Point06
  · exact factoredHeatR012Q00Point07
  · exact factoredHeatR012Q00Point08
  · exact factoredHeatR012Q00Point09
  · exact factoredHeatR012Q00Point10
  · exact factoredHeatR012Q00Point11
  · exact factoredHeatR012Q00Point12
  · exact factoredHeatR012Q00Point13
  · exact factoredHeatR012Q00Point14
  · exact factoredHeatR012Q00Point15
  · exact factoredHeatR012Q00Point16
  · exact factoredHeatR012Q00Point17
  · exact factoredHeatR012Q00Point18
  · exact factoredHeatR012Q00Point19
  · exact factoredHeatR012Q00Point20
  · exact factoredHeatR012Q00Point21
  · exact factoredHeatR012Q00Point22
  · exact factoredHeatR012Q00Point23
  · exact factoredHeatR012Q00Point24
  · exact factoredHeatR012Q00Point25
  · exact factoredHeatR012Q00Point26
  · exact factoredHeatR012Q00Point27
  · exact factoredHeatR012Q00Point28
  · exact factoredHeatR012Q00Point29
  · exact factoredHeatR012Q00Point30
  · exact factoredHeatR012Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR012Q00Bound {t a : ℝ} (tl : ((431/500):ℝ)≤t) (tu : t≤((863/1000):ℝ)) (al : ((195272897858239/329853488332800):ℝ)≤a) (au : a≤((195595020405439/329853488332800):ℝ)) : reportedHeatPeriod t a≤(((-347047332693636423085523133793793/40564819207303340847894502572032):ℚ):ℝ) := by
  have ts : factoredHeatR012Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (195272897858239/329853488332800) (195595020405439/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR012Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR012Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR012Q00U (-347047332693636423085523133793793/40564819207303340847894502572032) factoredHeatR012Q00Samples (by decide +kernel)

theorem factored_original_heat_012 {t a : ℝ} (tb : RealMem derivative_012.t t) (ab : RealMem derivative_012.a a) : reportedHeatPeriod t a≤(derivative_012.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((431/500):ℝ) ((863/1000):ℝ) := by simpa [derivative_012,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((431/500):ℝ)<((863/1000):ℝ)) tB
  have aB : a∈Icc ((195272897858239/329853488332800):ℝ) ((195595020405439/329853488332800):ℝ) := by simpa [derivative_012,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((195272897858239/329853488332800):ℝ)<((195595020405439/329853488332800):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR012Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_012] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR013Q00T := Grid.ofRats (863/1000) (108/125)
def factoredHeatR013Q00P : HeatGridParameters := ⟨⟨⟨⟨80090034989972248743962,80342040898279796975910,true⟩,⟨0,0,true⟩⟩, ⟨⟨1124801046621662566450123,1126655515602999029378097,true⟩,⟨0,0,true⟩⟩, ⟨(-1548350380392979088151111),(-1544641442430374881774144),true⟩, ⟨6262337686803279652096925,6301588155396688045079018,true⟩⟩, ⟨375984309081455076438051,400701035086111464836569,true⟩, ⟨596890734303608247395869,603896971569711383770713,true⟩, ⟨(-1491523923006784425370448),(-1477303389228621533415752),true⟩, ⟨(-2784804975730779841993028),(-2777291090258659858491981),true⟩, ⟨(-608035772528213984357714),(-606579275996180042200327),true⟩⟩
theorem factoredHeatR013Q00P_ok : factoredHeatR013Q00P.encloses (heatGridParameters factoredHeatR013Q00T (Grid.ofRats (325631202149053/549755813888000) (326168073061053/549755813888000))) := by decide +kernel
def factoredHeatR013Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨613330215651569905905775,613812113292557060309551,true⟩,⟨2381024430246749026474151,2382895217021420188924145,true⟩,⟨⟨720665071928470388792662,722519540909806851767961,true⟩,⟨969024403812814853536734,970878872794151316515505,true⟩⟩⟩
  | 1 => ⟨⟨10458336375723332637979,10515992428191566859952,true⟩,⟨613330215651569905905775,613812113292557060309551,true⟩,⟨⟨(-1139219479117449643754172),(-1133656072173577693855187),true⟩,⟨409541979351134543101313,415105386295006492990316,true⟩⟩⟩
  | 2 => ⟨⟨11814345861421566561,11973146117394463073,true⟩,⟨10458336375723332637979,10515992428191566859952,true⟩,⟨⟨(-72887169534157020895337),(-63614824627749584083795),true⟩,⟨(-1211633868693075844039144),(-1202361523786668407211930),true⟩⟩⟩
  | 3 => ⟨⟨884135258820717,905995364029271,true⟩,⟨11814345861421566561,11973146117394463073,true⟩,⟨⟨1169184826544155850608003,1182166109413098774316427,true⟩,⟨275092084108376040169821,288073366977318963865939,true⟩⟩⟩
  | 4 => ⟨⟨(-29976043429),38915425959,true⟩,⟨884135258820717,905995364029271,true⟩,⟨⟨(-615993283590401509213999),(-599303062758923098568877),true⟩,⟨1036769876065843370143655,1053460096897321780794800,true⟩⟩⟩
  | _ => ⟨⟨(-34359736929),34359739891,true⟩,⟨(-29976043429),38915425959,true⟩,⟨⟨(-836536384417702082480611),(-816137225623688184932214),true⟩,⟨(-892621883058407266097396),(-872222724264393368548224),true⟩⟩⟩
theorem factoredHeatR013Q00F_ok : ∀ n : Fin 6, (factoredHeatR013Q00F n).encloses (FactoredFrequency.build factoredHeatR013Q00T (Grid.ofRats (325631202149053/549755813888000) (326168073061053/549755813888000)) n) := by decide +kernel
def factoredHeatR013Q00U : ℕ → ℚ
  | 0 => (-5707683/125000)
  | 1 => (-4038577/125000)
  | 2 => (-19500999/1000000)
  | 3 => (-5660097/500000)
  | 4 => (-1366889/200000)
  | 5 => (-182973/40000)
  | 6 => (-1706573/500000)
  | 7 => (-2961803/1000000)
  | 8 => (-767307/250000)
  | 9 => (-3927177/1000000)
  | 10 => (-6337107/1000000)
  | 11 => (-10881053/1000000)
  | 12 => (-3393581/200000)
  | 13 => (-5768611/250000)
  | 14 => (-13004627/500000)
  | 15 => (-23674133/1000000)
  | 16 => (-937233/50000)
  | 17 => (-2805239/200000)
  | 18 => (-5668997/500000)
  | 19 => (-10323291/1000000)
  | 20 => (-5092213/500000)
  | 21 => (-101223/10000)
  | 22 => (-9188699/1000000)
  | 23 => (-98526/15625)
  | 24 => (150427/1000000)
  | 25 => (11020051/1000000)
  | 26 => (6310281/250000)
  | 27 => (18443877/500000)
  | 28 => (35025763/1000000)
  | 29 => (11060671/1000000)
  | 30 => (-24497397/1000000)
  | 31 => (-46602623/1000000)
  | _ => 0
theorem factoredHeatR013Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR013Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR013Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR013Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR013Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR013Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR013Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR013Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR013Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR013Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR013Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR013Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR013Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR013Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR013Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR013Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR013Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR013Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR013Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR013Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR013Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR013Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR013Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR013Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR013Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR013Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR013Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR013Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR013Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR013Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR013Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR013Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR013Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR013Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR013Q00P factoredHeatR013Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR013Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR013Q00Point00
  · exact factoredHeatR013Q00Point01
  · exact factoredHeatR013Q00Point02
  · exact factoredHeatR013Q00Point03
  · exact factoredHeatR013Q00Point04
  · exact factoredHeatR013Q00Point05
  · exact factoredHeatR013Q00Point06
  · exact factoredHeatR013Q00Point07
  · exact factoredHeatR013Q00Point08
  · exact factoredHeatR013Q00Point09
  · exact factoredHeatR013Q00Point10
  · exact factoredHeatR013Q00Point11
  · exact factoredHeatR013Q00Point12
  · exact factoredHeatR013Q00Point13
  · exact factoredHeatR013Q00Point14
  · exact factoredHeatR013Q00Point15
  · exact factoredHeatR013Q00Point16
  · exact factoredHeatR013Q00Point17
  · exact factoredHeatR013Q00Point18
  · exact factoredHeatR013Q00Point19
  · exact factoredHeatR013Q00Point20
  · exact factoredHeatR013Q00Point21
  · exact factoredHeatR013Q00Point22
  · exact factoredHeatR013Q00Point23
  · exact factoredHeatR013Q00Point24
  · exact factoredHeatR013Q00Point25
  · exact factoredHeatR013Q00Point26
  · exact factoredHeatR013Q00Point27
  · exact factoredHeatR013Q00Point28
  · exact factoredHeatR013Q00Point29
  · exact factoredHeatR013Q00Point30
  · exact factoredHeatR013Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR013Q00Bound {t a : ℝ} (tl : ((863/1000):ℝ)≤t) (tu : t≤((108/125):ℝ)) (al : ((325631202149053/549755813888000):ℝ)≤a) (au : a≤((326168073061053/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-1388890002734027180103341747374141/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR013Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (325631202149053/549755813888000) (326168073061053/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR013Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR013Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR013Q00U (-1388890002734027180103341747374141/162259276829213363391578010288128) factoredHeatR013Q00Samples (by decide +kernel)

theorem factored_original_heat_013 {t a : ℝ} (tb : RealMem derivative_013.t t) (ab : RealMem derivative_013.a a) : reportedHeatPeriod t a≤(derivative_013.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((863/1000):ℝ) ((108/125):ℝ) := by simpa [derivative_013,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((863/1000):ℝ)<((108/125):ℝ)) tB
  have aB : a∈Icc ((325631202149053/549755813888000):ℝ) ((326168073061053/549755813888000):ℝ) := by simpa [derivative_013,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((325631202149053/549755813888000):ℝ)<((326168073061053/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR013Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_013] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR014Q00T := Grid.ofRats (108/125) (173/200)
def factoredHeatR014Q00P : HeatGridParameters := ⟨⟨⟨⟨79838819539345365766088,80090034990040968221748,true⟩,⟨0,0,true⟩⟩, ⟨⟨1125411399600474030290424,1127265868581810493218401,true⟩,⟨0,0,true⟩⟩, ⟨(-1547129674435356160470504),(-1543420736472751954093541),true⟩, ⟨6253960014607200009177633,6293100231350083394255519,true⟩⟩, ⟨376711326192913118233913,401405598060308289871414,true⟩, ⟨596909962307141163951344,603903688029634183590666,true⟩, ⟨(-1489427720914549638218627),(-1475249748539276164126972),true⟩, ⟨(-2780882708518241583101688),(-2773393029942406609112089),true⟩, ⟨(-607556402419631298974500),(-606099905887597356817116),true⟩⟩
theorem factoredHeatR014Q00P_ok : factoredHeatR014Q00P.encloses (heatGridParameters factoredHeatR014Q00T (Grid.ofRats (977423700124141/1649267441664000) (979034312860141/1649267441664000))) := by decide +kernel
def factoredHeatR014Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨612848696343583151157382,613330215651638625404650,true⟩,⟨2382895217021351469361901,2384767473685668268359427,true⟩,⟨⟨720175278413933548956204,722029747395270011931778,true⟩,⟨969388592038803326685933,971243061020139789665089,true⟩⟩⟩
  | 1 => ⟨⟨10400996434275875522026,10458336375792052115229,true⟩,⟨612848696343583151157382,613330215651638625404650,true⟩,⟨⟨(-1139842687582820158888163),(-1134279280638948208989079),true⟩,⟨407820239708671127735676,413383646652543077624747,true⟩⟩⟩
  | 2 => ⟨⟨11657651845703751198,11814345930141043299,true⟩,⟨10400996434275875522026,10458336375792052115229,true⟩,⟨⟨(-69840057693966094618344),(-60567712787558657807409),true⟩,⟨(-1211802312916235595843801),(-1202529968009828159017148),true⟩⟩⟩
  | 3 => ⟨⟨862868028642907,884203978297454,true⟩,⟨11657651845703751198,11814345930141043299,true⟩,⟨⟨1168182343655593218957600,1181163626524536142666280,true⟩,⟨279245277607044209987274,292226560475987133683717,true⟩⟩⟩
  | 4 => ⟨⟨(-30141542774),38743433308,true⟩,⟨862868028642907,884203978297454,true⟩,⟨⟨(-620735839395971491464563),(-604045618564493080819173),true⟩,⟨1033998034805623396696897,1050688255637101807348202,true⟩⟩⟩
  | _ => ⟨⟨(-34359737007),34359739808,true⟩,⟨(-30141542774),38743433308,true⟩,⟨⟨(-831623051624511938289645),(-811223892830498040741517),true⟩,⟨(-897197390332644070869805),(-876798231538630173320774),true⟩⟩⟩
theorem factoredHeatR014Q00F_ok : ∀ n : Fin 6, (factoredHeatR014Q00F n).encloses (FactoredFrequency.build factoredHeatR014Q00T (Grid.ofRats (977423700124141/1649267441664000) (979034312860141/1649267441664000)) n) := by decide +kernel
def factoredHeatR014Q00U : ℕ → ℚ
  | 0 => (-9098287/200000)
  | 1 => (-8074669/250000)
  | 2 => (-978209/50000)
  | 3 => (-5698737/500000)
  | 4 => (-6901041/1000000)
  | 5 => (-925199/200000)
  | 6 => (-53912/15625)
  | 7 => (-2985393/1000000)
  | 8 => (-3078899/1000000)
  | 9 => (-3920601/1000000)
  | 10 => (-6309921/1000000)
  | 11 => (-169164/15625)
  | 12 => (-1688321/100000)
  | 13 => (-22971843/1000000)
  | 14 => (-5184519/200000)
  | 15 => (-23641879/1000000)
  | 16 => (-18760417/1000000)
  | 17 => (-14064767/1000000)
  | 18 => (-2275331/200000)
  | 19 => (-10351433/1000000)
  | 20 => (-10199669/1000000)
  | 21 => (-5061949/500000)
  | 22 => (-2294253/250000)
  | 23 => (-6284393/1000000)
  | 24 => (168971/1000000)
  | 25 => (1376269/125000)
  | 26 => (12585489/500000)
  | 27 => (36756423/1000000)
  | 28 => (6982979/200000)
  | 29 => (11125501/1000000)
  | 30 => (-4842169/200000)
  | 31 => (-4628521/100000)
  | _ => 0
theorem factoredHeatR014Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR014Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR014Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR014Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR014Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR014Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR014Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR014Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR014Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR014Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR014Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR014Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR014Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR014Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR014Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR014Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR014Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR014Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR014Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR014Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR014Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR014Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR014Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR014Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR014Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR014Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR014Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR014Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR014Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR014Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR014Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR014Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR014Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR014Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR014Q00P factoredHeatR014Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR014Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR014Q00Point00
  · exact factoredHeatR014Q00Point01
  · exact factoredHeatR014Q00Point02
  · exact factoredHeatR014Q00Point03
  · exact factoredHeatR014Q00Point04
  · exact factoredHeatR014Q00Point05
  · exact factoredHeatR014Q00Point06
  · exact factoredHeatR014Q00Point07
  · exact factoredHeatR014Q00Point08
  · exact factoredHeatR014Q00Point09
  · exact factoredHeatR014Q00Point10
  · exact factoredHeatR014Q00Point11
  · exact factoredHeatR014Q00Point12
  · exact factoredHeatR014Q00Point13
  · exact factoredHeatR014Q00Point14
  · exact factoredHeatR014Q00Point15
  · exact factoredHeatR014Q00Point16
  · exact factoredHeatR014Q00Point17
  · exact factoredHeatR014Q00Point18
  · exact factoredHeatR014Q00Point19
  · exact factoredHeatR014Q00Point20
  · exact factoredHeatR014Q00Point21
  · exact factoredHeatR014Q00Point22
  · exact factoredHeatR014Q00Point23
  · exact factoredHeatR014Q00Point24
  · exact factoredHeatR014Q00Point25
  · exact factoredHeatR014Q00Point26
  · exact factoredHeatR014Q00Point27
  · exact factoredHeatR014Q00Point28
  · exact factoredHeatR014Q00Point29
  · exact factoredHeatR014Q00Point30
  · exact factoredHeatR014Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR014Q00Bound {t a : ℝ} (tl : ((108/125):ℝ)≤t) (tu : t≤((173/200):ℝ)) (al : ((977423700124141/1649267441664000):ℝ)≤a) (au : a≤((979034312860141/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2778667922986107612164962118190623/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR014Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (977423700124141/1649267441664000) (979034312860141/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR014Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR014Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR014Q00U (-2778667922986107612164962118190623/324518553658426726783156020576256) factoredHeatR014Q00Samples (by decide +kernel)

theorem factored_original_heat_014 {t a : ℝ} (tb : RealMem derivative_014.t t) (ab : RealMem derivative_014.a a) : reportedHeatPeriod t a≤(derivative_014.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((108/125):ℝ) ((173/200):ℝ) := by simpa [derivative_014,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((108/125):ℝ)<((173/200):ℝ)) tB
  have aB : a∈Icc ((977423700124141/1649267441664000):ℝ) ((979034312860141/1649267441664000):ℝ) := by simpa [derivative_014,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((977423700124141/1649267441664000):ℝ)<((979034312860141/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR014Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_014] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR015Q00T := Grid.ofRats (173/200) (433/500)
def factoredHeatR015Q00P : HeatGridParameters := ⟨⟨⟨⟨79588392066931272212674,79838819539414085243867,true⟩,⟨0,0,true⟩⟩, ⟨⟨1126022877815890024434302,1127877346797226487362280,true⟩,⟨0,0,true⟩⟩, ⟨(-1545906718004524172182745),(-1542197780041919965805786),true⟩, ⟨6245595100732032969527309,6284625434010488757782012,true⟩⟩, ⟨377438837955371385104545,402110770548087329194731,true⟩, ⟨596925853381009053757883,603907089310070815301549,true⟩, ⟨(-1487339663401218549009900),(-1473204100535892853237337),true⟩, ⟨(-2776966804454033954312469),(-2769501248050553833640868),true⟩, ⟨(-607076148552286027909994),(-605619652020252085752613),true⟩⟩
theorem factoredHeatR015Q00P_ok : factoredHeatR015Q00P.encloses (heatGridParameters factoredHeatR015Q00T (Grid.ofRats (977954771073013/1649267441664000) (979565383809013/1649267441664000))) := by decide +kernel
def factoredHeatR015Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨612367555071502743716337,612848696343651870656261,true⟩,⟨2384767473685599548797184,2386641201394464082052407,true⟩,⟨⟨719684397609626096404371,721538866590962559379809,true⟩,⟨969753203662204495695515,971607672643540958674424,true⟩⟩⟩
  | 1 => ⟨⟨10343970870638336535503,10400996434344594999280,true⟩,⟨612367555071502743716337,612848696343651870656261,true⟩,⟨⟨(-1140464429277162662875174),(-1134901022333290712976412),true⟩,⟨406094381345080814380447,411657788288952764269170,true⟩⟩⟩
  | 2 => ⟨⟨11503036067306763086,11657651914423227936,true⟩,⟨10343970870638336535503,10400996434344594999280,true⟩,⟨⟨(-66786911606442931293659),(-57514566700035494482959),true⟩,⟨(-1211963353855829531311767),(-1202691008949422094485304),true⟩⟩⟩
  | 3 => ⟨⟨842112346328700,862936748119644,true⟩,⟨11503036067306763086,11657651914423227936,true⟩,⟨⟨1167163300485684288575767,1180144583354627212284648,true⟩,⟨283402549148168113723057,296383832017111037419777,true⟩⟩⟩
  | 4 => ⟨⟨(-30300793959),38577933963,true⟩,⟨842112346328700,862936748119644,true⟩,⟨⟨(-625474459707723120309411),(-608784238876244709664623),true⟩,⟨1031199503140290640149467,1047889723971769050800071,true⟩⟩⟩
  | _ => ⟨⟨(-34359737081),34359739730,true⟩,⟨(-30300793959),38577933963,true⟩,⟨⟨(-826675256075396518340337),(-806276097281382620791959),true⟩,⟨(-901753900077170988849972),(-881354741283157091300560),true⟩⟩⟩
theorem factoredHeatR015Q00F_ok : ∀ n : Fin 6, (factoredHeatR015Q00F n).encloses (FactoredFrequency.build factoredHeatR015Q00T (Grid.ofRats (977954771073013/1649267441664000) (979565383809013/1649267441664000)) n) := by decide +kernel
def factoredHeatR015Q00U : ℕ → ℚ
  | 0 => (-11330273/250000)
  | 1 => (-32287441/1000000)
  | 2 => (-19626197/1000000)
  | 3 => (-11473989/1000000)
  | 4 => (-6967173/1000000)
  | 5 => (-2338603/500000)
  | 6 => (-1743687/500000)
  | 7 => (-376103/125000)
  | 8 => (-772117/250000)
  | 9 => (-1957001/500000)
  | 10 => (-6282819/1000000)
  | 11 => (-2693041/250000)
  | 12 => (-16798883/1000000)
  | 13 => (-182957/8000)
  | 14 => (-2583547/100000)
  | 15 => (-23609253/1000000)
  | 16 => (-1877557/100000)
  | 17 => (-14102793/1000000)
  | 18 => (-11414923/1000000)
  | 19 => (-10379297/1000000)
  | 20 => (-10214489/1000000)
  | 21 => (-10125329/1000000)
  | 22 => (-1145653/125000)
  | 23 => (-782889/125000)
  | 24 => (187427/1000000)
  | 25 => (2750041/250000)
  | 26 => (5020197/200000)
  | 27 => (4578207/125000)
  | 28 => (34804537/1000000)
  | 29 => (11189553/1000000)
  | 30 => (-23926511/1000000)
  | 31 => (-1838773/40000)
  | _ => 0
theorem factoredHeatR015Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR015Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR015Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR015Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR015Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR015Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR015Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR015Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR015Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR015Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR015Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR015Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR015Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR015Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR015Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR015Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR015Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR015Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR015Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR015Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR015Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR015Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR015Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR015Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR015Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR015Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR015Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR015Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR015Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR015Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR015Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR015Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR015Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR015Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR015Q00P factoredHeatR015Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR015Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR015Q00Point00
  · exact factoredHeatR015Q00Point01
  · exact factoredHeatR015Q00Point02
  · exact factoredHeatR015Q00Point03
  · exact factoredHeatR015Q00Point04
  · exact factoredHeatR015Q00Point05
  · exact factoredHeatR015Q00Point06
  · exact factoredHeatR015Q00Point07
  · exact factoredHeatR015Q00Point08
  · exact factoredHeatR015Q00Point09
  · exact factoredHeatR015Q00Point10
  · exact factoredHeatR015Q00Point11
  · exact factoredHeatR015Q00Point12
  · exact factoredHeatR015Q00Point13
  · exact factoredHeatR015Q00Point14
  · exact factoredHeatR015Q00Point15
  · exact factoredHeatR015Q00Point16
  · exact factoredHeatR015Q00Point17
  · exact factoredHeatR015Q00Point18
  · exact factoredHeatR015Q00Point19
  · exact factoredHeatR015Q00Point20
  · exact factoredHeatR015Q00Point21
  · exact factoredHeatR015Q00Point22
  · exact factoredHeatR015Q00Point23
  · exact factoredHeatR015Q00Point24
  · exact factoredHeatR015Q00Point25
  · exact factoredHeatR015Q00Point26
  · exact factoredHeatR015Q00Point27
  · exact factoredHeatR015Q00Point28
  · exact factoredHeatR015Q00Point29
  · exact factoredHeatR015Q00Point30
  · exact factoredHeatR015Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR015Q00Bound {t a : ℝ} (tl : ((173/200):ℝ)≤t) (tu : t≤((433/500):ℝ)) (al : ((977954771073013/1649267441664000):ℝ)≤a) (au : a≤((979565383809013/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-694773203473323863274926243535291/81129638414606681695789005144064):ℚ):ℝ) := by
  have ts : factoredHeatR015Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (977954771073013/1649267441664000) (979565383809013/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR015Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR015Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR015Q00U (-694773203473323863274926243535291/81129638414606681695789005144064) factoredHeatR015Q00Samples (by decide +kernel)

theorem factored_original_heat_015 {t a : ℝ} (tb : RealMem derivative_015.t t) (ab : RealMem derivative_015.a a) : reportedHeatPeriod t a≤(derivative_015.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((173/200):ℝ) ((433/500):ℝ) := by simpa [derivative_015,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((173/200):ℝ)<((433/500):ℝ)) tB
  have aB : a∈Icc ((977954771073013/1649267441664000):ℝ) ((979565383809013/1649267441664000):ℝ) := by simpa [derivative_015,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((977954771073013/1649267441664000):ℝ)<((979565383809013/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR015Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_015] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR017Q00T := Grid.ofRats (867/1000) (217/250)
def factoredHeatR017Q00P : HeatGridParameters := ⟨⟨⟨⟨79089891178005632185862,79338750101176570842989,true⟩,⟨0,0,true⟩⟩, ⟨⟨1127249213442361650321255,1129103682423698113249238,true⟩,⟨0,0,true⟩⟩, ⟨(-1543454046751580920408831),(-1539745108788976714031880),true⟩, ⟨6228903542411639347622568,6267715209023442059624283,true⟩⟩, ⟨378895369239433461076891,403522966402569474410754,true⟩, ⟨596947643358171991232128,603903964791392940802035,true⟩, ⟨(-1483187897260873705651021),(-1469136699946627679855307),true⟩, ⟨(-2769154139901558456876146),(-2761736575127593255594711),true⟩, ⟨(-606112986803546353744989),(-604656490271512411587615),true⟩⟩
theorem factoredHeatR017Q00P_ok : factoredHeatR017Q00P.encloses (heatGridParameters factoredHeatR017Q00T (Grid.ofRats (326339949271293/549755813888000) (326876820183293/549755813888000))) := by decide +kernel
def factoredHeatR017Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨611406405448125414098454,611886791538605261794199,true⟩,⟨2388516401303548422424412,2390393074569845087393269,true⟩,⟨⟨718699367760181641130219,720553836741518104105689,true⟩,⟨970483693316817384533318,972338162298153847512299,true⟩⟩⟩
  | 1 => ⟨⟨10230855991683865774769,10287257961239597478371,true⟩,⟨611406405448125414098454,611886791538605261794199,true⟩,⟨⟨(-1141703452267189086414668),(-1136140045323317136515432),true⟩,⟨402630293701390515091900,408193700645262464981024,true⟩⟩⟩
  | 2 => ⟨⟨11199929333163854250,11350471031227610728,true⟩,⟨10230855991683865774769,10287257961239597478371,true⟩,⟨⟨(-60662568610991957446230),(-51390223704584520635658),true⟩,⟨(-1212263052025066133924465),(-1202990707118658697098042),true⟩⟩⟩
  | 3 => ⟨⟨802086703520286,821924626921458,true⟩,⟨11199929333163854250,11350471031227610728,true⟩,⟨⟨1165075253524719361223861,1178056536393662284933110,true⟩,⟨291729061300564428622023,304710344169507352319250,true⟩⟩⟩
  | 4 => ⟨⟨(-30601486494),38265443866,true⟩,⟨802086703520286,821924626921458,true⟩,⟨⟨(-634939245623609923123836),(-618249024792131512478180),true⟩,⟨1025522108841164958530175,1042212329672643369181432,true⟩⟩⟩
  | _ => ⟨⟨(-34359737216),34359739587,true⟩,⟨(-30601486494),38265443866,true⟩,⟨⟨(-816676303216488851608972),(-796277144422474954060483),true⟩,⟨(-910808779476762979145739),(-890409620682749081595955),true⟩⟩⟩
theorem factoredHeatR017Q00F_ok : ∀ n : Fin 6, (factoredHeatR017Q00F n).encloses (FactoredFrequency.build factoredHeatR017Q00T (Grid.ofRats (326339949271293/549755813888000) (326876820183293/549755813888000)) n) := by decide +kernel
def factoredHeatR017Q00U : ℕ → ℚ
  | 0 => (-22489757/500000)
  | 1 => (-32261087/1000000)
  | 2 => (-19746763/1000000)
  | 3 => (-11624727/1000000)
  | 4 => (-7098041/1000000)
  | 5 => (-1194643/250000)
  | 6 => (-712147/200000)
  | 7 => (-611041/200000)
  | 8 => (-3107299/1000000)
  | 9 => (-780147/200000)
  | 10 => (-6228863/1000000)
  | 11 => (-10664171/1000000)
  | 12 => (-4157831/250000)
  | 13 => (-11333167/500000)
  | 14 => (-25661587/1000000)
  | 15 => (-23542907/1000000)
  | 16 => (-9402039/500000)
  | 17 => (-3544303/250000)
  | 18 => (-2872569/250000)
  | 19 => (-5217097/500000)
  | 20 => (-2048699/200000)
  | 21 => (-2025539/200000)
  | 22 => (-182827/20000)
  | 23 => (-3110263/500000)
  | 24 => (28009/125000)
  | 25 => (439197/40000)
  | 26 => (12480729/500000)
  | 27 => (7273161/200000)
  | 28 => (6917067/200000)
  | 29 => (11315347/1000000)
  | 30 => (-23364429/1000000)
  | 31 => (-45341949/1000000)
  | _ => 0
theorem factoredHeatR017Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR017Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR017Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR017Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR017Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR017Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR017Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR017Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR017Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR017Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR017Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR017Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR017Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR017Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR017Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR017Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR017Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR017Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR017Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR017Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR017Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR017Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR017Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR017Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR017Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR017Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR017Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR017Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR017Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR017Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR017Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR017Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR017Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR017Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR017Q00P factoredHeatR017Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR017Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR017Q00Point00
  · exact factoredHeatR017Q00Point01
  · exact factoredHeatR017Q00Point02
  · exact factoredHeatR017Q00Point03
  · exact factoredHeatR017Q00Point04
  · exact factoredHeatR017Q00Point05
  · exact factoredHeatR017Q00Point06
  · exact factoredHeatR017Q00Point07
  · exact factoredHeatR017Q00Point08
  · exact factoredHeatR017Q00Point09
  · exact factoredHeatR017Q00Point10
  · exact factoredHeatR017Q00Point11
  · exact factoredHeatR017Q00Point12
  · exact factoredHeatR017Q00Point13
  · exact factoredHeatR017Q00Point14
  · exact factoredHeatR017Q00Point15
  · exact factoredHeatR017Q00Point16
  · exact factoredHeatR017Q00Point17
  · exact factoredHeatR017Q00Point18
  · exact factoredHeatR017Q00Point19
  · exact factoredHeatR017Q00Point20
  · exact factoredHeatR017Q00Point21
  · exact factoredHeatR017Q00Point22
  · exact factoredHeatR017Q00Point23
  · exact factoredHeatR017Q00Point24
  · exact factoredHeatR017Q00Point25
  · exact factoredHeatR017Q00Point26
  · exact factoredHeatR017Q00Point27
  · exact factoredHeatR017Q00Point28
  · exact factoredHeatR017Q00Point29
  · exact factoredHeatR017Q00Point30
  · exact factoredHeatR017Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR017Q00Bound {t a : ℝ} (tl : ((867/1000):ℝ)≤t) (tu : t≤((217/250):ℝ)) (al : ((326339949271293/549755813888000):ℝ)≤a) (au : a≤((326876820183293/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-1359188946676541414506934727623027/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR017Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (326339949271293/549755813888000) (326876820183293/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR017Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR017Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR017Q00U (-1359188946676541414506934727623027/162259276829213363391578010288128) factoredHeatR017Q00Samples (by decide +kernel)

theorem factored_original_heat_017 {t a : ℝ} (tb : RealMem derivative_017.t t) (ab : RealMem derivative_017.a a) : reportedHeatPeriod t a≤(derivative_017.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((867/1000):ℝ) ((217/250):ℝ) := by simpa [derivative_017,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((867/1000):ℝ)<((217/250):ℝ)) tB
  have aB : a∈Icc ((326339949271293/549755813888000):ℝ) ((326876820183293/549755813888000):ℝ) := by simpa [derivative_017,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((326339949271293/549755813888000):ℝ)<((326876820183293/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR017Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_017] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_012
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_013
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_014
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_015
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_017
