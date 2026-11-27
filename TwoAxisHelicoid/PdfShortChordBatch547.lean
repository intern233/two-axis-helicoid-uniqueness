import TwoAxisHelicoid.PdfSharedChord521Gauss8
import TwoAxisHelicoid.PdfSharedChord521Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP547Params : ChordParams := ⟨⟨(-28398379527524866447699),(-28239592324432526844444),true⟩,⟨1882174039593526058905445,1889422656050360013433357,true⟩,⟨134283072484363044862421,135218663450414343160694,true⟩,⟨253304849452055757246927,254828206193615148045524,true⟩,⟨361056510043079252656138,362116642606890587955490,true⟩,⟨1153432628307383087159608,1153735831328601702837508,true⟩,⟨(-2167155761964273800117060),(-2163352520299248535804130),true⟩,⟨⟨1142621206900699903686452,1157076967739384636082510,true⟩,⟨(-63142519),63142519,true⟩⟩⟩
theorem sharedDiskP547Params_ok : chordParams (Grid.ofRats (669/800) (67/80)) (Grid.ofRats (963136808707063/1649267441664000) (964747421443063/1649267441664000))=sharedDiskP547Params := by decide +kernel
def sharedDiskP547Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3033829614805798876930809),(-2744078782316805081246910),true⟩,⟨(-222149729051442381457473),14728863579077261800180,true⟩⟩
  | 0,1 => ⟨⟨(-2703798873472575637033881),(-2436453499177793542061210),true⟩,⟨(-277619371299849968386901),(-52816652608058287038200),true⟩⟩
  | 0,2 => ⟨⟨(-2464754651161568337783022),(-2215193115334971884503678),true⟩,⟨(-326594175373173139424986),(-112942038177738836821586),true⟩⟩
  | 0,3 => ⟨⟨(-2329891519920595144229121),(-2090751464126556613562019),true⟩,⟨(-357312339911794222618601),(-150522685868003399450495),true⟩⟩
  | 0,4 => ⟨⟨(-3423400000293710282677967),(-3110933044553458265666135),true⟩,⟨(-175815994312762102956527),69595535972028675657793,true⟩⟩
  | 0,5 => ⟨⟨(-3818807825014530004727283),(-3487622427199980895825232),true⟩,⟨(-150865474949834718421197),96869364754491340029052,true⟩⟩
  | 0,6 => ⟨⟨(-4152327345119781151332848),(-3808735143732235526030786),true⟩,⟨(-147602620891228961775603),97495967678650298401917,true⟩⟩
  | 0,7 => ⟨⟨(-4361292752349611028400104),(-4011370047450940239331090),true⟩,⟨(-155602361729330975761572),86641235022235343964899,true⟩⟩
  | 1,0 => ⟨⟨(-1511721577016503743069638),(-1341222126266382888618516),true⟩,⟨(-580676488316155950476714),(-425288385566927861753987),true⟩⟩
  | 1,1 => ⟨⟨(-1331807906582873367287167),(-1176807008089743393593747),true⟩,⟨(-634488752212238097769669),(-491648922957474110493455),true⟩⟩
  | 1,2 => ⟨⟨(-1200941228832856474379332),(-1057057951240396316909703),true⟩,⟨(-673377639607726300728734),(-539661632466939356904346),true⟩⟩
  | 1,3 => ⟨⟨(-1126436925974212994142424),(-988787327195114289801870),true⟩,⟨(-695187614955826268573799),(-566623467617916737606610),true⟩⟩
  | 1,4 => ⟨⟨(-1725771012559346794974940),(-1536772885870753159015927),true⟩,⟨(-517634341115607302719384),(-347608683997983890193193),true⟩⟩
  | 1,5 => ⟨⟨(-1948050868041026530804859),(-1740090756472262024880464),true⟩,⟨(-454911954819168081089716),(-270389861749185026908157),true⟩⟩
  | 1,6 => ⟨⟨(-2141767280583764877237803),(-1917714029538096993657999),true⟩,⟨(-403566631906953059198653),(-207265267068349479219580),true⟩⟩
  | 1,7 => ⟨⟨(-2266847281889463951338812),(-2032695899777039010918882),true⟩,⟨(-372386550928635284761155),(-168997911467977100854204),true⟩⟩
  | 2,0 => ⟨⟨(-295561961004232534708472),(-213474493602099638060013),true⟩,⟨(-889286384680480006034075),(-806028252879089498288718),true⟩⟩
  | 2,1 => ⟨⟨(-117072349916042467182203),(-42059843063793815418909),true⟩,⟨(-911466030756269550519792),(-833811943376541494572355),true⟩⟩
  | 2,2 => ⟨⟨13707124013755339482000,84561115675387788794879,true⟩,⟨(-922338913427571963542502),(-848194897550965449506865),true⟩⟩
  | 2,3 => ⟨⟨88726332404127369345759,157662972951537225880565,true⟩,⟨(-926666871584701872330663),(-854318559628947460797321),true⟩⟩
  | 2,4 => ⟨⟨(-508407693689932941162572),(-416053229951332382209569),true⟩,⟨(-851741098744713172871283),(-760547256029241746150082),true⟩⟩
  | 2,5 => ⟨⟨(-734429506514531845396172),(-627755864203454150212167),true⟩,⟨(-800972074077627171759429),(-698282737354881650382923),true⟩⟩
  | 2,6 => ⟨⟨(-938195530573642129237641),(-815862993543776901090404),true⟩,⟨(-748353124921533180916949),(-632535329055058061641244),true⟩⟩
  | 2,7 => ⟨⟨(-1074140499620851970069473),(-940814086784473456956013),true⟩,⟨(-710278730144300938944109),(-585300575907264986419445),true⟩⟩
  | 3,0 => ⟨⟨993890119660988820116008,1062655752560968039158211,true⟩,⟨(-942035876455768684242810),(-873619567320178931807944),true⟩⟩
  | 3,1 => ⟨⟨1215425643364737032769245,1287638467372167770496037,true⟩,⟨(-968535115745054608342796),(-897727226240256605517312),true⟩⟩
  | 3,2 => ⟨⟨1386732531150620515467777,1462473005082084330373940,true⟩,⟨(-1008034373757781075490435),(-934405745033928668141586),true⟩⟩
  | 3,3 => ⟨⟨1489164718545756838087205,1567428238885614425107024,true⟩,⟨(-1042133702821313805507192),(-966348898108741986341676),true⟩⟩
  | 3,4 => ⟨⟨744743193688479607059117,810951921012652381777304,true⟩,⟨(-933018496792877781641036),(-865845445604064296677403),true⟩⟩
  | 3,5 => ⟨⟨495627973755419707396547,560603166640450668021315,true⟩,⟨(-933209454371704934060265),(-865911683868903706629749),true⟩⟩
  | 3,6 => ⟨⟨281444139872994396089509,346642258944786216759818,true⟩,⟨(-932324592226861803377631),(-863734644898257570666601),true⟩⟩
  | 3,7 => ⟨⟨141766546762419914940844,209479287258844748530104,true⟩,⟨(-928954176529448113572531),(-857780745473010412959587),true⟩⟩
  | 4,0 => ⟨⟨2233476828048988925721641,2357320349684460964609617,true⟩,⟨(-1742064438956875775088655),(-1620084462769272689239699),true⟩⟩
  | 4,1 => ⟨⟨2398661035424451970683908,2546171416221453922074717,true⟩,⟨(-2189214563116438269512668),(-2041379540684925559125547),true⟩⟩
  | 4,2 => ⟨⟨2467424032677197332660648,2639482327281449520748391,true⟩,⟨(-2682136076638117246588896),(-2506511352921491883423489),true⟩⟩
  | 4,3 => ⟨⟨2457419772235958118517219,2647350504958181335737223,true⟩,⟨(-3053344380741745473685467),(-2856921567113299536636568),true⟩⟩
  | 4,4 => ⟨⟨2018542715450766836956606,2123673708581326881238341,true⟩,⟨(-1419305638613845979181110),(-1316996496020042954009752),true⟩⟩
  | 4,5 => ⟨⟨1808141135471504786184574,1900241359468922712207512,true⟩,⟨(-1219770427881603978180587),(-1130650851775724408903442),true⟩⟩
  | 4,6 => ⟨⟨1640145580625046608496539,1724138992692176989768716,true⟩,⟨(-1111236002116738356771680),(-1030048567433091630879575),true⟩⟩
  | 4,7 => ⟨⟨1538626919199308778816413,1618481957076328603070926,true⟩,⟨(-1062098297769806432461093),(-984857899896682307576145),true⟩⟩
  | 5,0 => ⟨⟨2209398143706609368585645,2444115112716213465833848,true⟩,⟨(-4009310117384194222122242),(-3758777218998161933347878),true⟩⟩
  | 5,1 => ⟨⟨2071432018574674873163512,2319253745267070863053946,true⟩,⟨(-4292215627270779959647352),(-4025307488163026072794000),true⟩⟩
  | 5,2 => ⟨⟨1932529556428881460034758,2191128806411576062743489,true⟩,⟨(-4524807371270683300142275),(-4244239600258168881148118),true⟩⟩
  | 5,3 => ⟨⟨1834490141982218931407596,2099725898921405432056079,true⟩,⟨(-4667733791628954767704996),(-4378665092738485022484661),true⟩⟩
  | 5,4 => ⟨⟨2317885432602043034553795,2539268370095524823190116,true⟩,⟨(-3722234164786727796176660),(-3488107862840322798817261),true⟩⟩
  | 5,5 => ⟨⟨2388342122805274036755184,2598021983446740992093780,true⟩,⟨(-3471623490083026943348151),(-3251689146285723381527780),true⟩⟩
  | 5,6 => ⟨⟨2426570544041974644900493,2627491183255911173829595,true⟩,⟨(-3285259644873958667775528),(-3075821135832566402534367),true⟩⟩
  | 5,7 => ⟨⟨2443135771394690497221953,2638991471523913630005704,true⟩,⟨(-3178084043506661473528651),(-2974665330497740923665789),true⟩⟩
  | 6,0 => ⟨⟨676053892834586069006423,999922669075169194475666,true⟩,⟨(-5708593194374443933477575),(-5348099312499151625542800),true⟩⟩
  | 6,1 => ⟨⟨193774029658338607392569,541271555887662907084530,true⟩,⟨(-5944912350878481522361495),(-5560652283620003464296468),true⟩⟩
  | 6,2 => ⟨⟨(-240454213269919053174472),126561756420099834403367,true⟩,⟨(-6092853776700610126348458),(-5690441587388805554184903),true⟩⟩
  | 6,3 => ⟨⟨(-523952387038146718131634),(-144660949670232431016536),true⟩,⟨(-6160188651853782277032826),(-5747389385615572939253505),true⟩⟩
  | 6,4 => ⟨⟨1113070042539053121526470,1414409704343238944913886,true⟩,⟨(-5414289679382680916937723),(-5078319236784778333840757),true⟩⟩
  | 6,5 => ⟨⟨1447040099683184678320955,1733469991987416139492311,true⟩,⟨(-5120528828102733120425096),(-4803821483915526758193961),true⟩⟩
  | 6,6 => ⟨⟨1667144768438025498598166,1942364541969631839965257,true⟩,⟨(-4881927712084829981353901),(-4579935478953742836833470),true⟩⟩
  | 6,7 => ⟨⟨1782755449617724436115365,2051240249142455969873497,true⟩,⟨(-4737567530093514588038209),(-4444311283567167854399036),true⟩⟩
  | 7,0 => ⟨⟨(-2976975273516488341973097),(-2516011009732978790085670),true⟩,⟨(-5861408399036372846754803),(-5403505620742875963307402),true⟩⟩
  | 7,1 => ⟨⟨(-3660122612706315501533297),(-3186209852442993894500516),true⟩,⟨(-5449377244244399203572097),(-4996289155584887758615371),true⟩⟩
  | 7,2 => ⟨⟨(-4149254692379996427756848),(-3670563551799911416599991),true⟩,⟨(-5011666610039408619597552),(-4569930219351826633274546),true⟩⟩
  | 7,3 => ⟨⟨(-4411190735617681005812757),(-3932386575470870520196090),true⟩,⟨(-4703001013324922550758600),(-4271543966168528564977521),true⟩⟩
  | 7,4 => ⟨⟨(-2210395839738222550072468),(-1769802445021434934724477),true⟩,⟨(-6129647336077056967213591),(-5676791226155573997589881),true⟩⟩
  | 7,5 => ⟨⟨(-1504844734147747129860858),(-1087273910122655625092890),true⟩,⟨(-6230984496584200946479810),(-5790380134181301045949297),true⟩⟩
  | 7,6 => ⟨⟨(-972165771137624774835667),(-574464714683751347135985),true⟩,⟨(-6223028642012050948439737),(-5795988551576511577178647),true⟩⟩
  | 7,7 => ⟨⟨(-667002565880199086479609),(-281661457377398350632264),true⟩,⟨(-6185934266141991302052282),(-5768304895734540615210523),true⟩⟩
  | 8,0 => ⟨⟨(-5151276290243985526752274),(-4748494488392774183738656),true⟩,⟨(-1780103346440535526928946),(-1498061277227504009653055),true⟩⟩
  | 8,1 => ⟨⟨(-4929169551711257201030993),(-4569465887869435470316581),true⟩,⟨(-977709298131923297821066),(-750177223028197816079063),true⟩⟩
  | 8,2 => ⟨⟨(-4644327049818818913191830),(-4322535293149818642876700),true⟩,⟨(-415640415178900560186476),(-230151577370444316673772),true⟩⟩
  | 8,3 => ⟨⟨(-4435971054708693595067835),(-4138246503416197610745195),true⟩,⟨(-116666904340360432589386),45919910499203131623513,true⟩⟩
  | 8,4 => ⟨⟨(-5184744766834821808956837),(-4744891175489094046352290),true⟩,⟨(-2702169065852245591582222),(-2364532575407784391893548),true⟩⟩
  | 8,5 => ⟨⟨(-5011884551876753068955961),(-4548207214919256807319391),true⟩,⟨(-3556491833569933090492393),(-3173972995286975834094676),true⟩⟩
  | 8,6 => ⟨⟨(-4741512610911808723032122),(-4266815804319481694705792),true⟩,⟨(-4190095740901074413746878),(-3778707387670235748957614),true⟩⟩
  | 8,7 => ⟨⟨(-4527413689346401273826425),(-4049372561709488128600420),true⟩,⟨(-4542111716902933259981655),(-4116585656776275160661354),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP547Value0_0 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP547Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value0_1 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP547Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value0_2 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP547Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value0_3 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP547Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value0_4 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP547Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value0_5 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP547Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value0_6 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP547Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value0_7 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP547Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP547Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 0 j)=sharedDiskP547Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP547Value0_0
  · exact sharedDiskP547Value0_1
  · exact sharedDiskP547Value0_2
  · exact sharedDiskP547Value0_3
  · exact sharedDiskP547Value0_4
  · exact sharedDiskP547Value0_5
  · exact sharedDiskP547Value0_6
  · exact sharedDiskP547Value0_7
private theorem sharedDiskP547Value1_0 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP547Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value1_1 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP547Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value1_2 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP547Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value1_3 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP547Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value1_4 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP547Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value1_5 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP547Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value1_6 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP547Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value1_7 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP547Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP547Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 1 j)=sharedDiskP547Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP547Value1_0
  · exact sharedDiskP547Value1_1
  · exact sharedDiskP547Value1_2
  · exact sharedDiskP547Value1_3
  · exact sharedDiskP547Value1_4
  · exact sharedDiskP547Value1_5
  · exact sharedDiskP547Value1_6
  · exact sharedDiskP547Value1_7
private theorem sharedDiskP547Value2_0 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP547Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value2_1 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP547Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value2_2 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP547Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value2_3 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP547Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value2_4 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP547Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value2_5 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP547Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value2_6 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP547Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value2_7 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP547Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP547Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 2 j)=sharedDiskP547Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP547Value2_0
  · exact sharedDiskP547Value2_1
  · exact sharedDiskP547Value2_2
  · exact sharedDiskP547Value2_3
  · exact sharedDiskP547Value2_4
  · exact sharedDiskP547Value2_5
  · exact sharedDiskP547Value2_6
  · exact sharedDiskP547Value2_7
private theorem sharedDiskP547Value3_0 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP547Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value3_1 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP547Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value3_2 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP547Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value3_3 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP547Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value3_4 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP547Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value3_5 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP547Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value3_6 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP547Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value3_7 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP547Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP547Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 3 j)=sharedDiskP547Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP547Value3_0
  · exact sharedDiskP547Value3_1
  · exact sharedDiskP547Value3_2
  · exact sharedDiskP547Value3_3
  · exact sharedDiskP547Value3_4
  · exact sharedDiskP547Value3_5
  · exact sharedDiskP547Value3_6
  · exact sharedDiskP547Value3_7
private theorem sharedDiskP547Value4_0 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP547Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value4_1 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP547Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value4_2 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP547Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value4_3 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP547Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value4_4 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP547Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value4_5 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP547Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value4_6 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP547Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value4_7 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP547Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP547Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 4 j)=sharedDiskP547Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP547Value4_0
  · exact sharedDiskP547Value4_1
  · exact sharedDiskP547Value4_2
  · exact sharedDiskP547Value4_3
  · exact sharedDiskP547Value4_4
  · exact sharedDiskP547Value4_5
  · exact sharedDiskP547Value4_6
  · exact sharedDiskP547Value4_7
private theorem sharedDiskP547Value5_0 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP547Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value5_1 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP547Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value5_2 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP547Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value5_3 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP547Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value5_4 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP547Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value5_5 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP547Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value5_6 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP547Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value5_7 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP547Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP547Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 5 j)=sharedDiskP547Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP547Value5_0
  · exact sharedDiskP547Value5_1
  · exact sharedDiskP547Value5_2
  · exact sharedDiskP547Value5_3
  · exact sharedDiskP547Value5_4
  · exact sharedDiskP547Value5_5
  · exact sharedDiskP547Value5_6
  · exact sharedDiskP547Value5_7
private theorem sharedDiskP547Value6_0 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP547Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value6_1 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP547Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value6_2 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP547Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value6_3 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP547Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value6_4 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP547Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value6_5 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP547Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value6_6 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP547Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value6_7 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP547Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP547Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 6 j)=sharedDiskP547Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP547Value6_0
  · exact sharedDiskP547Value6_1
  · exact sharedDiskP547Value6_2
  · exact sharedDiskP547Value6_3
  · exact sharedDiskP547Value6_4
  · exact sharedDiskP547Value6_5
  · exact sharedDiskP547Value6_6
  · exact sharedDiskP547Value6_7
private theorem sharedDiskP547Value7_0 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP547Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value7_1 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP547Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value7_2 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP547Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value7_3 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP547Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value7_4 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP547Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value7_5 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP547Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value7_6 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP547Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value7_7 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP547Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP547Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 7 j)=sharedDiskP547Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP547Value7_0
  · exact sharedDiskP547Value7_1
  · exact sharedDiskP547Value7_2
  · exact sharedDiskP547Value7_3
  · exact sharedDiskP547Value7_4
  · exact sharedDiskP547Value7_5
  · exact sharedDiskP547Value7_6
  · exact sharedDiskP547Value7_7
private theorem sharedDiskP547Value8_0 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP547Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value8_1 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP547Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value8_2 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP547Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value8_3 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP547Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value8_4 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP547Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value8_5 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP547Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value8_6 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP547Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP547Value8_7 : truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP547Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP547Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points 8 j)=sharedDiskP547Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP547Value8_0
  · exact sharedDiskP547Value8_1
  · exact sharedDiskP547Value8_2
  · exact sharedDiskP547Value8_3
  · exact sharedDiskP547Value8_4
  · exact sharedDiskP547Value8_5
  · exact sharedDiskP547Value8_6
  · exact sharedDiskP547Value8_7
theorem sharedDiskP547Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP547Params (sharedChord521Gauss8Points i j)=sharedDiskP547Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP547Values0_eq
  · exact sharedDiskP547Values1_eq
  · exact sharedDiskP547Values2_eq
  · exact sharedDiskP547Values3_eq
  · exact sharedDiskP547Values4_eq
  · exact sharedDiskP547Values5_eq
  · exact sharedDiskP547Values6_eq
  · exact sharedDiskP547Values7_eq
  · exact sharedDiskP547Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP547Box : HorizontalRectangle := ⟨(669/800),(67/80),(963136808707063/1649267441664000),(964747421443063/1649267441664000),(319320894451591966850738212972695/2596148429267413814265248164610048),(1246426073613220066527479706036375/2596148429267413814265248164610048),(-2089826358382523980056934650424367/649037107316853453566312041152512),(-1851068090233028147689722439478319/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP547Grid : CGrid := momentChordGrid sharedDiskP547Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP547Columns : containedInReported sharedDiskP547Grid.re sharedDiskP547Box.reLo sharedDiskP547Box.reHi=true ∧ containedInReported sharedDiskP547Grid.im sharedDiskP547Box.imLo sharedDiskP547Box.imHi=true := by
  rw [sharedDiskP547Grid,momentChordGrid_eq_tabulated sharedDiskP547Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP547Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP547Values_eq]
  decide +kernel
theorem sharedDiskP547Sound : sharedDiskP547Box.Sound := by
  intro t a tl tu al au
  change (((669/800):ℚ):ℝ)≤t at tl
  change t≤(((67/80):ℚ):ℝ) at tu
  change (((963136808707063/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((964747421443063/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP547Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(669/800))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((67/80):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(963136808707063/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((964747421443063/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP547Columns.1 sharedDiskP547Columns.2
def sharedDiskP547Rows : List SignRow := [positive_547.toSignRow]
theorem sharedDiskP547Rows_actual : ∀ r∈sharedDiskP547Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP547Rows.all (sharedDiskP547Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP547Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP548Params : ChordParams := ⟨⟨(-28557582290359735714861),(-28398379527524866447109),true⟩,⟨1877637800945107171319391,1884868828065963136530711,true⟩,⟨134531153765319542884428,135466698807934575680476,true⟩,⟨254260807179394118498301,255786191377417134503560,true⟩,⟨362023591291077399116032,363083645278027934387291,true⟩,⟨1153128709894306583044648,1153432628307383087160736,true⟩,⟨(-2163352520299248535813138),(-2159559274901597307894103),true⟩,⟨⟨1142268701877646244248288,1156731806348069533865824,true⟩,⟨(-67037768),67037768,true⟩⟩⟩
theorem sharedDiskP548Params_ok : chordParams (Grid.ofRats (67/80) (671/800)) (Grid.ofRats (321255788357211/549755813888000) (321792659269211/549755813888000))=sharedDiskP548Params := by decide +kernel
def sharedDiskP548Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3032775162080269680091363),(-2742590905978751473271203),true⟩,⟨(-221333735345122373604456),15966421753127407720909,true⟩⟩
  | 0,1 => ⟨⟨(-2704025342193094368896857),(-2436191015432968449087467),true⟩,⟨(-276307927741702696092693),(-51048542265851973919800),true⟩⟩
  | 0,2 => ⟨⟨(-2465797552485083038658973),(-2215727437034592281059876),true⟩,⟨(-324918745003710394859903),(-110810130148014950297284),true⟩⟩
  | 0,3 => ⟨⟨(-2331365690784406780488844),(-2091702323413197186225165),true⟩,⟨(-355436585536981962628594),(-148178925432960441209690),true⟩⟩
  | 0,4 => ⟨⟨(-3420645089572620960109384),(-3107815871472717417007456),true⟩,⟨(-175528704163476867037899),70271742025802982660046,true⟩⟩
  | 0,5 => ⟨⟨(-3814138916243666674662874),(-3482663493834946876622342),true⟩,⟨(-151004593634440717926480),97115139339457628412725,true⟩⟩
  | 0,6 => ⟨⟨(-4145917723527895938822116),(-3802092131309817375863703),true⟩,⟨(-147984976480352491156695),97507623234352519073520,true⟩⟩
  | 0,7 => ⟨⟨(-4353740111135932764588955),(-4003618751735072978618019),true⟩,⟨(-156084626569208732613653),86583066098408323394733,true⟩⟩
  | 1,0 => ⟨⟨(-1515281900744522712863361),(-1344235054204723032835590),true⟩,⟨(-577897049456841771708501),(-422021199556857585872113),true⟩⟩
  | 1,1 => ⟨⟨(-1335724985231141547766072),(-1180189097574928479152553),true⟩,⟨(-631640098871865930664918),(-488325101799661489985932),true⟩⟩
  | 1,2 => ⟨⟨(-1205102245568681456013840),(-1060696903684523984536240),true⟩,⟨(-670521587337466828811343),(-536343589805396358198835),true⟩⟩
  | 1,3 => ⟨⟨(-1130732266666666289252127),(-992569283486597201711909),true⟩,⟨(-692345106717728275566941),(-563327830117427076019027),true⟩⟩
  | 1,4 => ⟨⟨(-1728865970385614182203450),(-1539314303683413452981187),true⟩,⟨(-515013243009653638257346),(-344493634445451290273101),true⟩⟩
  | 1,5 => ⟨⟨(-1950606101161846771268750),(-1742095898886275606164270),true⟩,⟨(-452524577160412445842230),(-267511608152562062719315),true⟩⟩
  | 1,6 => ⟨⟨(-2143799469187498355503664),(-1919206699227648240718963),true⟩,⟨(-401425577102599998766405),(-204642679133374223779796),true⟩⟩
  | 1,7 => ⟨⟨(-2268514070252215349568065),(-2033833346360036980485497),true⟩,⟨(-370419675739444910117364),(-166558103671298997939304),true⟩⟩
  | 2,0 => ⟨⟨(-301252401926890609688937),(-218871094855909019991724),true⟩,⟨(-887528229963037176250977),(-804038035954306130313999),true⟩⟩
  | 2,1 => ⟨⟨(-123078999879897987667361),(-47804918306760294701457),true⟩,⟨(-910169636798499609379738),(-832306380489871727959281),true⟩⟩
  | 2,2 => ⟨⟨7479801323037583447457,78553541268626417400551,true⟩,⟨(-921414754243937603444066),(-847074952387029947411844),true⟩⟩
  | 2,3 => ⟨⟨82367817146623206247637,151513270852662409318296,true⟩,⟨(-925966434598223547753767),(-853428705451604864432816),true⟩⟩
  | 2,4 => ⟨⟨(-513727820490044974132569),(-421035162252871509971221),true⟩,⟨(-849522049277729737050940),(-758062678382281410148431),true⟩⟩
  | 2,5 => ⟨⟨(-739402479516023065864964),(-632272329265872775178755),true⟩,⟨(-798435103691057710162457),(-695350262578292819352125),true⟩⟩
  | 2,6 => ⟨⟨(-942820076540724473751096),(-819999621833366844446314),true⟩,⟨(-745606650586703825545566),(-629361668625676471791045),true⟩⟩
  | 2,7 => ⟨⟨(-1078528549303515907492575),(-944695358085397046648403),true⟩,⟨(-707453835492901132971377),(-582029293597980425371817),true⟩⟩
  | 3,0 => ⟨⟨986368004135219597174728,1055196269472784915080933,true⟩,⟨(-944157373532405576607240),(-875633009941784877995814),true⟩⟩
  | 3,1 => ⟨⟨1207753234306342673232175,1280037212074006833388202,true⟩,⟨(-971341318113683409659394),(-900412277180756840318804),true⟩⟩
  | 3,2 => ⟨⟨1378963164460498067647284,1454786440246565893497399,true⟩,⟨(-1011376281148585202599802),(-937612042407177934889847),true⟩⟩
  | 3,3 => ⟨⟨1481334631464961071021142,1559689960022582113508782,true⟩,⟨(-1045803993292770933031388),(-969873094697651541043169),true⟩⟩
  | 3,4 => ⟨⟨737457570488001035866588,803728581745733803562225,true⟩,⟨(-934360980780063116672087),(-867087023628179531054673),true⟩⟩
  | 3,5 => ⟨⟨488661437721715762849686,553708951124994065398099,true⟩,⟨(-933757190987348122216642),(-866357223833643289406831),true⟩⟩
  | 3,6 => ⟨⟨274760174447058554707172,340096469456797753250911,true⟩,⟨(-932221165722421678220673),(-863486749581899141944549),true⟩⟩
  | 3,7 => ⟨⟨135316486935742563497193,203230922045978001486739,true⟩,⟨(-928415330422102643069766),(-857056413272892843098150),true⟩⟩
  | 4,0 => ⟨⟨2224040071408002371235022,2348060619920183790228621,true⟩,⟨(-1748644238323774207598435),(-1626400279944539703276743),true⟩⟩
  | 4,1 => ⟨⟨2387696502684836203524431,2535415403445493647996853,true⟩,⟨(-2196663771124410980692479),(-2048517785615953223647284),true⟩⟩
  | 4,2 => ⟨⟨2454498495768432625070171,2626782718841018872538771,true⟩,⟨(-2690005855497709886948475),(-2514038513807893425573243),true⟩⟩
  | 4,3 => ⟨⟨2442891324434853994729549,2633049088254658356872987,true⟩,⟨(-3061169113158980245013736),(-2864394232757823718943389),true⟩⟩
  | 4,4 => ⟨⟨2009991574224246292952115,2115266921991143974198866,true⟩,⟨(-1424910992297151808466212),(-1322383366004739360794055),true⟩⟩
  | 4,5 => ⟨⟨1800014609639770540164013,1892234079029972340272977,true⟩,⟨(-1224544338904705903423191),(-1135240636548227234728001),true⟩⟩
  | 4,6 => ⟨⟨1632205784145553405889430,1716302773076680425162421,true⟩,⟨(-1115410280768806348056696),(-1034060498751401089177865),true⟩⟩
  | 4,7 => ⟨⟨1530764504607120600273443,1610715428865808454250130,true⟩,⟨(-1065930672787656172371132),(-988538972416190134398605),true⟩⟩
  | 5,0 => ⟨⟨2190532929269868095183250,2425428263479412921460967,true⟩,⟨(-4015480462533691895096230),(-3764636189645073066890643),true⟩⟩
  | 5,1 => ⟨⟨2051298199745999057856376,2299267733230004727311035,true⟩,⟨(-4297415600595089355460029),(-4030229465314552239216881),true⟩⟩
  | 5,2 => ⟨⟨1911385353912230654399727,2170100762594773442985018,true⟩,⟨(-4529016198301463371622495),(-4248206823237086363259783),true⟩⟩
  | 5,3 => ⟨⟨1812747072398422937414409,2078076305093100116577695,true⟩,⟨(-4671237927831046436630655),(-4381954501108617451131082),true⟩⟩
  | 5,4 => ⟨⟨2300329557531113531005071,2521913839958787900570655,true⟩,⟨(-3729150618269044377278385),(-3494689854851326668025829),true⟩⟩
  | 5,5 => ⟨⟨2371931500803289166645986,2581826698967016809869378,true⟩,⟨(-3479010590305860719924230),(-3258729600631380239596439),true⟩⟩
  | 5,6 => ⟨⟨2411005339851953208384471,2612148274100023623857678,true⟩,⟨(-3292893912240976697704081),(-3083104134705528759552103),true⟩⟩
  | 5,7 => ⟨⟨2428052263404582639518996,2624132978255870240961944,true⟩,⟨(-3185822196747310553882047),(-2982051181207037093677200),true⟩⟩
  | 6,0 => ⟨⟨650909528028199619520421,975108416479848177483660,true⟩,⟨(-5704001475468279341502258),(-5343339086168924931657332),true⟩⟩
  | 6,1 => ⟨⟨168665813471585988641638,516394090888712384036272,true⟩,⟨(-5937059023094280156379830),(-5552781384776109600492573),true⟩⟩
  | 6,2 => ⟨⟨(-265080496436453550616208),102110270092430228856863,true⟩,⟨(-6082191728526116135607420),(-5679903973664438573350320),true⟩⟩
  | 6,3 => ⟨⟨(-548008796762048941972160),(-168570752874935981864818),true⟩,⟨(-6147771316246012105151693),(-5735191219360578440323819),true⟩⟩
  | 6,4 => ⟨⟨1088478354437628710900442,1389986051829830927258382,true⟩,⟨(-5412748175522897564527389),(-5076628247941137534615837),true⟩⟩
  | 6,5 => ⟨⟨1423575732286544964720665,1710007990107188955466937,true⟩,⟨(-5121233720865455663332158),(-4804424225051123828878907),true⟩⟩
  | 6,6 => ⟨⟨1644547619652299199587088,1919821721919129607927758,true⟩,⟨(-4884223840066252458099284),(-4582064453608168203200020),true⟩⟩
  | 6,7 => ⟨⟨1760727548261257832464428,2029293769917269441799542,true⟩,⟨(-4740698714988550600807767),(-4447242241663083846915394),true⟩⟩
  | 7,0 => ⟨⟨(-2989624886288027503007922),(-2529248176714714112984092),true⟩,⟨(-5837684331689988196327615),(-5380805013490719695179023),true⟩⟩
  | 7,1 => ⟨⟨(-3667593443500851421299326),(-3194495765693181728358538),true⟩,⟨(-5424477068290603896345215),(-4972592827250408987503941),true⟩⟩
  | 7,2 => ⟨⟨(-4152394573039060049087423),(-3674680411095166648025639),true⟩,⟨(-4986899560621489564936228),(-4546462701378995604596078),true⟩⟩
  | 7,3 => ⟨⟨(-4411747210666644794031034),(-3934003577492684950220060),true⟩,⟨(-4678811969429244967405213),(-4248685988635062509821232),true⟩⟩
  | 7,4 => ⟨⟨(-2227800124668231286030243),(-1787546766146340628792017),true⟩,⟨(-6108511398683813740259206),(-5656441392187041282675573),true⟩⟩
  | 7,5 => ⟨⟨(-1525680840992248841462032),(-1108234971733417871567445),true⟩,⟨(-6213080382657305925013120),(-5773027621852934898575016),true⟩⟩
  | 7,6 => ⟨⟨(-994982829408845320501668),(-597254781662902475398583),true⟩,⟨(-6207981040539644905617654),(-5781311779867539790375332),true⟩⟩
  | 7,7 => ⟨⟨(-690707416858871468309901),(-305256991500597268859779),true⟩,⟨(-6172657145578630525783190),(-5755295167091553391671832),true⟩⟩
  | 8,0 => ⟨⟨(-5140025293176735688441087),(-4738331324894552264907942),true⟩,⟨(-1769769195806274617232556),(-1488580406146087764728696),true⟩⟩
  | 8,1 => ⟨⟨(-4918271947055429730596188),(-4559454491597172668359626),true⟩,⟨(-972177671594308807444910),(-745207177346754580922989),true⟩⟩
  | 8,2 => ⟨⟨(-4634720002275522948987572),(-4313621860310851648189357),true⟩,⟨(-413373685687261843522633),(-228229317657712943607088),true⟩⟩
  | 8,3 => ⟨⟨(-4427464605676348128846612),(-4130307187707801205593500),true⟩,⟨(-116031742112527174338410),46350276659382406018268,true⟩⟩
  | 8,4 => ⟨⟨(-5175018726694122960942402),(-4736372596613430584379104),true⟩,⟨(-2686518660551024014567230),(-2349998426556127107538796),true⟩⟩
  | 8,5 => ⟨⟨(-5005330280880251937345836),(-4542870059440756943924429),true⟩,⟨(-3536481595155515542492599),(-3155241768672330613840757),true⟩⟩
  | 8,6 => ⟨⟨(-4738447784818715353056046),(-4264908276185625152743795),true⟩,⟨(-4167457281374039640856057),(-3757405008158604683071122),true⟩⟩
  | 8,7 => ⟨⟨(-4526750025616894111169884),(-4049804988546887771690378),true⟩,⟨(-4518339727296542973193716),(-4094152063438265955506597),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP548Value0_0 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP548Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value0_1 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP548Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value0_2 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP548Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value0_3 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP548Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value0_4 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP548Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value0_5 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP548Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value0_6 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP548Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value0_7 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP548Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP548Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 0 j)=sharedDiskP548Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP548Value0_0
  · exact sharedDiskP548Value0_1
  · exact sharedDiskP548Value0_2
  · exact sharedDiskP548Value0_3
  · exact sharedDiskP548Value0_4
  · exact sharedDiskP548Value0_5
  · exact sharedDiskP548Value0_6
  · exact sharedDiskP548Value0_7
private theorem sharedDiskP548Value1_0 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP548Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value1_1 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP548Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value1_2 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP548Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value1_3 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP548Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value1_4 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP548Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value1_5 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP548Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value1_6 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP548Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value1_7 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP548Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP548Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 1 j)=sharedDiskP548Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP548Value1_0
  · exact sharedDiskP548Value1_1
  · exact sharedDiskP548Value1_2
  · exact sharedDiskP548Value1_3
  · exact sharedDiskP548Value1_4
  · exact sharedDiskP548Value1_5
  · exact sharedDiskP548Value1_6
  · exact sharedDiskP548Value1_7
private theorem sharedDiskP548Value2_0 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP548Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value2_1 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP548Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value2_2 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP548Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value2_3 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP548Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value2_4 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP548Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value2_5 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP548Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value2_6 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP548Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value2_7 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP548Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP548Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 2 j)=sharedDiskP548Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP548Value2_0
  · exact sharedDiskP548Value2_1
  · exact sharedDiskP548Value2_2
  · exact sharedDiskP548Value2_3
  · exact sharedDiskP548Value2_4
  · exact sharedDiskP548Value2_5
  · exact sharedDiskP548Value2_6
  · exact sharedDiskP548Value2_7
private theorem sharedDiskP548Value3_0 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP548Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value3_1 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP548Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value3_2 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP548Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value3_3 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP548Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value3_4 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP548Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value3_5 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP548Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value3_6 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP548Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value3_7 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP548Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP548Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 3 j)=sharedDiskP548Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP548Value3_0
  · exact sharedDiskP548Value3_1
  · exact sharedDiskP548Value3_2
  · exact sharedDiskP548Value3_3
  · exact sharedDiskP548Value3_4
  · exact sharedDiskP548Value3_5
  · exact sharedDiskP548Value3_6
  · exact sharedDiskP548Value3_7
private theorem sharedDiskP548Value4_0 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP548Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value4_1 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP548Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value4_2 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP548Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value4_3 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP548Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value4_4 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP548Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value4_5 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP548Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value4_6 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP548Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value4_7 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP548Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP548Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 4 j)=sharedDiskP548Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP548Value4_0
  · exact sharedDiskP548Value4_1
  · exact sharedDiskP548Value4_2
  · exact sharedDiskP548Value4_3
  · exact sharedDiskP548Value4_4
  · exact sharedDiskP548Value4_5
  · exact sharedDiskP548Value4_6
  · exact sharedDiskP548Value4_7
private theorem sharedDiskP548Value5_0 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP548Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value5_1 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP548Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value5_2 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP548Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value5_3 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP548Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value5_4 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP548Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value5_5 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP548Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value5_6 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP548Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value5_7 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP548Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP548Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 5 j)=sharedDiskP548Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP548Value5_0
  · exact sharedDiskP548Value5_1
  · exact sharedDiskP548Value5_2
  · exact sharedDiskP548Value5_3
  · exact sharedDiskP548Value5_4
  · exact sharedDiskP548Value5_5
  · exact sharedDiskP548Value5_6
  · exact sharedDiskP548Value5_7
private theorem sharedDiskP548Value6_0 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP548Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value6_1 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP548Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value6_2 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP548Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value6_3 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP548Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value6_4 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP548Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value6_5 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP548Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value6_6 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP548Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value6_7 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP548Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP548Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 6 j)=sharedDiskP548Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP548Value6_0
  · exact sharedDiskP548Value6_1
  · exact sharedDiskP548Value6_2
  · exact sharedDiskP548Value6_3
  · exact sharedDiskP548Value6_4
  · exact sharedDiskP548Value6_5
  · exact sharedDiskP548Value6_6
  · exact sharedDiskP548Value6_7
private theorem sharedDiskP548Value7_0 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP548Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value7_1 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP548Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value7_2 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP548Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value7_3 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP548Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value7_4 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP548Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value7_5 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP548Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value7_6 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP548Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value7_7 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP548Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP548Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 7 j)=sharedDiskP548Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP548Value7_0
  · exact sharedDiskP548Value7_1
  · exact sharedDiskP548Value7_2
  · exact sharedDiskP548Value7_3
  · exact sharedDiskP548Value7_4
  · exact sharedDiskP548Value7_5
  · exact sharedDiskP548Value7_6
  · exact sharedDiskP548Value7_7
private theorem sharedDiskP548Value8_0 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP548Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value8_1 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP548Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value8_2 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP548Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value8_3 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP548Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value8_4 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP548Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value8_5 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP548Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value8_6 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP548Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP548Value8_7 : truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP548Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP548Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points 8 j)=sharedDiskP548Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP548Value8_0
  · exact sharedDiskP548Value8_1
  · exact sharedDiskP548Value8_2
  · exact sharedDiskP548Value8_3
  · exact sharedDiskP548Value8_4
  · exact sharedDiskP548Value8_5
  · exact sharedDiskP548Value8_6
  · exact sharedDiskP548Value8_7
theorem sharedDiskP548Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP548Params (sharedChord521Gauss8Points i j)=sharedDiskP548Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP548Values0_eq
  · exact sharedDiskP548Values1_eq
  · exact sharedDiskP548Values2_eq
  · exact sharedDiskP548Values3_eq
  · exact sharedDiskP548Values4_eq
  · exact sharedDiskP548Values5_eq
  · exact sharedDiskP548Values6_eq
  · exact sharedDiskP548Values7_eq
  · exact sharedDiskP548Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP548Box : HorizontalRectangle := ⟨(67/80),(671/800),(321255788357211/549755813888000),(321792659269211/549755813888000),(288416932704502102042959277776649/2596148429267413814265248164610048),(1208954089214787278676643424296713/2596148429267413814265248164610048),(-4176905775638928187970401775995277/1298074214633706907132624082305024),(-3702650058632684497711418464094605/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP548Grid : CGrid := momentChordGrid sharedDiskP548Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP548Columns : containedInReported sharedDiskP548Grid.re sharedDiskP548Box.reLo sharedDiskP548Box.reHi=true ∧ containedInReported sharedDiskP548Grid.im sharedDiskP548Box.imLo sharedDiskP548Box.imHi=true := by
  rw [sharedDiskP548Grid,momentChordGrid_eq_tabulated sharedDiskP548Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP548Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP548Values_eq]
  decide +kernel
theorem sharedDiskP548Sound : sharedDiskP548Box.Sound := by
  intro t a tl tu al au
  change (((67/80):ℚ):ℝ)≤t at tl
  change t≤(((671/800):ℚ):ℝ) at tu
  change (((321255788357211/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((321792659269211/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP548Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(67/80))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((671/800):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(321255788357211/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((321792659269211/549755813888000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP548Columns.1 sharedDiskP548Columns.2
def sharedDiskP548Rows : List SignRow := [positive_548.toSignRow]
theorem sharedDiskP548Rows_actual : ∀ r∈sharedDiskP548Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP548Rows.all (sharedDiskP548Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP548Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP549Params : ChordParams := ⟨⟨(-28717199748898103469460),(-28557582290359735714272),true⟩,⟨1873110950671668142020526,1880324454875394010369677,true⟩,⟨134778492726164656385077,135713987261725602253907,true⟩,⟨255218376610099228173963,256745784085519976492167,true⟩,⟨362990113939545475300401,364050085432682133215993,true⟩,⟨1152824078320395112195622,1153128709894306583045774,true⟩,⟨(-2159559274901597307903093),(-2155775985317129589915549),true⟩,⟨⟨1141915091968938150572158,1156385462010888267562385,true⟩,⟨(-71160775),71160775,true⟩⟩⟩
theorem sharedDiskP549Params_ok : chordParams (Grid.ofRats (671/800) (21/25)) (Grid.ofRats (964399421498729/1649267441664000) (966010034234729/1649267441664000))=sharedDiskP549Params := by decide +kernel
def sharedDiskP549Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3031711414073440100497685),(-2741085801021153689422806),true⟩,⟨(-220531195601217473242365),17198714708664035338640,true⟩⟩
  | 0,1 => ⟨⟨(-2704238087107824596685197),(-2435907597680803429412114),true⟩,⟨(-275012013462815107900221),(-49288544312154557830734),true⟩⟩
  | 0,2 => ⟨⟨(-2466824539979028743162899),(-2216239061960181874156420),true⟩,⟨(-323259862046796407048080),(-108687758115785862475499),true⟩⟩
  | 0,3 => ⟨⟨(-2332822967376474736503162),(-2092629789410071035077872),true⟩,⟨(-353577701052083476825310),(-145845331763584678057304),true⟩⟩
  | 0,4 => ⟨⟨(-3417888138218877910015137),(-3104687926053928032737985),true⟩,⟨(-175251984533171105482556),70946333333027714602585,true⟩⟩
  | 0,5 => ⟨⟨(-3809477542078641755517356),(-3477702668625230158552536),true⟩,⟨(-151151584880694197127061),97362435049168527520163,true⟩⟩
  | 0,6 => ⟨⟨(-4139525274611779953387713),(-3795456397097264153591355),true⟩,⟨(-148373611464160250632237),97522504509779022018734,true⟩⟩
  | 0,7 => ⟨⟨(-4346211307254976863899645),(-3995881161509273269906543),true⟩,⟨(-156572730774164869983576),86528518600981094190696,true⟩⟩
  | 1,0 => ⟨⟨(-1518822380607274765300744),(-1347223261756645196948303),true⟩,⟨(-575131040471507507196811),(-418762380972167288444032),true⟩⟩
  | 1,1 => ⟨⟨(-1339621821017821404391982),(-1183546404010187196721101),true⟩,⟨(-628802704622794019357382),(-485007789572667446258467),true⟩⟩
  | 1,2 => ⟨⟨(-1209242689480959834404198),(-1064310987996911291129261),true⟩,⟨(-667674904261286745937788),(-533030393496766401311804),true⟩⟩
  | 1,3 => ⟨⟨(-1135006822982799744968228),(-996326300564068699126888),true⟩,⟨(-689510783731433018093044),(-560035986615928414994357),true⟩⟩
  | 1,4 => ⟨⟨(-1731941562153584031431370),(-1541831072699691221942044),true⟩,⟨(-512407477626007772500049),(-341388469124618007021507),true⟩⟩
  | 1,5 => ⟨⟨(-1953142601316123773906918),(-1744076590797828112901304),true⟩,⟨(-450153725885080863989366),(-264644000800915717369631),true⟩⟩
  | 1,6 => ⟨⟨(-2145813706575879690850141),(-1920675308726616988418380),true⟩,⟨(-399301473906760875308950),(-202030756799841614946608),true⟩⟩
  | 1,7 => ⟨⟨(-2270163572531042487369794),(-2034947139476538150154681),true⟩,⟨(-368469748303315713455755),(-164128682361941191500138),true⟩⟩
  | 2,0 => ⟨⟨(-306918926003339534863964),(-224240747623489338211202),true⟩,⟨(-885762280104702208153593),(-802037010934800912685627),true⟩⟩
  | 2,1 => ⟨⟨(-129061193783001486514522),(-53522859745162894676092),true⟩,⟨(-908862088195361705676805),(-830787032337090639432078),true⟩⟩
  | 2,2 => ⟨⟨1277034256051178448407,72573088854985781900892,true⟩,⟨(-920477214162028856389016),(-845939253781173831648149),true⟩⟩
  | 2,3 => ⟨⟨76033831246622707478979,145390537286874953678775,true⟩,⟨(-925251446895276819994820),(-852522065959263775239800),true⟩⟩
  | 2,4 => ⟨⟨(-519024942716764976050964),(-425990615699006457893155),true⟩,⟨(-847299516158365197193532),(-755571121400185776675705),true⟩⟩
  | 2,5 => ⟨⟨(-744353212175520490036690),(-636763164036675638163891),true⟩,⟨(-795899078156294184142223),(-692415087927043155604038),true⟩⟩
  | 2,6 => ⟨⟨(-947423210567489175772862),(-824111044471755082977646),true⟩,⟨(-742865065539168280315558),(-626188851659328514827697),true⟩⟩
  | 2,7 => ⟨⟨(-1082895654093445359936277),(-948551628977529934348303),true⟩,⟨(-704636251834743162539642),(-578761024896794865204978),true⟩⟩
  | 3,0 => ⟨⟨978859555008057457991450,1047752234017814837073715,true⟩,⟨(-946257109897592041151821),(-877623247933902113804650),true⟩⟩
  | 3,1 => ⟨⟨1200088534471308056964110,1272445248115138704962424,true⟩,⟨(-974125189860383432292924),(-903073722760007038811005),true⟩⟩
  | 3,2 => ⟨⟨1371196025936904791855418,1447103540633261380394687,true⟩,⟨(-1014695314383447707347353),(-940794307128761723724351),true⟩⟩
  | 3,3 => ⟨⟨1473503146855432244799927,1551951636185799816075176,true⟩,⟨(-1049450928526183158182163),(-973372843288136650796817),true⟩⟩
  | 3,4 => ⟨⟨730190712815919117507150,796526035967291779344039,true⟩,⟨(-935682640494941968986557),(-868306106535606277882536),true⟩⟩
  | 3,5 => ⟨⟨481717050653881663632791,546839193760316238217093,true⟩,⟨(-934285754181646612026689),(-866781639728528861120210),true⟩⟩
  | 3,6 => ⟨⟨268100181508432441598136,333577030987925227608094,true⟩,⟨(-932100590962146585939458),(-863219617704062476605569),true⟩⟩
  | 3,7 => ⟨⟨128890877544286013832101,197009360860869784337720,true⟩,⟨(-927861158756328827437314),(-856314613530493424395217),true⟩⟩
  | 4,0 => ⟨⟨2214567229911051327779470,2338765694989483498531160,true⟩,⟨(-1755183148379190090503305),(-1632674597381839514615851),true⟩⟩
  | 4,1 => ⟨⟨2376685771795430705206244,2524613777200304072018149,true⟩,⟨(-2204055722420885565179732),(-2055598546557424805830371),true⟩⟩
  | 4,2 => ⟨⟨2441522134350940641499855,2614032495515793235198905,true⟩,⟨(-2697797549798670954691186),(-2521487875155143068324510),true⟩⟩
  | 4,3 => ⟨⟨2428312915154023398941850,2618697623244094308078838,true⟩,⟨(-3068898884274980512887314),(-2871772655782276440265486),true⟩⟩
  | 4,4 => ⟨⟨2001415953912124320508326,2106836743565170981027121,true⟩,⟨(-1430485115095855910597508),(-1327738169575594149173817),true⟩⟩
  | 4,5 => ⟨⟨1791873636933960255182695,1884213559741168184607176,true⟩,⟨(-1229291757478009040412929),(-1139802968988622008666604),true⟩⟩
  | 4,6 => ⟨⟨1624258729398947952603163,1708460577522365939690901,true⟩,⟨(-1119560124297891040760685),(-1038046964012508366080572),true⟩⟩
  | 4,7 => ⟨⟨1522898839573493745701779,1602946972890389522446437,true⟩,⟨(-1069739396946247047184698),(-992195325768567441635194),true⟩⟩
  | 5,0 => ⟨⟨2171638235049944515839801,2406711138896854108084316,true⟩,⟨(-4021511809934295019736349),(-3770358061904182346966326),true⟩⟩
  | 5,1 => ⟨⟨2031146512912484810883694,2279262900644955669904384,true⟩,⟨(-4302464601039854448900412),(-4035002691365729530827117),true⟩⟩
  | 5,2 => ⟨⟨1890234962791012408819710,2149065483250705348853475,true⟩,⟨(-4533065067691850194331074),(-4252016545806411690361785),true⟩⟩
  | 5,3 => ⟨⟨1791006012972224491198930,2056427636825925864804017,true⟩,⟨(-4674577108591004306477105),(-4385081536661904321062743),true⟩⟩
  | 5,4 => ⟨⟨2282735132171714266917827,2504520156551392183047402,true⟩,⟨(-3735940986301981299537785),(-3501147310559177253290164),true⟩⟩
  | 5,5 => ⟨⟨2355476511522396102362145,2565586630365710991012301,true⟩,⟨(-3486283217809443663905998),(-3265656818106050218470342),true⟩⟩
  | 5,6 => ⟨⟨2395392655259542598714654,2596757612877640968908258,true⟩,⟨(-3300422417618201162580435),(-3090282374807815018967085),true⟩⟩
  | 5,7 => ⟨⟨2412919939185008701206841,2609225482153429935361413,true⟩,⟨(-3193459592113473198493351),(-2989337144835567718911718),true⟩⟩
  | 6,0 => ⟨⟨625857589307296757781494,950383477478644461558488,true⟩,⟨(-5699232396234840590994353),(-5338405678932855910137159),true⟩⟩
  | 6,1 => ⟨⟨143681446668568856456486,491637316653721182699466,true⟩,⟨(-5929039549563999472314412),(-5544748265370256510587835),true⟩⟩
  | 6,2 => ⟨⟨(-289558014405879620216351),77804203436878203887457,true⟩,⟨(-6071379127161086863110268),(-5669219226369523614068716),true⟩⟩
  | 6,3 => ⟨⟨(-571902450540663479785732),(-192321328331511157740420),true⟩,⟨(-6135215957888028419102250),(-5722857988461123514369850),true⟩⟩
  | 6,4 => ⟨⟨1063947355583361699134226,1365621227775251117737654,true⟩,⟨(-5411026051654168451569441),(-5074760084242324150786752),true⟩⟩
  | 6,5 => ⟨⟨1400145079671156427485726,1686578644386007191016896,true⟩,⟨(-5121761668201926834954794),(-4804852848506608730076372),true⟩⟩
  | 6,6 => ⟨⟨1621966334105693840533846,1897293660949688587618087,true⟩,⟨(-4886348492643298614045439),(-4584024685813846117803078),true⟩⟩
  | 6,7 => ⟨⟨1738705961194426944324679,2007352508709768098395601,true⟩,⟨(-4743662678723653004460112),(-4450008615747475585433084),true⟩⟩
  | 7,0 => ⟨⟨(-3002075299673881064145646),(-2542284949367023335855619),true⟩,⟨(-5813978161366067676314721),(-5358117621559618143422462),true⟩⟩
  | 7,1 => ⟨⟨(-3674889269297723176766112),(-3202602991408970141270065),true⟩,⟨(-5399642445982901012809484),(-4948954384988639101128171),true⟩⟩
  | 7,2 => ⟨⟨(-4155389676487183921792583),(-3678646679470443212978069),true⟩,⟨(-4962228599770467384441965),(-4523081403997364831656019),true⟩⟩
  | 7,3 => ⟨⟨(-4412180777847348758258216),(-3935490588563576880235396),true⟩,⟨(-4654732696261243838396234),(-4225926774990965523819957),true⟩⟩
  | 7,4 => ⟨⟨(-2244998140352794532041192),(-1805085781526770825602106),true⟩,⟨(-6087338961370242410776467),(-5636053378157030720274247),true⟩⟩
  | 7,5 => ⟨⟨(-1546319938003679688358731),(-1129001415638632134006059),true⟩,⟨(-6195092843676023765742083),(-5755592311619301623341395),true⟩⟩
  | 7,6 => ⟨⟨(-1017618626782087990418762),(-619866717673708712479149),true⟩,⟨(-6192818439855660778265094),(-5766522037882061390300792),true⟩⟩
  | 7,7 => ⟨⟨(-714243111323189597457795),(-328686792166420037999021),true⟩,⟨(-6159248949334496488057968),(-5742157050295935281364817),true⟩⟩
  | 8,0 => ⟨⟨(-5128800864297972457832099),(-4728183653645931060721902),true⟩,⟨(-1759509934943153764213454),(-1479163596899706031148122),true⟩⟩
  | 8,1 => ⟨⟨(-4907410163200310989950625),(-4549469392307639528039766),true⟩,⟨(-966686170316619479500046),(-740269038445273320685425),true⟩⟩
  | 8,2 => ⟨⟨(-4625144506717710092573421),(-4304732207705739128629909),true⟩,⟨(-411122815965219773257074),(-226316782393505359837226),true⟩⟩
  | 8,3 => ⟨⟨(-4418983470357657936911717),(-4122386630105360975066390),true⟩,⟨(-115400833895930663166243),46781325686223014542224,true⟩⟩
  | 8,4 => ⟨⟨(-5165288889057656162750423),(-4727838844582702558004083),true⟩,⟨(-2670975582771772145699550),(-2335558962295578874824319),true⟩⟩
  | 8,5 => ⟨⟨(-4998728454056761662419937),(-4537474992943400031164904),true⟩,⟨(-3516594628477762589779571),(-3136620811612625636857217),true⟩⟩
  | 8,6 => ⟨⟨(-4735295460941245866864708),(-4262904431521084390725088),true⟩,⟨(-4144940826614977702545969),(-3736212338524171909244204),true⟩⟩
  | 8,7 => ⟨⟨(-4525974755665380168665916),(-4050118132900759912355428),true⟩,⟨(-4494682622185087225718272),(-4071821867612217854721768),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP549Value0_0 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP549Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value0_1 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP549Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value0_2 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP549Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value0_3 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP549Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value0_4 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP549Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value0_5 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP549Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value0_6 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP549Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value0_7 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP549Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP549Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 0 j)=sharedDiskP549Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP549Value0_0
  · exact sharedDiskP549Value0_1
  · exact sharedDiskP549Value0_2
  · exact sharedDiskP549Value0_3
  · exact sharedDiskP549Value0_4
  · exact sharedDiskP549Value0_5
  · exact sharedDiskP549Value0_6
  · exact sharedDiskP549Value0_7
private theorem sharedDiskP549Value1_0 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP549Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value1_1 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP549Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value1_2 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP549Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value1_3 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP549Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value1_4 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP549Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value1_5 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP549Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value1_6 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP549Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value1_7 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP549Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP549Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 1 j)=sharedDiskP549Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP549Value1_0
  · exact sharedDiskP549Value1_1
  · exact sharedDiskP549Value1_2
  · exact sharedDiskP549Value1_3
  · exact sharedDiskP549Value1_4
  · exact sharedDiskP549Value1_5
  · exact sharedDiskP549Value1_6
  · exact sharedDiskP549Value1_7
private theorem sharedDiskP549Value2_0 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP549Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value2_1 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP549Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value2_2 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP549Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value2_3 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP549Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value2_4 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP549Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value2_5 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP549Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value2_6 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP549Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value2_7 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP549Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP549Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 2 j)=sharedDiskP549Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP549Value2_0
  · exact sharedDiskP549Value2_1
  · exact sharedDiskP549Value2_2
  · exact sharedDiskP549Value2_3
  · exact sharedDiskP549Value2_4
  · exact sharedDiskP549Value2_5
  · exact sharedDiskP549Value2_6
  · exact sharedDiskP549Value2_7
private theorem sharedDiskP549Value3_0 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP549Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value3_1 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP549Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value3_2 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP549Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value3_3 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP549Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value3_4 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP549Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value3_5 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP549Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value3_6 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP549Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value3_7 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP549Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP549Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 3 j)=sharedDiskP549Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP549Value3_0
  · exact sharedDiskP549Value3_1
  · exact sharedDiskP549Value3_2
  · exact sharedDiskP549Value3_3
  · exact sharedDiskP549Value3_4
  · exact sharedDiskP549Value3_5
  · exact sharedDiskP549Value3_6
  · exact sharedDiskP549Value3_7
private theorem sharedDiskP549Value4_0 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP549Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value4_1 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP549Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value4_2 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP549Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value4_3 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP549Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value4_4 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP549Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value4_5 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP549Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value4_6 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP549Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value4_7 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP549Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP549Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 4 j)=sharedDiskP549Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP549Value4_0
  · exact sharedDiskP549Value4_1
  · exact sharedDiskP549Value4_2
  · exact sharedDiskP549Value4_3
  · exact sharedDiskP549Value4_4
  · exact sharedDiskP549Value4_5
  · exact sharedDiskP549Value4_6
  · exact sharedDiskP549Value4_7
private theorem sharedDiskP549Value5_0 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP549Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value5_1 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP549Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value5_2 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP549Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value5_3 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP549Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value5_4 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP549Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value5_5 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP549Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value5_6 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP549Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value5_7 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP549Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP549Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 5 j)=sharedDiskP549Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP549Value5_0
  · exact sharedDiskP549Value5_1
  · exact sharedDiskP549Value5_2
  · exact sharedDiskP549Value5_3
  · exact sharedDiskP549Value5_4
  · exact sharedDiskP549Value5_5
  · exact sharedDiskP549Value5_6
  · exact sharedDiskP549Value5_7
private theorem sharedDiskP549Value6_0 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP549Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value6_1 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP549Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value6_2 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP549Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value6_3 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP549Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value6_4 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP549Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value6_5 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP549Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value6_6 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP549Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value6_7 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP549Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP549Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 6 j)=sharedDiskP549Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP549Value6_0
  · exact sharedDiskP549Value6_1
  · exact sharedDiskP549Value6_2
  · exact sharedDiskP549Value6_3
  · exact sharedDiskP549Value6_4
  · exact sharedDiskP549Value6_5
  · exact sharedDiskP549Value6_6
  · exact sharedDiskP549Value6_7
private theorem sharedDiskP549Value7_0 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP549Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value7_1 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP549Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value7_2 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP549Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value7_3 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP549Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value7_4 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP549Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value7_5 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP549Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value7_6 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP549Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value7_7 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP549Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP549Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 7 j)=sharedDiskP549Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP549Value7_0
  · exact sharedDiskP549Value7_1
  · exact sharedDiskP549Value7_2
  · exact sharedDiskP549Value7_3
  · exact sharedDiskP549Value7_4
  · exact sharedDiskP549Value7_5
  · exact sharedDiskP549Value7_6
  · exact sharedDiskP549Value7_7
private theorem sharedDiskP549Value8_0 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP549Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value8_1 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP549Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value8_2 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP549Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value8_3 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP549Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value8_4 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP549Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value8_5 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP549Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value8_6 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP549Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP549Value8_7 : truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP549Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP549Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points 8 j)=sharedDiskP549Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP549Value8_0
  · exact sharedDiskP549Value8_1
  · exact sharedDiskP549Value8_2
  · exact sharedDiskP549Value8_3
  · exact sharedDiskP549Value8_4
  · exact sharedDiskP549Value8_5
  · exact sharedDiskP549Value8_6
  · exact sharedDiskP549Value8_7
theorem sharedDiskP549Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP549Params (sharedChord521Gauss8Points i j)=sharedDiskP549Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP549Values0_eq
  · exact sharedDiskP549Values1_eq
  · exact sharedDiskP549Values2_eq
  · exact sharedDiskP549Values3_eq
  · exact sharedDiskP549Values4_eq
  · exact sharedDiskP549Values5_eq
  · exact sharedDiskP549Values6_eq
  · exact sharedDiskP549Values7_eq
  · exact sharedDiskP549Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP549Box : HorizontalRectangle := ⟨(671/800),(21/25),(964399421498729/1649267441664000),(966010034234729/1649267441664000),(1029012968532376862680971659342709/10384593717069655257060992658440192),(4687540886225801732539827552678773/10384593717069655257060992658440192),(-2087129035529297474999952469924215/649037107316853453566312041152512),(-1851466009169980648459840674339191/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP549Grid : CGrid := momentChordGrid sharedDiskP549Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP549Columns : containedInReported sharedDiskP549Grid.re sharedDiskP549Box.reLo sharedDiskP549Box.reHi=true ∧ containedInReported sharedDiskP549Grid.im sharedDiskP549Box.imLo sharedDiskP549Box.imHi=true := by
  rw [sharedDiskP549Grid,momentChordGrid_eq_tabulated sharedDiskP549Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP549Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP549Values_eq]
  decide +kernel
theorem sharedDiskP549Sound : sharedDiskP549Box.Sound := by
  intro t a tl tu al au
  change (((671/800):ℚ):ℝ)≤t at tl
  change t≤(((21/25):ℚ):ℝ) at tu
  change (((964399421498729/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((966010034234729/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP549Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(671/800))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((21/25):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(964399421498729/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((966010034234729/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP549Columns.1 sharedDiskP549Columns.2
def sharedDiskP549Rows : List SignRow := [positive_549.toSignRow]
theorem sharedDiskP549Rows_actual : ∀ r∈sharedDiskP549Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP549Rows.all (sharedDiskP549Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP549Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP550Params : ChordParams := ⟨⟨(-28877231036482020019682),(-28717199748898103468864),true⟩,⟨1868593443905575199459846,1875789491247738837435614,true⟩,⟨135025088623651703960183,135960528092338100030166,true⟩,⟨256177558392548859152790,257706984980996436890497,true⟩,⟨363956073583807584748398,365015958691081554810423,true⟩,⟨1152518735821102584590052,1152824078320395112196760,true⟩,⟨(-2155775985317129589924545),(-2152002611340369426266370),true⟩,⟨⟨1141560376315807192686005,1156037934095691119906071,true⟩,⟨(-75524128),75524128,true⟩⟩⟩
theorem sharedDiskP550Params_ok : chordParams (Grid.ofRats (21/25) (673/800)) (Grid.ofRats (193006595818139/329853488332800) (193328718365339/329853488332800))=sharedDiskP550Params := by decide +kernel
def sharedDiskP550Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3030638524960548125440922),(-2739563582733678789678295),true⟩,⟨(-219742055694199922900091),18425834563056469086888,true⟩⟩
  | 0,1 => ⟨⟨(-2704437273683214769188593),(-2435603367071652307627938),true⟩,⟨(-273731564683050912512208),(-47536550438961669028044),true⟩⟩
  | 0,2 => ⟨⟨(-2467835778794972925524315),(-2216728109193569880789118),true⟩,⟨(-321617462797852383913345),(-106574813007593756088677),true⟩⟩
  | 0,3 => ⟨⟨(-2334263513686102089597486),(-2093533978670382226254925),true⟩,⟨(-351735625803543097702266),(-143521797435920611339434),true⟩⟩
  | 0,4 => ⟨⟨(-3415129267641672753795980),(-3101549297843525414017380),true⟩,⟨(-174985802358386220930260),71619372511224408704738,true⟩⟩
  | 0,5 => ⟨⟨(-3804823766324912020913884),(-3472739990149463988205295),true⟩,⟨(-151306439389522399863028),97611285114014545511296,true⟩⟩
  | 0,6 => ⟨⟨(-4133149995209190974964401),(-3788827917353822436404277),true⟩,⟨(-148768531390010577584295),97540627218556847134825,true⟩⟩
  | 0,7 => ⟨⟨(-4338706288245480580329601),(-3988157206084480944581528),true⟩,⟨(-157066684505746648114709),86477604456640050554218,true⟩⟩
  | 1,0 => ⟨⟨(-1522343171518541800889473),(-1350186855444066614088342),true⟩,⟨(-572378462888405289510245),(-415511885624582485148280),true⟩⟩
  | 1,1 => ⟨⟨(-1343498570554724255427784),(-1186879037101518924741348),true⟩,⟨(-625976591448424644218320),(-481696964400069509166422),true⟩⟩
  | 1,2 => ⟨⟨(-1213362719653033973122685),(-1067900317726085549386667),true⟩,⟨(-664837627560950329452131),(-529722038352539613622138),true⟩⟩
  | 1,3 => ⟨⟨(-1139260755839447252227517),(-1000058494677779948834956),true⟩,⟨(-686684691751823884984603),(-556747941372023937097102),true⟩⟩
  | 1,4 => ⟨⟨(-1734997943242267647246149),(-1544323298874365520841464),true⟩,⟨(-509817024185116495152862),(-338293119858180629638706),true⟩⟩
  | 1,5 => ⟨⟨(-1955660526559658229253163),(-1746032940724268976752785),true⟩,⟨(-447799360929304499070821),(-261786951414188713509141),true⟩⟩
  | 1,6 => ⟨⟨(-2147810153980815334573949),(-1922119970446141011698811),true⟩,⟨(-397194269653108354343597),(-199429399443635195420976),true⟩⟩
  | 1,7 => ⟨⟨(-2271795951895170092231030),(-2036037394324430299007007),true⟩,⟨(-366536710160902416675244),(-161709541809794970813493),true⟩⟩
  | 2,0 => ⟨⟨(-312561716421087076513653),(-229583604420981017077266),true⟩,⟨(-883988644491969917618819),(-800025257326457817749828),true⟩⟩
  | 2,1 => ⟨⟨(-135019113850194891967222),(-59213821492519324027704),true⟩,⟨(-907543494634658565991355),(-829253981154764174646100),true⟩⟩
  | 2,2 => ⟨⟨(-4909949275225942461054),66619605772668999591367,true⟩,⟨(-919526399298040185730679),(-844787882132642427052141),true⟩⟩
  | 2,3 => ⟨⟨69724200260700492203689,139294622068629377989731,true⟩,⟨(-924522011103939712673067),(-851598719020917516141906),true⟩⟩
  | 2,4 => ⟨⟨(-524299239863791833424500),(-430919736112019230085895),true⟩,⟨(-845073600922429230557917),(-753072653891296206384768),true⟩⟩
  | 2,5 => ⟨⟨(-749281878227309307453697),(-641228502807875775287024),true⟩,⟨(-793364083451369731376122),(-689477262557184333326874),true⟩⟩
  | 2,6 => ⟨⟨(-952005099293259591671076),(-828197385836106084121664),true⟩,⟨(-740128436240906332001092),(-623016905358930668325642),true⟩⟩
  | 2,7 => ⟨⟨(-1087241976357256767810275),(-952383017801885800162871),true⟩,⟨(-701826030847309053627561),(-575495780604048731065690),true⟩⟩
  | 3,0 => ⟨⟨971364719911594343361410,1040323607425844726114745,true⟩,⟨(-948335077076618986989587),(-879590256935945081614181),true⟩⟩
  | 3,1 => ⟨⟨1192431537479231556882559,1264862583328066910345433,true⟩,⟨(-976886681661670358509849),(-905711497687742337671108),true⟩⟩
  | 3,2 => ⟨⟨1363431147928914146051344,1439424353536443897634155,true⟩,⟨(-1017991389302213160923679),(-943952438790437700279145),true⟩⟩
  | 3,3 => ⟨⟨1465670321747917428496030,1544213339866485175347826,true⟩,⟨(-1053074402015092734007954),(-976848020889480379998509),true⟩⟩
  | 3,4 => ⟨⟨722942522859585636300985,789344199407040666582968,true⟩,⟨(-936983507796371590598728),(-869502709859792438885699),true⟩⟩
  | 3,5 => ⟨⟨474794677977418131345858,539993774352967964116082,true⟩,⟨(-934795209290904131153840),(-867184979386536312674455),true⟩⟩
  | 3,6 => ⟨⟨261464000303626258589278,327083801778940586919564,true⟩,⟨(-931962957027209895107653),(-862933317437227194918830),true⟩⟩
  | 3,7 => ⟨⟨122489547224294003041388,190814455906508029100789,true⟩,⟨(-927291761077313900865957),(-855555421686510336550339),true⟩⟩
  | 4,0 => ⟨⟨2205058660649379995655450,2329435955238507820593163,true⟩,⟨(-1761680852135232967436502),(-1638907075488933291678184),true⟩⟩
  | 4,1 => ⟨⟨2365629394439323111549592,2513767117035660199866258,true⟩,⟨(-2211390049811289907133165),(-2062621429868704489373448),true⟩⟩
  | 4,2 => ⟨⟨2428495735534753242794876,2601232478168021859565256,true⟩,⟨(-2705510804155859277090976),(-2528859049786927283430736),true⟩⟩
  | 4,3 => ⟨⟨2413685515844368062429678,2604297120407155295190439,true⟩,⟨(-3076533399695092817895345),(-2879056504788848763517207),true⟩⟩
  | 4,4 => ⟨⟨1992816082346948539555178,2098383421143339531852079,true⟩,⟨(-1436027760480541949300631),(-1333060640185363650049045),true⟩⟩
  | 4,5 => ⟨⟨1783718364074071918661545,1876179966131640322522812,true⟩,⟨(-1234012498404314292583006),(-1144337645616525592138589),true⟩⟩
  | 4,6 => ⟨⟨1616304512799980886611891,1700612518884668578638840,true⟩,⟨(-1123685390843306989454177),(-1042007804148137403038078),true⟩⟩
  | 4,7 => ⟨⟨1515029993568415606892109,1595176674366539409748688,true⟩,⟨(-1073524352490754977413463),(-995826825532105158659056),true⟩⟩
  | 5,0 => ⟨⟨2152715468505242316466419,2387965203385375083218353,true⟩,⟨(-4027404259353195445855933),(-3775942878525230773100416),true⟩⟩
  | 5,1 => ⟨⟨2010978461633301490723854,2259240814669709363869587,true⟩,⟨(-4307362917130932931071638),(-4039627389677099659118371),true⟩⟩
  | 5,2 => ⟨⟨1869079944988797503278583,2128024599824164492915623,true⟩,⟨(-4536954449522428541313351),(-4255669165313826391964091),true⟩⟩
  | 5,3 => ⟨⟨1769268549680946674988774,2034781553457203063653342,true⟩,⟨(-4677751927608239273288665),(-4388046715309214863012543),true⟩⟩
  | 5,4 => ⟨⟨2265103446079580583464794,2487088660287986200758107,true⟩,⟨(-3742605211943964648556173),(-3507480123161440830187552),true⟩⟩
  | 5,5 => ⟨⟨2338978330193117113094398,2549302998922453658932580,true⟩,⟨(-3493441206407541737966376),(-3272470588065888474604311),true⟩⟩
  | 5,6 => ⟨⟨2379733576026502600293196,2581320328121909223571412,true⟩,⟨(-3307844929567196881988928),(-3097355583792275953995911),true⟩⟩
  | 5,7 => ⟨⟨2397739831950435903851057,2594270057428167912299746,true⟩,⟨(-3200995966608296262000546),(-2996522919350039092612675),true⟩⟩
  | 6,0 => ⟨⟨600899346258093104867081,925749216275155879720779,true⟩,⟨(-5694287720484242994412470),(-5333300738940891015121955),true⟩⟩
  | 6,1 => ⟨⟨118821870725177242611506,467002282374852047964087,true⟩,⟨(-5920856019295092347051104),(-5536554882339454725032170),true⟩⟩
  | 6,2 => ⟨⟨(-313886173006555372994941),53644268544143948545015,true⟩,⟨(-6060418267024266652944823),(-5658389496225523629497886),true⟩⟩
  | 6,3 => ⟨⟨(-595632998582523829069819),(-215912201905288819993228),true⟩,⟨(-6122524959586596219283203),(-5710391926250352620491010),true⟩⟩
  | 6,4 => ⟨⟨1039478535318635597994974,1341316810287662466524079,true⟩,⟨(-5409124692512121135040613),(-5072716026478991282092072),true⟩⟩
  | 6,5 => ⟨⟨1376749722628947886725857,1663183622010263601505847,true⟩,⟨(-5122113716984199046700612),(-4805108305253371879305778),true⟩⟩
  | 6,6 => ⟨⟨1599402512890071184021739,1874782039528914950198246,true⟩,⟨(-4888302466185050607232929),(-4585816885982335467171348),true⟩⟩
  | 6,7 => ⟨⟨1716692282301920246695399,1985418134692674149606322,true⟩,⟨(-4746460078771893659359215),(-4452610982920105881795533),true⟩⟩
  | 7,0 => ⟨⟨(-3014328144774315400941903),(-2555122825690480135787221),true⟩,⟨(-5790291517932657381432544),(-5335444951281452845697413),true⟩⟩
  | 7,1 => ⟨⟨(-3682011967968128652530745),(-3210533295402227813002885),true⟩,⟨(-5374874346560971936477875),(-4925374710967467874333838),true⟩⟩
  | 7,2 => ⟨⟨(-4158241871464553781159070),(-3682464138528564709589062),true⟩,⟨(-4937654131674272660175087),(-4499786679476707079109752),true⟩⟩
  | 7,3 => ⟨⟨(-4412493209476917180816268),(-3936849311602651386747161),true⟩,⟨(-4630763274030693656380664),(-4203266375569783472738296),true⟩⟩
  | 7,4 => ⟨⟨(-2261991009133983116725247),(-1822420471367110406375055),true⟩,⟨(-6066132176008455766209464),(-5615629187857133330343209),true⟩⟩
  | 7,5 => ⟨⟨(-1566762555990062015712668),(-1149573632697296558752118),true⟩,⟨(-6177024285485791057433810),(-5738076452564078742598827),true⟩⟩
  | 7,6 => ⟨⟨(-1040073214751484020228691),(-642300441187658779441121),true⟩,⟨(-6177543287917238171911690),(-5751621618194585969819930),true⟩⟩
  | 7,7 => ⟨⟨(-737609426181350653037600),(-351950508916990278197202),true⟩,⟨(-6145712090974578847880791),(-5728892807109429168543633),true⟩⟩
  | 8,0 => ⟨⟨(-5117603107559352612332294),(-4718051614932549342827516),true⟩,⟨(-1749324929303264397711935),(-1469810261432067119045396),true⟩⟩
  | 8,1 => ⟨⟨(-4896584086614849126660050),(-4539510507635336445312303),true⟩,⟨(-961234447145041278431531),(-735362486255798028060309),true⟩⟩
  | 8,2 => ⟨⟨(-4615600431983530615093159),(-4295866222628236259310474),true⟩,⟨(-408887683683082949841291),(-224413858510565166864022),true⟩⟩
  | 8,3 => ⟨⟨(-4410527557255653294668144),(-4114484747220709955378233),true⟩,⟨(-114774163193494886523872),47213076283388182051356,true⟩⟩
  | 8,4 => ⟨⟨(-5155555828479678557835869),(-4719290514764582000484845),true⟩,⟨(-2655539047136630232694348),(-2321213445797827877776754),true⟩⟩
  | 8,5 => ⟨⟨(-4992080193202176628831264),(-4532023127015779703823723),true⟩,⟨(-3496830282472788408318269),(-3118109502257701530771786),true⟩⟩
  | 8,6 => ⟨⟨(-4732057156913510043567366),(-4260805746850088976417471),true⟩,⟨(-4122546042716719164792429),(-3715129046014022295814238),true⟩⟩
  | 8,7 => ⟨⟨(-4525089582069222509789331),(-4050313637042401498234587),true⟩,⟨(-4471140335702373211692610),(-4049594984062665447389847),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP550Value0_0 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP550Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value0_1 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP550Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value0_2 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP550Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value0_3 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP550Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value0_4 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP550Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value0_5 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP550Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value0_6 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP550Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value0_7 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP550Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP550Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 0 j)=sharedDiskP550Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP550Value0_0
  · exact sharedDiskP550Value0_1
  · exact sharedDiskP550Value0_2
  · exact sharedDiskP550Value0_3
  · exact sharedDiskP550Value0_4
  · exact sharedDiskP550Value0_5
  · exact sharedDiskP550Value0_6
  · exact sharedDiskP550Value0_7
private theorem sharedDiskP550Value1_0 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP550Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value1_1 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP550Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value1_2 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP550Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value1_3 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP550Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value1_4 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP550Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value1_5 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP550Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value1_6 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP550Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value1_7 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP550Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP550Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 1 j)=sharedDiskP550Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP550Value1_0
  · exact sharedDiskP550Value1_1
  · exact sharedDiskP550Value1_2
  · exact sharedDiskP550Value1_3
  · exact sharedDiskP550Value1_4
  · exact sharedDiskP550Value1_5
  · exact sharedDiskP550Value1_6
  · exact sharedDiskP550Value1_7
private theorem sharedDiskP550Value2_0 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP550Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value2_1 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP550Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value2_2 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP550Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value2_3 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP550Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value2_4 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP550Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value2_5 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP550Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value2_6 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP550Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value2_7 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP550Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP550Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 2 j)=sharedDiskP550Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP550Value2_0
  · exact sharedDiskP550Value2_1
  · exact sharedDiskP550Value2_2
  · exact sharedDiskP550Value2_3
  · exact sharedDiskP550Value2_4
  · exact sharedDiskP550Value2_5
  · exact sharedDiskP550Value2_6
  · exact sharedDiskP550Value2_7
private theorem sharedDiskP550Value3_0 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP550Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value3_1 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP550Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value3_2 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP550Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value3_3 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP550Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value3_4 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP550Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value3_5 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP550Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value3_6 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP550Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value3_7 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP550Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP550Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 3 j)=sharedDiskP550Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP550Value3_0
  · exact sharedDiskP550Value3_1
  · exact sharedDiskP550Value3_2
  · exact sharedDiskP550Value3_3
  · exact sharedDiskP550Value3_4
  · exact sharedDiskP550Value3_5
  · exact sharedDiskP550Value3_6
  · exact sharedDiskP550Value3_7
private theorem sharedDiskP550Value4_0 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP550Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value4_1 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP550Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value4_2 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP550Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value4_3 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP550Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value4_4 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP550Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value4_5 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP550Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value4_6 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP550Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value4_7 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP550Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP550Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 4 j)=sharedDiskP550Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP550Value4_0
  · exact sharedDiskP550Value4_1
  · exact sharedDiskP550Value4_2
  · exact sharedDiskP550Value4_3
  · exact sharedDiskP550Value4_4
  · exact sharedDiskP550Value4_5
  · exact sharedDiskP550Value4_6
  · exact sharedDiskP550Value4_7
private theorem sharedDiskP550Value5_0 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP550Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value5_1 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP550Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value5_2 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP550Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value5_3 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP550Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value5_4 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP550Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value5_5 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP550Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value5_6 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP550Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value5_7 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP550Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP550Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 5 j)=sharedDiskP550Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP550Value5_0
  · exact sharedDiskP550Value5_1
  · exact sharedDiskP550Value5_2
  · exact sharedDiskP550Value5_3
  · exact sharedDiskP550Value5_4
  · exact sharedDiskP550Value5_5
  · exact sharedDiskP550Value5_6
  · exact sharedDiskP550Value5_7
private theorem sharedDiskP550Value6_0 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP550Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value6_1 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP550Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value6_2 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP550Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value6_3 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP550Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value6_4 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP550Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value6_5 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP550Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value6_6 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP550Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value6_7 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP550Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP550Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 6 j)=sharedDiskP550Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP550Value6_0
  · exact sharedDiskP550Value6_1
  · exact sharedDiskP550Value6_2
  · exact sharedDiskP550Value6_3
  · exact sharedDiskP550Value6_4
  · exact sharedDiskP550Value6_5
  · exact sharedDiskP550Value6_6
  · exact sharedDiskP550Value6_7
private theorem sharedDiskP550Value7_0 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP550Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value7_1 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP550Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value7_2 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP550Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value7_3 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP550Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value7_4 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP550Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value7_5 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP550Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value7_6 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP550Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value7_7 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP550Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP550Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 7 j)=sharedDiskP550Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP550Value7_0
  · exact sharedDiskP550Value7_1
  · exact sharedDiskP550Value7_2
  · exact sharedDiskP550Value7_3
  · exact sharedDiskP550Value7_4
  · exact sharedDiskP550Value7_5
  · exact sharedDiskP550Value7_6
  · exact sharedDiskP550Value7_7
private theorem sharedDiskP550Value8_0 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP550Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value8_1 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP550Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value8_2 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP550Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value8_3 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP550Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value8_4 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP550Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value8_5 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP550Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value8_6 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP550Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP550Value8_7 : truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP550Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP550Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points 8 j)=sharedDiskP550Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP550Value8_0
  · exact sharedDiskP550Value8_1
  · exact sharedDiskP550Value8_2
  · exact sharedDiskP550Value8_3
  · exact sharedDiskP550Value8_4
  · exact sharedDiskP550Value8_5
  · exact sharedDiskP550Value8_6
  · exact sharedDiskP550Value8_7
theorem sharedDiskP550Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP550Params (sharedChord521Gauss8Points i j)=sharedDiskP550Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP550Values0_eq
  · exact sharedDiskP550Values1_eq
  · exact sharedDiskP550Values2_eq
  · exact sharedDiskP550Values3_eq
  · exact sharedDiskP550Values4_eq
  · exact sharedDiskP550Values5_eq
  · exact sharedDiskP550Values6_eq
  · exact sharedDiskP550Values7_eq
  · exact sharedDiskP550Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP550Box : HorizontalRectangle := ⟨(21/25),(673/800),(193006595818139/329853488332800),(193328718365339/329853488332800),(14118704369282239281274624083387/162259276829213363391578010288128),(70946942406578514367561456879035/162259276829213363391578010288128),(-2085837680207016372904072459248145/649037107316853453566312041152512),(-1851508369523886621116939416298001/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP550Grid : CGrid := momentChordGrid sharedDiskP550Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP550Columns : containedInReported sharedDiskP550Grid.re sharedDiskP550Box.reLo sharedDiskP550Box.reHi=true ∧ containedInReported sharedDiskP550Grid.im sharedDiskP550Box.imLo sharedDiskP550Box.imHi=true := by
  rw [sharedDiskP550Grid,momentChordGrid_eq_tabulated sharedDiskP550Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP550Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP550Values_eq]
  decide +kernel
theorem sharedDiskP550Sound : sharedDiskP550Box.Sound := by
  intro t a tl tu al au
  change (((21/25):ℚ):ℝ)≤t at tl
  change t≤(((673/800):ℚ):ℝ) at tu
  change (((193006595818139/329853488332800):ℚ):ℝ)≤a at al
  change a≤(((193328718365339/329853488332800):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP550Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(21/25))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((673/800):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(193006595818139/329853488332800))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((193328718365339/329853488332800):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP550Columns.1 sharedDiskP550Columns.2
def sharedDiskP550Rows : List SignRow := [positive_550.toSignRow]
theorem sharedDiskP550Rows_actual : ∀ r∈sharedDiskP550Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP550Rows.all (sharedDiskP550Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP550Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP547Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP548Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP549Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP550Rows_actual
