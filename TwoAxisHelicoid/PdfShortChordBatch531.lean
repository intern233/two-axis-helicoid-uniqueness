import TwoAxisHelicoid.PdfSharedChord521Gauss8
import TwoAxisHelicoid.PdfSharedChord521Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP531Params : ChordParams := ⟨⟨(-24407438008109296679509),(-24112497901100355923581),true⟩,⟨2002105438883700773949840,2017585986575015696978664,true⟩,⟨126975263675828991986674,128845368346006969177329,true⟩,⟨227825384861668510310357,230761495145130001199049,true⟩,⟨334711114647531821062611,336832508783440639740073,true⟩,⟨1161076981003852740738048,1161643880563822812207394,true⟩,⟨(-2273776873063454797938410),(-2265609263213614712872163),true⟩,⟨⟨1144514487143120242486624,1172978916327169963122369,true⟩,⟨(-12576423),12576423,true⟩⟩⟩
theorem sharedDiskP531Params_ok : chordParams (Grid.ofRats (321/400) (161/200)) (Grid.ofRats (946164923013499/1649267441664000) (949386148485499/1649267441664000))=sharedDiskP531Params := by decide +kernel
def sharedDiskP531Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3180690478560360218797015),(-2666561045532544603217126),true⟩,⟨(-341139117990751085322082),70685291548948928025677,true⟩⟩
  | 0,1 => ⟨⟨(-2804287572696370411370519),(-2334230657437101816720703),true⟩,⟨(-406448968847864067817464),(-17574676914770623684581),true⟩⟩
  | 0,2 => ⟨⟨(-2533754162120604193045574),(-2098321528982440444873391),true⟩,⟨(-461358480021472155709012),(-93949951544421074232641),true⟩⟩
  | 0,3 => ⟨⟨(-2382236173160472143946508),(-1966763327535626099985207),true⟩,⟨(-494810601207226487672627),(-140322723167844629222628),true⟩⟩
  | 0,4 => ⟨⟨(-3629184086561530131713767),(-3069360311523151623564781),true⟩,⟨(-281946528445873340839120),145404006398706535845904,true⟩⟩
  | 0,5 => ⟨⟨(-4088446464184227900268176),(-3489713510529040379238565),true⟩,⟨(-243986890309106172538724),188235578689345712595593,true⟩⟩
  | 0,6 => ⟨⟨(-4478279742116889298871486),(-3852897283842427202591080),true⟩,⟨(-230770653996612589095272),194193849139696305441316,true⟩⟩
  | 0,7 => ⟨⟨(-4723674347672915999557114),(-4084026932629371439535989),true⟩,⟨(-236504227914663547955736),182730778049588165422384,true⟩⟩
  | 1,0 => ⟨⟨(-1477696032851734752268699),(-1188873638008299409749982),true⟩,⟨(-720218834504784132484802),(-458025767144112994170703),true⟩⟩
  | 1,1 => ⟨⟨(-1281556091671905036242753),(-1020564493439660236317268),true⟩,⟨(-770015333739403304339839),(-529794231405058068922006),true⟩⟩
  | 1,2 => ⟨⟨(-1139375926145001139413221),(-898200464706547395860100),true⟩,⟨(-804737561909587496068576),(-580367420151193721093612),true⟩⟩
  | 1,3 => ⟨⟨(-1058591018587614366522466),(-828477998685605801171484),true⟩,⟨(-823683677257390372400653),(-608223327961494070911009),true⟩⟩
  | 1,4 => ⟨⟨(-1712223763187532651585795),(-1389837561131467259959058),true⟩,⟨(-659581670747185282208859),(-371481478942997634046437),true⟩⟩
  | 1,5 => ⟨⟨(-1957290371526305141040493),(-1600079302191098505746225),true⟩,⟨(-596945912798756456917098),(-282884232579300109313551),true⟩⟩
  | 1,6 => ⟨⟨(-2172231476276785011732713),(-1785110301794893364802667),true⟩,⟨(-543955375480414876796229),(-208583843695284547623435),true⟩⟩
  | 1,7 => ⟨⟨(-2311718481679798090776144),(-1905655009699456968745878),true⟩,⟨(-510981628481974765956211),(-162705427873252195554158),true⟩⟩
  | 2,0 => ⟨⟨(-167396829842563204249243),(-28566164922705753328223),true⟩,⟨(-967074463221198389253584),(-822716444356506981708667),true⟩⟩
  | 2,1 => ⟨⟨22233130375536529829101,150246042414456252910527,true⟩,⟨(-973693175056400495337278),(-838372195123019512540807),true⟩⟩
  | 2,2 => ⟨⟨160330949535064294507930,282338709686869270476089,true⟩,⟨(-972573216811906006822067),(-842974340316028956751934),true⟩⟩
  | 2,3 => ⟨⟨239464383226444291246627,359076976837327405971037,true⟩,⟨(-969872456995960653266243),(-842857391786815736210030),true⟩⟩
  | 2,4 => ⟨⟨(-394281738419565799596781),(-238755694901240967936055),true⟩,⟨(-946280816459925564841639),(-789242454625458840559151),true⟩⟩
  | 2,5 => ⟨⟨(-635004415288679311729844),(-458016042728182983729648),true⟩,⟨(-909855333036304435026657),(-737052939334044417026349),true⟩⟩
  | 2,6 => ⟨⟨(-854917684561430934394995),(-651862444777771220683867),true⟩,⟨(-867972203844945009154678),(-674456991236730311569190),true⟩⟩
  | 2,7 => ⟨⟨(-1001948382222646945412668),(-779488919590338587013543),true⟩,⟨(-836546300350851753725597),(-627272622186699637235152),true⟩⟩
  | 3,0 => ⟨⟨1168626082172079200137253,1297126422544225942861640,true⟩,⟨(-907911386198201092615770),(-782757057364791877297372),true⟩⟩
  | 3,1 => ⟨⟨1390126000712991000968577,1525166165581208498622659,true⟩,⟨(-917311102892639259782829),(-787920821242829608009049),true⟩⟩
  | 3,2 => ⟨⟨1560251757264922355514206,1701720679647902885873968,true⟩,⟨(-943791471186170831019949),(-809495063313025261454098),true⟩⟩
  | 3,3 => ⟨⟨1661762093177282757928300,1807754815049465890717382,true⟩,⟨(-970036050374842370634761),(-832003810393219588265207),true⟩⟩
  | 3,4 => ⟨⟨916668230738096948629632,1039829389913777741208130,true⟩,⟨(-919059053879466096073139),(-796306868606442183083401),true⟩⟩
  | 3,5 => ⟨⟨661457780432935961519434,781230527920961604031766,true⟩,⟨(-940629375869238202670921),(-818127953151893725872909),true⟩⟩
  | 3,6 => ⟨⟨439852844998154567101296,558315916311209392533911,true⟩,⟨(-958720334232889364013353),(-834833914214773366630283),true⟩⟩
  | 3,7 => ⟨⟨295306466841531583492312,413862159823498872743092,true⟩,⟨(-967154895997475904094260),(-841529865851982720580641),true⟩⟩
  | 4,0 => ⟨⟨2414603138858918793666456,2645496350500845665087813,true⟩,⟨(-1608339795042157224067969),(-1385890835851976382139730),true⟩⟩
  | 4,1 => ⟨⟨2605400840229728260193415,2880590790748199636642517,true⟩,⟨(-2038602033807252714776474),(-1768387006697744394094454),true⟩⟩
  | 4,2 => ⟨⟨2712594386413090384982954,3034345475123698839447412,true⟩,⟨(-2525798477131991776123365),(-2203457976587108172441212),true⟩⟩
  | 4,3 => ⟨⟨2736584513424936013044036,3092751623310669803298934,true⟩,⟨(-2901779695003852710031575),(-2539785860938758794221007),true⟩⟩
  | 4,4 => ⟨⟨2189164739083709743776853,2385270408475037952143966,true⟩,⟨(-1305682982604892593617662),(-1119235904312034410975915),true⟩⟩
  | 4,5 => ⟨⟨1977253377369292287414240,2149126229034024045012635,true⟩,⟨(-1123673422206366744513842),(-961293527928868640009704),true⟩⟩
  | 4,6 => ⟨⟨1810757583449212818113693,1967474540118733198026022,true⟩,⟨(-1027991013578170051362006),(-880107816900724484904469),true⟩⟩
  | 4,7 => ⟨⟨1710630158878927528969309,1859559069686639365255960,true⟩,⟨(-986293664177413945012840),(-845648428077311589487414),true⟩⟩
  | 5,0 => ⟨⟨2588362615097405451071807,3033249451385328455390653,true⟩,⟨(-3910845593232245541827041),(-3442547014606122570284007),true⟩⟩
  | 5,1 => ⟨⟨2481532574149206775015896,2953205273150812675081074,true⟩,⟨(-4222781888885263498316187),(-3721253921093985446589980),true⟩⟩
  | 5,2 => ⟨⟨2368124544656854126587877,2862169186001654425511803,true⟩,⟨(-4484794184182957825493071),(-3955102315032119824816313),true⟩⟩
  | 5,3 => ⟨⟨2285531615450365473307727,2793523326098874112145308,true⟩,⟨(-4648590911690170711374086),(-4101147863985685397532357),true⟩⟩
  | 5,4 => ⟨⟨2665640042114016512343454,3083690249237471619080383,true⟩,⟨(-3601025272715503127961486),(-3165491029324877875129049),true⟩⟩
  | 5,5 => ⟨⟨2709547020633484835764939,3104354058301491325274371,true⟩,⟨(-3335538505593010244548539),(-2927956554580185814319142),true⟩⟩
  | 5,6 => ⟨⟨2728636464769339508274175,3106220288208927832893150,true⟩,⟨(-3140892196560632873890053),(-2753767401456977776338026),true⟩⟩
  | 5,7 => ⟨⟨2734480235479196997575961,3102168043345525811578271,true⟩,⟨(-3029972680375635332170641),(-2654502761784190567418393),true⟩⟩
  | 6,0 => ⟨⟨1223612573866428514558988,1841635600905433210404297,true⟩,⟨(-5932599283222423471031141),(-5239488429884847904950893),true⟩⟩
  | 6,1 => ⟨⟨740280757956440250817023,1399048150943063720615539,true⟩,⟨(-6271880801796026381908539),(-5530930108236677802533519),true⟩⟩
  | 6,2 => ⟨⟨292197834455520254733026,992541215887376758769856,true⟩,⟨(-6509973408057448937167902),(-5726653543419619033849414),true⟩⟩
  | 6,3 => ⟨⟨(-6448192652182565650793),719864088788443283650489,true⟩,⟨(-6634436340358061566128873),(-5825893782322493055566659),true⟩⟩
  | 6,4 => ⟨⟨1637103121404933120015413,2221791072941742668365773,true⟩,⟨(-5549117630660955814479140),(-4901204533069478891322824),true⟩⟩
  | 6,5 => ⟨⟨1944389038608572313877279,2497943665856411373540432,true⟩,⟨(-5184397372549261155372321),(-4577880048919801738023022),true⟩⟩
  | 6,6 => ⟨⟨2140741186002562293159807,2669988046321145584736329,true⟩,⟨(-4898561597401117611900666),(-4323771901152583532881780),true⟩⟩
  | 6,7 => ⟨⟨2241244050530596482355455,2756115219865209333806233,true⟩,⟨(-4729466949503386004847757),(-4173212219887321293599878),true⟩⟩
  | 7,0 => ⟨⟨(-2792251163410132601465728),(-1868336044744852886379850),true⟩,⟨(-6728640894382768256139302),(-5786735975940764426704889),true⟩⟩
  | 7,1 => ⟨⟨(-3630769941491610545706295),(-2667729690130189720162453),true⟩,⟨(-6368185458676980754920166),(-5424407435646765418074627),true⟩⟩
  | 7,2 => ⟨⟨(-4251072388861961168445016),(-3268372953512159260203486),true⟩,⟨(-5936340858119949403128957),(-5008227761863808468981407),true⟩⟩
  | 7,3 => ⟨⟨(-4591543129821066646400027),(-3603051213039984280388092),true⟩,⟨(-5614183634564190530125438),(-4703657620888804824728237),true⟩⟩
  | 7,4 => ⟨⟨(-1885054249237618528605313),(-1015296318292155608355270),true⟩,⟨(-6900442812434654988164193),(-5982422988069557808950306),true⟩⟩
  | 7,5 => ⟨⟨(-1079590637572222556295997),(-266759536123940891031457),true⟩,⟨(-6888689332289786285447157),(-6007872073400483310566103),true⟩⟩
  | 7,6 => ⟨⟨(-489983074328373400462217),276895156679071836935790,true⟩,⟨(-6784189333645328303486005),(-5939757401221740219208005),true⟩⟩
  | 7,7 => ⟨⟨(-159497945145356901366034),580039421221122836674990,true⟩,⟨(-6688409412503360352712947),(-5867888100540508347177190),true⟩⟩
  | 8,0 => ⟨⟨(-5672427131540236460714860),(-4824505060473311765152925),true⟩,⟨(-2234277670937934768971224),(-1639256392566023539151602),true⟩⟩
  | 8,1 => ⟨⟨(-5423614209900799250777708),(-4668541516729756314075097),true⟩,⟨(-1259466125854362433174601),(-784201290999716336426835),true⟩⟩
  | 8,2 => ⟨⟨(-5081810347610926901063184),(-4411768478727304177404775),true⟩,⟨(-576622700592391517420489),(-196057837760456518873108),true⟩⟩
  | 8,3 => ⟨⟨(-4828101675341481903385027),(-4212355312568909584320968),true⟩,⟨(-215706914506684731488831),116990116101675642995859,true⟩⟩
  | 8,4 => ⟨⟨(-5671484592564137972690627),(-4745901202585240617797644),true⟩,⟨(-3340896327298514439838579),(-2622849203835545012592524),true⟩⟩
  | 8,5 => ⟨⟨(-5407188593047912680689004),(-4436394203184333818391786),true⟩,⟨(-4340359030064910019046592),(-3526330648091318893106859),true⟩⟩
  | 8,6 => ⟨⟨(-5031875260838519191345665),(-4044546784893934189579791),true⟩,⟨(-5056715997802720650395024),(-4184075297919896653890616),true⟩⟩
  | 8,7 => ⟨⟨(-4744871421053786182591332),(-3755418773515414816775441),true⟩,⟨(-5441949927771841313545580),(-4542250592684350022499301),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP531Value0_0 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP531Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value0_1 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP531Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value0_2 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP531Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value0_3 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP531Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value0_4 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP531Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value0_5 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP531Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value0_6 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP531Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value0_7 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP531Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP531Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 0 j)=sharedDiskP531Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP531Value0_0
  · exact sharedDiskP531Value0_1
  · exact sharedDiskP531Value0_2
  · exact sharedDiskP531Value0_3
  · exact sharedDiskP531Value0_4
  · exact sharedDiskP531Value0_5
  · exact sharedDiskP531Value0_6
  · exact sharedDiskP531Value0_7
private theorem sharedDiskP531Value1_0 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP531Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value1_1 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP531Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value1_2 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP531Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value1_3 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP531Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value1_4 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP531Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value1_5 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP531Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value1_6 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP531Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value1_7 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP531Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP531Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 1 j)=sharedDiskP531Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP531Value1_0
  · exact sharedDiskP531Value1_1
  · exact sharedDiskP531Value1_2
  · exact sharedDiskP531Value1_3
  · exact sharedDiskP531Value1_4
  · exact sharedDiskP531Value1_5
  · exact sharedDiskP531Value1_6
  · exact sharedDiskP531Value1_7
private theorem sharedDiskP531Value2_0 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP531Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value2_1 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP531Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value2_2 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP531Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value2_3 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP531Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value2_4 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP531Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value2_5 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP531Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value2_6 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP531Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value2_7 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP531Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP531Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 2 j)=sharedDiskP531Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP531Value2_0
  · exact sharedDiskP531Value2_1
  · exact sharedDiskP531Value2_2
  · exact sharedDiskP531Value2_3
  · exact sharedDiskP531Value2_4
  · exact sharedDiskP531Value2_5
  · exact sharedDiskP531Value2_6
  · exact sharedDiskP531Value2_7
private theorem sharedDiskP531Value3_0 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP531Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value3_1 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP531Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value3_2 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP531Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value3_3 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP531Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value3_4 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP531Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value3_5 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP531Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value3_6 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP531Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value3_7 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP531Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP531Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 3 j)=sharedDiskP531Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP531Value3_0
  · exact sharedDiskP531Value3_1
  · exact sharedDiskP531Value3_2
  · exact sharedDiskP531Value3_3
  · exact sharedDiskP531Value3_4
  · exact sharedDiskP531Value3_5
  · exact sharedDiskP531Value3_6
  · exact sharedDiskP531Value3_7
private theorem sharedDiskP531Value4_0 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP531Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value4_1 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP531Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value4_2 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP531Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value4_3 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP531Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value4_4 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP531Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value4_5 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP531Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value4_6 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP531Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value4_7 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP531Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP531Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 4 j)=sharedDiskP531Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP531Value4_0
  · exact sharedDiskP531Value4_1
  · exact sharedDiskP531Value4_2
  · exact sharedDiskP531Value4_3
  · exact sharedDiskP531Value4_4
  · exact sharedDiskP531Value4_5
  · exact sharedDiskP531Value4_6
  · exact sharedDiskP531Value4_7
private theorem sharedDiskP531Value5_0 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP531Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value5_1 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP531Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value5_2 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP531Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value5_3 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP531Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value5_4 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP531Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value5_5 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP531Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value5_6 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP531Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value5_7 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP531Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP531Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 5 j)=sharedDiskP531Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP531Value5_0
  · exact sharedDiskP531Value5_1
  · exact sharedDiskP531Value5_2
  · exact sharedDiskP531Value5_3
  · exact sharedDiskP531Value5_4
  · exact sharedDiskP531Value5_5
  · exact sharedDiskP531Value5_6
  · exact sharedDiskP531Value5_7
private theorem sharedDiskP531Value6_0 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP531Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value6_1 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP531Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value6_2 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP531Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value6_3 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP531Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value6_4 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP531Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value6_5 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP531Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value6_6 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP531Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value6_7 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP531Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP531Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 6 j)=sharedDiskP531Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP531Value6_0
  · exact sharedDiskP531Value6_1
  · exact sharedDiskP531Value6_2
  · exact sharedDiskP531Value6_3
  · exact sharedDiskP531Value6_4
  · exact sharedDiskP531Value6_5
  · exact sharedDiskP531Value6_6
  · exact sharedDiskP531Value6_7
private theorem sharedDiskP531Value7_0 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP531Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value7_1 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP531Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value7_2 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP531Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value7_3 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP531Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value7_4 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP531Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value7_5 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP531Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value7_6 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP531Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value7_7 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP531Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP531Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 7 j)=sharedDiskP531Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP531Value7_0
  · exact sharedDiskP531Value7_1
  · exact sharedDiskP531Value7_2
  · exact sharedDiskP531Value7_3
  · exact sharedDiskP531Value7_4
  · exact sharedDiskP531Value7_5
  · exact sharedDiskP531Value7_6
  · exact sharedDiskP531Value7_7
private theorem sharedDiskP531Value8_0 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP531Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value8_1 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP531Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value8_2 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP531Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value8_3 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP531Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value8_4 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP531Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value8_5 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP531Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value8_6 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP531Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP531Value8_7 : truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP531Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP531Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points 8 j)=sharedDiskP531Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP531Value8_0
  · exact sharedDiskP531Value8_1
  · exact sharedDiskP531Value8_2
  · exact sharedDiskP531Value8_3
  · exact sharedDiskP531Value8_4
  · exact sharedDiskP531Value8_5
  · exact sharedDiskP531Value8_6
  · exact sharedDiskP531Value8_7
theorem sharedDiskP531Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP531Params (sharedChord521Gauss8Points i j)=sharedDiskP531Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP531Values0_eq
  · exact sharedDiskP531Values1_eq
  · exact sharedDiskP531Values2_eq
  · exact sharedDiskP531Values3_eq
  · exact sharedDiskP531Values4_eq
  · exact sharedDiskP531Values5_eq
  · exact sharedDiskP531Values6_eq
  · exact sharedDiskP531Values7_eq
  · exact sharedDiskP531Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP531Box : HorizontalRectangle := ⟨(321/400),(161/200),(946164923013499/1649267441664000),(949386148485499/1649267441664000),(1378533860338515657168481629180045/5192296858534827628530496329220096),(2736324479999645442757840305489991/2596148429267413814265248164610048),(-2235322786172907788502692124661837/649037107316853453566312041152512),(-1710290978839344607313447651350605/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP531Grid : CGrid := momentChordGrid sharedDiskP531Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP531Columns : containedInReported sharedDiskP531Grid.re sharedDiskP531Box.reLo sharedDiskP531Box.reHi=true ∧ containedInReported sharedDiskP531Grid.im sharedDiskP531Box.imLo sharedDiskP531Box.imHi=true := by
  rw [sharedDiskP531Grid,momentChordGrid_eq_tabulated sharedDiskP531Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP531Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP531Values_eq]
  decide +kernel
theorem sharedDiskP531Sound : sharedDiskP531Box.Sound := by
  intro t a tl tu al au
  change (((321/400):ℚ):ℝ)≤t at tl
  change t≤(((161/200):ℚ):ℝ) at tu
  change (((946164923013499/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((949386148485499/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP531Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(321/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((161/200):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(946164923013499/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((949386148485499/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP531Columns.1 sharedDiskP531Columns.2
def sharedDiskP531Rows : List SignRow := [positive_531.toSignRow]
theorem sharedDiskP531Rows_actual : ∀ r∈sharedDiskP531Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP531Rows.all (sharedDiskP531Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP531Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP532Params : ChordParams := ⟨⟨(-24704125990979293853902),(-24407438008109296678991),true⟩,⟨1992531082560603744897794,2007933819991004345094059,true⟩,⟨127509335897775462584088,129379768549988026538138,true⟩,⟨229651642913425222597386,232596318071781662100620,true⟩,⟨336670969600243487310610,338792493634493755367776,true⟩,⟨1160506995366898578310886,1161076981003852740739044,true⟩,⟨(-2265609263213614712881324),(-2257486223581555908402814),true⟩,⟨⟨1143857142186152571564995,1172359391958515267749048,true⟩,⟨(-14311839),14311839,true⟩⟩⟩
theorem sharedDiskP532Params_ok : chordParams (Grid.ofRats (161/200) (323/400)) (Grid.ofRats (37893948235507/65970697666560) (38022797254387/65970697666560))=sharedDiskP532Params := by decide +kernel
def sharedDiskP532Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3178763444579551006592464),(-2664972971265520724851179),true⟩,⟨(-338319670042564889480038),73105813124258032782232,true⟩⟩
  | 0,1 => ⟨⟨(-2805287013628887108899432),(-2335186952750945135309012),true⟩,⟨(-402611254054957191053351),(-13827916639243992635977),true⟩⟩
  | 0,2 => ⟨⟨(-2536627938824097004966482),(-2100887223650565086793330),true⟩,⟨(-456811193186516551058984),(-89247638207112539465005),true⟩⟩
  | 0,3 => ⟨⟨(-2386001795539803080368228),(-1970155612888844784699153),true⟩,⟨(-489889451015587215235999),(-135251224621788651414318),true⟩⟩
  | 0,4 => ⟨⟨(-3623314320928054269576718),(-3064275903105428994314986),true⟩,⟨(-280274490568476299028709),146387508863886872865110,true⟩⟩
  | 0,5 => ⟨⟨(-4078082640808697918874549),(-3480553031264591444197227),true⟩,⟨(-243291253461189911748992),188112555242601124261111,true⟩⟩
  | 0,6 => ⟨⟨(-4463799188807404952181037),(-3839923546500354608124345),true⟩,⟨(-230664576194317102968113),193480142615043309952950,true⟩⟩
  | 0,7 => ⟨⟨(-4706476357352052675530905),(-4068509710172080738400191),true⟩,⟨(-236657816748141491753614),181869714596330954400024,true⟩⟩
  | 1,0 => ⟨⟨(-1486006179846232413384988),(-1196246970962410881461957),true⟩,⟨(-713932958212405179930094),(-451053461065295704856241),true⟩⟩
  | 1,1 => ⟨⟨(-1290635362766174847488442),(-1028651141701146282550536),true⟩,⟨(-763751185538598579528475),(-522793361195125395544704),true⟩⟩
  | 1,2 => ⟨⟨(-1148982237267140681501037),(-906789580100308648738532),true⟩,⟨(-798587146404230914896720),(-573459994544025931271214),true⟩⟩
  | 1,3 => ⟨⟨(-1068488248459153691330537),(-837349641460583991949280),true⟩,⟨(-817637507007734551408050),(-601414136524139627145761),true⟩⟩
  | 1,4 => ⟨⟨(-1719530100731851546119701),(-1396307782057897608519307),true⟩,⟨(-653449902058813719001580),(-364758484186388254341674),true⟩⟩
  | 1,5 => ⟨⟨(-1963427049317159167789150),(-1605522251684145269013251),true⟩,⟨(-591147428056105323573808),(-276631644416140400569550),true⟩⟩
  | 1,6 => ⟨⟨(-2177226097813855738162039),(-1789563210131229780768007),true⟩,⟨(-538562259141692158068685),(-202882362579845207518259),true⟩⟩
  | 1,7 => ⟨⟨(-2315909592524268004658803),(-1909414346158053533312105),true⟩,⟨(-505895072286830112519302),(-157414215806826740358910),true⟩⟩
  | 2,0 => ⟨⟨(-180205804000005548465481),(-40850508323612745340367),true⟩,⟨(-964023418194667284221496),(-819387052393977266744037),true⟩⟩
  | 2,1 => ⟨⟨8816603890332415932087,137203760581925785899633,true⟩,⟨(-971745623158794924804366),(-836161053880107028230575),true⟩⟩
  | 2,2 => ⟨⟨146450318496523060712141,268794539679756668594243,true⟩,⟨(-971487590412664864584764),(-841629032422757930428397),true⟩⟩
  | 2,3 => ⟨⟨225327003833692939695136,345044531825877716355025,true⟩,⟨(-969295300504284114462477),(-842163974407398395149355),true⟩⟩
  | 2,4 => ⟨⟨(-406304696986657916131111),(-250177808774786450460029),true⟩,⟨(-942072587422343473484967),(-784725879997948218499868),true⟩⟩
  | 2,5 => ⟨⟨(-646377813265254079190401),(-468532750206646055845371),true⟩,⟨(-904696982925461058542963),(-731339760987332393723078),true⟩⟩
  | 2,6 => ⟨⟨(-865530496138423479006411),(-661444220022556333489967),true⟩,⟨(-862323601423020639078480),(-668045042755116903584835),true⟩⟩
  | 2,7 => ⟨⟨(-1012046751435008943229950),(-788558050568646912579822),true⟩,⟨(-830591050076081760090416),(-620552284942463951222568),true⟩⟩
  | 3,0 => ⟨⟨1152911696643029744032677,1281279270174123678555215,true⟩,⟨(-913243766619752914702647),(-788003958490317808556253),true⟩⟩
  | 3,1 => ⟨⟨1374438884216505157369929,1509405305194478801050110,true⟩,⟨(-924031882367421465784725),(-794482098980427357184848),true⟩⟩
  | 3,2 => ⟨⟨1544668113012998927415435,1686125409187399237609163,true⟩,⟨(-951603830557745276627541),(-817077867594170262132045),true⟩⟩
  | 3,3 => ⟨⟨1646252428670770824514527,1792277303422035387807479,true⟩,⟨(-978525288676926231737817),(-840216007842716625020665),true⟩⟩
  | 3,4 => ⟨⟨901139150833204106375711,1024131027128943717320629,true⟩,⟨(-922796884045128819807145),(-800020977892532857870384),true⟩⟩
  | 3,5 => ⟨⟨646367942282363227967538,765967426632905319834036,true⟩,⟨(-942703350765873891374596),(-820217492323150195042345),true⟩⟩
  | 3,6 => ⟨⟨425322543863476292100048,543635081719315721065978,true⟩,⟨(-959319088944002615591933),(-835463730374974008141417),true⟩⟩
  | 3,7 => ⟨⟨280993422701528550026927,399641467736652422915275,true⟩,⟨(-966941026530636164958485),(-841199943869824626342216),true⟩⟩
  | 4,0 => ⟨⟨2397819430160807768090311,2629077261685488260572633,true⟩,⟨(-1623497176056747867195051),(-1400309873057634549768717),true⟩⟩
  | 4,1 => ⟨⟨2586201738957364992621949,2861876625422200162085545,true⟩,⟨(-2056336045927582976576580),(-1785196161063553446819444),true⟩⟩
  | 4,2 => ⟨⟨2689875545467417717727244,3012180746166721902259191,true⟩,⟨(-2545468002020253263641853),(-2222067260107577627968518),true⟩⟩
  | 4,3 => ⟨⟨2710757540026717151382036,3067485991952150526425485,true⟩,⟨(-2922267650400624292124304),(-2559162819852369365091158),true⟩⟩
  | 4,4 => ⟨⟨2173485213598385713635129,2369831525922007771040392,true⟩,⟨(-1318409980671992599915518),(-1131400488838471197655265),true⟩⟩
  | 4,5 => ⟨⟨1961866536308400702191055,2133883441424810391385858,true⟩,⟨(-1134509231296881223713439),(-971699840188045660805073),true⟩⟩
  | 4,6 => ⟨⟨1795349339778142690751134,1952148302914472410174873,true⟩,⟨(-1037533701200697621024102),(-889306753009132356303114),true⟩⟩
  | 4,7 => ⟨⟨1695156570315673825916270,1844135967897922810119384,true⟩,⟨(-995119363970311551261877),(-854174882839806120597417),true⟩⟩
  | 5,0 => ⟨⟨2553210044606309559321723,2998473856743024706783642,true⟩,⟨(-3930503038746009247929782),(-3461207524193413204477458),true⟩⟩
  | 5,1 => ⟨⟨2443361516690907655872097,2915289317750367086938078,true⟩,⟨(-4241210302522461325389999),(-3738804167408713585559503),true⟩⟩
  | 5,2 => ⟨⟨2327420995658059782867784,2821591888715615121980308,true⟩,⟨(-4501792350621452376719964),(-3971357547945585047286760),true⟩⟩
  | 5,3 => ⟨⟨2243259007460313296712489,2751283220512134866337625,true⟩,⟨(-4664496781924104788635143),(-4116413341331077724225143),true⟩⟩
  | 5,4 => ⟨⟨2633450827376839032309843,3051967476817399553440012,true⟩,⟨(-3621429124587782668225806),(-3184821351763545653896383),true⟩⟩
  | 5,5 => ⟨⟨2679840767566950532537317,3075167269916424320133922,true⟩,⟨(-3356227671295971800755551),(-2947536812448946439880926),true⟩⟩
  | 5,6 => ⟨⟨2700702967075395098071761,3078831796136423330901405,true⟩,⟨(-3161591417251635472907028),(-2773348484135293825158932),true⟩⟩
  | 5,7 => ⟨⟨2707534671758390879545111,3075777106245216923445017,true⟩,⟨(-3050604205847307426754247),(-2674016973600644256799147),true⟩⟩
  | 6,0 => ⟨⟨1169481950029156722959847,1787468020255869328101513,true⟩,⟨(-5933775632049008819644126),(-5240803666806847494738602),true⟩⟩
  | 6,1 => ⟨⟨684487839226483771490893,1343397690327674046163774,true⟩,⟨(-6266048873718504146205136),(-5525520467371272652568991),true⟩⟩
  | 6,2 => ⟨⟨236049100940259611372901,936639181558221962369355,true⟩,⟨(-6497731524991446923166095),(-5715151473409273984089451),true⟩⟩
  | 6,3 => ⟨⟨(-62482743373773389051989),663977190062036908836027,true⟩,⟨(-6618007351764743601390057),(-5810635506107206710676197),true⟩⟩
  | 6,4 => ⟨⟨1586817891704982911911989,2170805133885426538503510,true⟩,⟨(-5555762822873713410380193),(-4908079864275641509837189),true⟩⟩
  | 6,5 => ⟨⟨1897168414826088546843702,2450368871168177419439499,true⟩,⟨(-5195532119271033029863796),(-4588821472709287603694593),true⟩⟩
  | 6,6 => ⟨⟨2096114884972789455187039,2625229995548336429559553,true⟩,⟨(-4912482980649987602318707),(-4337238729598333214224445),true⟩⟩
  | 6,7 => ⟨⟨2198203486087322882976301,2713056903918303253667936,true⟩,⟨(-4744774026905000191632847),(-4187935005862184917385337),true⟩⟩
  | 7,0 => ⟨⟨(-2828048742113394578551770),(-1907239033603230488523627),true⟩,⟨(-6680033100627723633431970),(-5743367726069820241500394),true⟩⟩
  | 7,1 => ⟨⟨(-3654895380306010448578619),(-2696147467410282718269122),true⟩,⟨(-6313981931394316676175056),(-5376508321150319173806671),true⟩⟩
  | 7,2 => ⟨⟨(-4264774976493881381256823),(-3287255795543344286321868),true⟩,⟨(-5880211279713674673775291),(-4959041809919280344915049),true⟩⟩
  | 7,3 => ⟨⟨(-4598768338626673481701520),(-3615935022038049080333920),true⟩,⟨(-5558172604680276219297684),(-4654849667030846475185079),true⟩⟩
  | 7,4 => ⟨⟨(-1930605748273888537035530),(-1062726414228810469914496),true⟩,⟨(-6860529820547367182318855),(-5946461471079372861051647),true⟩⟩
  | 7,5 => ⟨⟨(-1131311734250809341511386),(-319342975824468233310910),true⟩,⟨(-6858130533925511270146914),(-5980070774557928047877086),true⟩⟩
  | 7,6 => ⟨⟨(-544659372736743628894492),221847059380299240380090,true⟩,⟨(-6761202412509573074391699),(-5918650589723659752415564),true⟩⟩
  | 7,7 => ⟨⟨(-215211861091476634714792),524312622065303429311906,true⟩,⟨(-6669875767472611955938448),(-5850748125753719697139386),true⟩⟩
  | 8,0 => ⟨⟨(-5646882048337028572010840),(-4805127210824687043165314),true⟩,⟨(-2207705254123784741398903),(-1617869967668197562179344),true⟩⟩
  | 8,1 => ⟨⟨(-5398379498021757605907385),(-4648452404165701456409731),true⟩,⟨(-1244943883567466181384932),(-773357749433200230046148),true⟩⟩
  | 8,2 => ⟨⟨(-5059641197107221259599225),(-4393710219936055425851407),true⟩,⟨(-570404582166150560860712),(-192341690964372404773087),true⟩⟩
  | 8,3 => ⟨⟨(-4808677941806747255390292),(-4196355469082194555391666),true⟩,⟨(-213627628012887343674268),117265197178935090656877,true⟩⟩
  | 8,4 => ⟨⟨(-5650797106350375871446708),(-4731931345847696246218844),true⟩,⟨(-3301542898196136105671174),(-2589997598637625189829293),true⟩⟩
  | 8,5 => ⟨⟨(-5395557836457089641132142),(-4431417846886355907109612),true⟩,⟨(-4291392678024855439799499),(-3484584160955207413414288),true⟩⟩
  | 8,6 => ⟨⟨(-5029696469501885038718892),(-4048611008934635952051228),true⟩,⟨(-5002787289106109995319501),(-4137519187429840823451310),true⟩⟩
  | 8,7 => ⟨⟨(-4748970957034921461384324),(-3765386651172160472907908),true⟩,⟨(-5386366566169361931912347),(-4493955699881853070506347),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP532Value0_0 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP532Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value0_1 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP532Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value0_2 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP532Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value0_3 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP532Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value0_4 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP532Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value0_5 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP532Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value0_6 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP532Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value0_7 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP532Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP532Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 0 j)=sharedDiskP532Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP532Value0_0
  · exact sharedDiskP532Value0_1
  · exact sharedDiskP532Value0_2
  · exact sharedDiskP532Value0_3
  · exact sharedDiskP532Value0_4
  · exact sharedDiskP532Value0_5
  · exact sharedDiskP532Value0_6
  · exact sharedDiskP532Value0_7
private theorem sharedDiskP532Value1_0 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP532Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value1_1 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP532Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value1_2 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP532Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value1_3 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP532Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value1_4 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP532Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value1_5 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP532Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value1_6 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP532Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value1_7 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP532Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP532Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 1 j)=sharedDiskP532Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP532Value1_0
  · exact sharedDiskP532Value1_1
  · exact sharedDiskP532Value1_2
  · exact sharedDiskP532Value1_3
  · exact sharedDiskP532Value1_4
  · exact sharedDiskP532Value1_5
  · exact sharedDiskP532Value1_6
  · exact sharedDiskP532Value1_7
private theorem sharedDiskP532Value2_0 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP532Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value2_1 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP532Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value2_2 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP532Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value2_3 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP532Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value2_4 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP532Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value2_5 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP532Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value2_6 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP532Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value2_7 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP532Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP532Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 2 j)=sharedDiskP532Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP532Value2_0
  · exact sharedDiskP532Value2_1
  · exact sharedDiskP532Value2_2
  · exact sharedDiskP532Value2_3
  · exact sharedDiskP532Value2_4
  · exact sharedDiskP532Value2_5
  · exact sharedDiskP532Value2_6
  · exact sharedDiskP532Value2_7
private theorem sharedDiskP532Value3_0 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP532Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value3_1 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP532Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value3_2 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP532Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value3_3 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP532Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value3_4 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP532Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value3_5 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP532Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value3_6 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP532Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value3_7 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP532Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP532Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 3 j)=sharedDiskP532Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP532Value3_0
  · exact sharedDiskP532Value3_1
  · exact sharedDiskP532Value3_2
  · exact sharedDiskP532Value3_3
  · exact sharedDiskP532Value3_4
  · exact sharedDiskP532Value3_5
  · exact sharedDiskP532Value3_6
  · exact sharedDiskP532Value3_7
private theorem sharedDiskP532Value4_0 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP532Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value4_1 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP532Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value4_2 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP532Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value4_3 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP532Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value4_4 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP532Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value4_5 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP532Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value4_6 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP532Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value4_7 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP532Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP532Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 4 j)=sharedDiskP532Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP532Value4_0
  · exact sharedDiskP532Value4_1
  · exact sharedDiskP532Value4_2
  · exact sharedDiskP532Value4_3
  · exact sharedDiskP532Value4_4
  · exact sharedDiskP532Value4_5
  · exact sharedDiskP532Value4_6
  · exact sharedDiskP532Value4_7
private theorem sharedDiskP532Value5_0 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP532Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value5_1 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP532Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value5_2 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP532Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value5_3 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP532Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value5_4 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP532Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value5_5 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP532Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value5_6 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP532Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value5_7 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP532Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP532Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 5 j)=sharedDiskP532Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP532Value5_0
  · exact sharedDiskP532Value5_1
  · exact sharedDiskP532Value5_2
  · exact sharedDiskP532Value5_3
  · exact sharedDiskP532Value5_4
  · exact sharedDiskP532Value5_5
  · exact sharedDiskP532Value5_6
  · exact sharedDiskP532Value5_7
private theorem sharedDiskP532Value6_0 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP532Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value6_1 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP532Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value6_2 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP532Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value6_3 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP532Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value6_4 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP532Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value6_5 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP532Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value6_6 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP532Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value6_7 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP532Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP532Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 6 j)=sharedDiskP532Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP532Value6_0
  · exact sharedDiskP532Value6_1
  · exact sharedDiskP532Value6_2
  · exact sharedDiskP532Value6_3
  · exact sharedDiskP532Value6_4
  · exact sharedDiskP532Value6_5
  · exact sharedDiskP532Value6_6
  · exact sharedDiskP532Value6_7
private theorem sharedDiskP532Value7_0 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP532Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value7_1 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP532Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value7_2 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP532Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value7_3 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP532Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value7_4 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP532Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value7_5 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP532Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value7_6 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP532Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value7_7 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP532Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP532Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 7 j)=sharedDiskP532Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP532Value7_0
  · exact sharedDiskP532Value7_1
  · exact sharedDiskP532Value7_2
  · exact sharedDiskP532Value7_3
  · exact sharedDiskP532Value7_4
  · exact sharedDiskP532Value7_5
  · exact sharedDiskP532Value7_6
  · exact sharedDiskP532Value7_7
private theorem sharedDiskP532Value8_0 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP532Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value8_1 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP532Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value8_2 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP532Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value8_3 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP532Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value8_4 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP532Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value8_5 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP532Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value8_6 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP532Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP532Value8_7 : truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP532Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP532Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points 8 j)=sharedDiskP532Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP532Value8_0
  · exact sharedDiskP532Value8_1
  · exact sharedDiskP532Value8_2
  · exact sharedDiskP532Value8_3
  · exact sharedDiskP532Value8_4
  · exact sharedDiskP532Value8_5
  · exact sharedDiskP532Value8_6
  · exact sharedDiskP532Value8_7
theorem sharedDiskP532Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP532Params (sharedChord521Gauss8Points i j)=sharedDiskP532Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP532Values0_eq
  · exact sharedDiskP532Values1_eq
  · exact sharedDiskP532Values2_eq
  · exact sharedDiskP532Values3_eq
  · exact sharedDiskP532Values4_eq
  · exact sharedDiskP532Values5_eq
  · exact sharedDiskP532Values6_eq
  · exact sharedDiskP532Values7_eq
  · exact sharedDiskP532Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP532Box : HorizontalRectangle := ⟨(161/200),(323/400),(37893948235507/65970697666560),(38022797254387/65970697666560),(1234968907153619415978189989022269/5192296858534827628530496329220096),(2664587795099392685086574005945631/2596148429267413814265248164610048),(-559005983284091298815077738783303/162259276829213363391578010288128),(-427735662326177116439365614215751/162259276829213363391578010288128),true,[]⟩
noncomputable def sharedDiskP532Grid : CGrid := momentChordGrid sharedDiskP532Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP532Columns : containedInReported sharedDiskP532Grid.re sharedDiskP532Box.reLo sharedDiskP532Box.reHi=true ∧ containedInReported sharedDiskP532Grid.im sharedDiskP532Box.imLo sharedDiskP532Box.imHi=true := by
  rw [sharedDiskP532Grid,momentChordGrid_eq_tabulated sharedDiskP532Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP532Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP532Values_eq]
  decide +kernel
theorem sharedDiskP532Sound : sharedDiskP532Box.Sound := by
  intro t a tl tu al au
  change (((161/200):ℚ):ℝ)≤t at tl
  change t≤(((323/400):ℚ):ℝ) at tu
  change (((37893948235507/65970697666560):ℚ):ℝ)≤a at al
  change a≤(((38022797254387/65970697666560):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP532Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(161/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((323/400):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(37893948235507/65970697666560))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((38022797254387/65970697666560):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP532Columns.1 sharedDiskP532Columns.2
def sharedDiskP532Rows : List SignRow := [positive_532.toSignRow]
theorem sharedDiskP532Rows_actual : ∀ r∈sharedDiskP532Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP532Rows.all (sharedDiskP532Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP532Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP533Params : ChordParams := ⟨⟨(-25002555585015811786575),(-24704125990979293853380),true⟩,⟨1982999030015169528289435,1998324569953384881374839,true⟩,⟨128040542143431469596605,129911260931296826528405,true⟩,⟨231484322550013547952998,234437526195708166002036,true⟩,⟨338629095683738911683889,340750712815648911078310,true⟩,⟨1159933940327980834266512,1160506995366898578311890,true⟩,⟨(-2257486223581555908411961),(-2249407373817189008840856),true⟩,⟨⟨1143195619665534295526840,1171735017954253227622875,true⟩,⟨(-16273897),16273897,true⟩⟩⟩
theorem sharedDiskP533Params_ok : chordParams (Grid.ofRats (323/400) (81/100)) (Grid.ofRats (12647178627601/21990232555520) (12690128300561/21990232555520))=sharedDiskP533Params := by decide +kernel
def sharedDiskP533Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3176783457771608733774454),(-2663301356239045454076499),true⟩,⟨(-335563440352606465009748),75496428398088417380482,true⟩⟩
  | 0,1 => ⟨⟨(-2806213000588910269334168),(-2336045655612909913186189),true⟩,⟨(-398844530105396156902582),(-10126001710412721413960),true⟩⟩
  | 0,2 => ⟨⟨(-2539417987015197718060994),(-2103349392067559801163562),true⟩,⟨(-452337800352256996166959),(-84598065195427472667934),true⟩⟩
  | 0,3 => ⟨⟨(-2389680653530106881080693),(-1973442280151220854199493),true⟩,⟨(-485042542645278352284620),(-130232906473188966934175),true⟩⟩
  | 0,4 => ⟨⟨(-3617426193884823847322411),(-3059134953089139601116313),true⟩,⟨(-278653307551237435807676),147361251657559520999636,true⟩⟩
  | 0,5 => ⟨⟨(-4067747092149580873344351),(-3471375793851955350375618),true⟩,⟨(-242633786795549716783928),187997244213356159567192,true⟩⟩
  | 0,6 => ⟨⟨(-4449394946955489822051392),(-3826973050692788687744648),true⟩,⟨(-230653198982382440047695),192783750794669914047535,true⟩⟩
  | 0,7 => ⟨⟨(-4689387117545797419261756),(-4053049146717369390012815),true⟩,⟨(-236839065596600932447315),181027818072099832074287,true⟩⟩
  | 1,0 => ⟨⟨(-1494217104557861092886853),(-1203511164180447846530783),true⟩,⟨(-707698765130961769042170),(-444120431804793341343016),true⟩⟩
  | 1,1 => ⟨⟨(-1299613504650233020599817),(-1036627806456381191863969),true⟩,⟨(-757527791531027480307515),(-515821669770145214043931),true⟩⟩
  | 1,2 => ⟨⟨(-1158485778002760824771966),(-915267722109832626996938),true⟩,⟨(-792468323785312661336356),(-566573107432006489103615),true⟩⟩
  | 1,3 => ⟨⟨(-1078281643110605772059781),(-846109589332084901072910),true⟩,⟨(-811617308518712835741592),(-594620155133570359009285),true⟩⟩
  | 1,4 => ⟨⟨(-1726739331044283673916364),(-1402669345408997848265587),true⟩,⟨(-647380063410771950976551),(-358083653557824546230322),true⟩⟩
  | 1,5 => ⟨⟨(-1969469259626616067545452),(-1610856967212799906082122),true⟩,⟨(-585418210189419142856676),(-270432513181145800114613),true⟩⟩
  | 1,6 => ⟨⟨(-2182129491528480795361302),(-1793908736684235446314436),true⟩,⟨(-533242092085475975398253),(-197235627468490301866452),true⟩⟩
  | 1,7 => ⟨⟨(-2320012272116730730286436),(-1913067341318188759426307),true⟩,⟨(-500882564223230919480764),(-152177003034500229856383),true⟩⟩
  | 2,0 => ⟨⟨(-192897040663018787611183),(-53008780868034506286762),true⟩,⟨(-960928958581240770973605),(-816005778362166351855781),true⟩⟩
  | 2,1 => ⟨⟨(-4496779205049397884911),124289091603570034258062,true⟩,⟨(-969741273601306408573688),(-833886152277703891672718),true⟩⟩
  | 2,2 => ⟨⟨132689173326909722061394,255377406491909011582190,true⟩,⟨(-970336713168357267990768),(-840212557900945254528555),true⟩⟩
  | 2,3 => ⟨⟨211308631141003916450792,331141022934509439523320,true⟩,⟨(-968648628681477412359998),(-841393785687281771174483),true⟩⟩
  | 2,4 => ⟨⟨(-418214045971324523905257),(-261476577682947343581393),true⟩,⟨(-937838937931252547066810),(-780173605421254910689624),true⟩⟩
  | 2,5 => ⟨⟨(-657640103407676193681878),(-478929772664524249125065),true⟩,⟨(-899532571138298641160391),(-725609923942974639688973),true⟩⟩
  | 2,6 => ⟨⟨(-876036310844346057105417),(-670911979828338821463978),true⟩,⟨(-856685688027199990581776),(-661633828037926830047644),true⟩⟩
  | 2,7 => ⟨⟨(-1022040475510885871155685),(-797514911370671993672606),true⟩,⟨(-824657669050636522628686),(-613843266356941972436204),true⟩⟩
  | 3,0 => ⟨⟨1137258878316495052601560,1265499991047783873190138,true⟩,⟨(-918490596455509638689155),(-793162355958259282701793),true⟩⟩
  | 3,1 => ⟨⟨1358785062792106727561560,1493682287650560701722026,true⟩,⟨(-930668980700501548179128),(-800958121503876103704354),true⟩⟩
  | 3,2 => ⟨⟨1529092231798549695904592,1670541025792590392854629,true⟩,⟨(-959333847188872761978879),(-824577836739177651962586),true⟩⟩
  | 3,3 => ⟨⟨1630733788595679772238606,1776793056942221042735275,true⟩,⟨(-986932511578261121893404),(-848346364735364456499045),true⟩⟩
  | 3,4 => ⟨⟨885696583547596044098579,1008527351553946185792170,true⟩,⟨(-926448746209206829136880),(-803644593943998015973143),true⟩⟩
  | 3,5 => ⟨⟨631381931756045111846957,750818079601500434942331,true⟩,⟨(-944694424864534657996207),(-822217968016577355957102),true⟩⟩
  | 3,6 => ⟨⟨410904940944503193231146,529078295344125371654079,true⟩,⟨(-959841278325391837725991),(-836009326221834518906177),true⟩⟩
  | 3,7 => ⟨⟨266798735819480200134111,385548736408805819732207,true⟩,⟨(-966654901940525587174455),(-840790905602470285841726),true⟩⟩
  | 4,0 => ⟨⟨2380861810336101684012640,2612479126916951291526606,true⟩,⟨(-1638524727498941045760989),(-1414606520687966824176332),true⟩⟩
  | 4,1 => ⟨⟨2566770558089338124723703,2842920763912318915438442,true⟩,⟨(-2073881335941484005715326),(-1801829064168805988597018),true⟩⟩
  | 4,2 => ⟨⟨2666883338841241840146890,2989727744704946223928489,true⟩,⟨(-2564866425906379708091773),(-2240424285910923129162265),true⟩⟩
  | 4,3 => ⟨⟨2684641767005036988991279,3041912453168025955317548,true⟩,⟨(-2942412522794951030488100),(-2578220894931115061859058),true⟩⟩
  | 4,4 => ⟨⟨2157689438613701614609021,2354274385902056810256711,true⟩,⟨(-1331037963165737778730561),(-1143470236107443256120948),true⟩⟩
  | 4,5 => ⟨⟨1946410546772002243152128,2118571514451394864467333,true⟩,⟨(-1145258536950659720080205),(-982021854343484175787444),true⟩⟩
  | 4,6 => ⟨⟨1779905118360182602853458,1936787327994642616075028,true⟩,⟨(-1046993658926711954500754),(-898424013245833249597259),true⟩⟩
  | 4,7 => ⟨⟨1679665467080219448022218,1828697228557155542078262,true⟩,⟨(-1003863007116692850736700),(-862619752793106530877346),true⟩⟩
  | 5,0 => ⟨⟨2517800812000947847219903,2963411393142140308129945,true⟩,⟨(-3949604315575373846427678),(-3479351543986907849068149),true⟩⟩
  | 5,1 => ⟨⟨2404967254193481314711169,2877116831991522095013906,true⟩,⟨(-4259015436369619522372502),(-3755775621114262236748769),true⟩⟩
  | 5,2 => ⟨⟨2286531794661136751943252,2780793226829501542065870,true⟩,⟨(-4518112257943146679625269),(-3986982914936770673592327),true⟩⟩
  | 5,3 => ⟨⟨2200828850559508312914147,2708848502416523182961674,true⟩,⟨(-4679691159234739338154569),(-4131018057831619330523331),true⟩⟩
  | 5,4 => ⟨⟨2600983143489252245374513,3019939329933272293701432,true⟩,⟨(-3641343836119991724059695),(-3203697379412344985330557),true⟩⟩
  | 5,5 => ⟨⟨2649845958205908735984950,3045667949046752524079321,true⟩,⟨(-3376484439686553488399564),(-2966715404465130183315345),true⟩⟩
  | 5,6 => ⟨⟨2672478362987397774713296,3051130400720928238342331,true⟩,⟨(-3181898975594994622756227),(-2792565667192489269350013),true⟩⟩
  | 5,7 => ⟨⟨2680298334957049818475035,3049074846263940837361439,true⟩,⟨(-3070866831089510065823701),(-2693188381871972244202962),true⟩⟩
  | 6,0 => ⟨⟨1115572102650207122866365,1733470105157316088182727,true⟩,⟨(-5934051222329882512547259),(-5241286681594017212060622),true⟩⟩
  | 6,1 => ⟨⟨629071578414554559876659,1288585029880150120394779,true⟩,⟨(-6259317532969537572737104),(-5518978019338909071000815),true⟩⟩
  | 6,2 => ⟨⟨180409921053165671901416,881180177541564713917047,true⟩,⟨(-6484622388074120615180575),(-5702858221727001655853744),true⟩⟩
  | 6,3 => ⟨⟨(-117923611739449279318737),608614526399373910933505,true⟩,⟨(-6600746490251735010511705),(-5794619448420580763931395),true⟩⟩
  | 6,4 => ⟨⟨1536601659838500061553535,2119846858998697640269061,true⟩,⟨(-5561546194588070275056894),(-4914154025837596406208177),true⟩⟩
  | 6,5 => ⟨⟨1849909215382163519540110,2402715087281045018761354,true⟩,⟨(-5205857091732433792751993),(-4599010565568905177879455),true⟩⟩
  | 6,6 => ⟨⟨2051381180054800804959690,2580325681071520364747354,true⟩,⟨(-4925644625567991841417480),(-4349999899080163719253907),true⟩⟩
  | 6,7 => ⟨⟨2155020616369939662812138,2669818599860190708946878,true⟩,⟨(-4759353633601481132719162),(-4201982169288270811654315),true⟩⟩
  | 7,0 => ⟨⟨(-2862873862189706127575171),(-1945208099264115415061047),true⟩,⟨(-6631277564445573145384837),(-5699861392124598050070225),true⟩⟩
  | 7,1 => ⟨⟨(-3678109749117435311444360),(-2723668157794407294098834),true⟩,⟨(-6259901944403232739371520),(-5328709930881748891866335),true⟩⟩
  | 7,2 => ⟨⟨(-4277684154264909087366786),(-3305336171872627166764423),true⟩,⟨(-5824401149825143723504277),(-4910126051255416955729113),true⟩⟩
  | 7,3 => ⟨⟨(-4605297322382338177428032),(-3628098947800219572475616),true⟩,⟨(-5502579914226830701962257),(-4606395909053381281145540),true⟩⟩
  | 7,4 => ⟨⟨(-1975221252049274430212603),(-1109277810260034159332852),true⟩,⟨(-6820194385178913148025875),(-5910116329590569707495097),true⟩⟩
  | 7,5 => ⟨⟨(-1182204318742659973018476),(-371165451924877261910161),true⟩,⟨(-6826940347912138481031681),(-5951696542441662282301766),true⟩⟩
  | 7,6 => ⟨⟨(-598624431173917704463174),167441912715695226988722,true⟩,⟨(-6737460953248640401215721),(-5896857873932229744840520),true⟩⟩
  | 7,7 => ⟨⟨(-270292943784773186186291),469149352892016255927066,true⟩,⟨(-6650532165651240034940216),(-5832870852884614488603671),true⟩⟩
  | 8,0 => ⟨⟨(-5621446072657474918630723),(-4785772597954811037302316),true⟩,⟨(-2181527223007694459839599),(-1596790724146597364736639),true⟩⟩
  | 8,1 => ⟨⟨(-5373316764900191949801018),(-4628461412596613110996773),true⟩,⟨(-1230638102246061889978811),(-762667406333256837176911),true⟩⟩
  | 8,2 => ⟨⟨(-5037626143496519149034288),(-4375748546070728343668695),true⟩,⟨(-564273624187582143083429),(-188669721522409628705197),true⟩⟩
  | 8,3 => ⟨⟨(-4789375851662313457205792),(-4180431592787909406720727),true⟩,⟨(-211573337733392475443595),117546821238506451733814,true⟩⟩
  | 8,4 => ⟨⟨(-5630037298231908205073424),(-4717806366751232564291932),true⟩,⟨(-3262729853076109939634944),(-2557585912744474031407239),true⟩⟩
  | 8,5 => ⟨⟨(-5383610285270040980240859),(-4426059102687604490490668),true⟩,⟨(-4243005578144722778652516),(-3443320158814286231766434),true⟩⟩
  | 8,6 => ⟨⟨(-5026992498249502010239255),(-4052105158099233194117298),true⟩,⟨(-4949384681989131553031157),(-4091406253058139051998930),true⟩⟩
  | 8,7 => ⟨⟨(-4752427237502843295085168),(-3774680540726493216785985),true⟩,⟨(-5331242405113714677839456),(-4446049201609109726633580),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP533Value0_0 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP533Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value0_1 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP533Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value0_2 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP533Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value0_3 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP533Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value0_4 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP533Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value0_5 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP533Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value0_6 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP533Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value0_7 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP533Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP533Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 0 j)=sharedDiskP533Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP533Value0_0
  · exact sharedDiskP533Value0_1
  · exact sharedDiskP533Value0_2
  · exact sharedDiskP533Value0_3
  · exact sharedDiskP533Value0_4
  · exact sharedDiskP533Value0_5
  · exact sharedDiskP533Value0_6
  · exact sharedDiskP533Value0_7
private theorem sharedDiskP533Value1_0 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP533Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value1_1 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP533Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value1_2 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP533Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value1_3 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP533Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value1_4 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP533Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value1_5 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP533Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value1_6 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP533Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value1_7 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP533Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP533Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 1 j)=sharedDiskP533Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP533Value1_0
  · exact sharedDiskP533Value1_1
  · exact sharedDiskP533Value1_2
  · exact sharedDiskP533Value1_3
  · exact sharedDiskP533Value1_4
  · exact sharedDiskP533Value1_5
  · exact sharedDiskP533Value1_6
  · exact sharedDiskP533Value1_7
private theorem sharedDiskP533Value2_0 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP533Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value2_1 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP533Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value2_2 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP533Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value2_3 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP533Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value2_4 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP533Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value2_5 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP533Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value2_6 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP533Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value2_7 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP533Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP533Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 2 j)=sharedDiskP533Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP533Value2_0
  · exact sharedDiskP533Value2_1
  · exact sharedDiskP533Value2_2
  · exact sharedDiskP533Value2_3
  · exact sharedDiskP533Value2_4
  · exact sharedDiskP533Value2_5
  · exact sharedDiskP533Value2_6
  · exact sharedDiskP533Value2_7
private theorem sharedDiskP533Value3_0 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP533Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value3_1 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP533Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value3_2 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP533Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value3_3 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP533Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value3_4 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP533Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value3_5 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP533Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value3_6 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP533Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value3_7 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP533Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP533Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 3 j)=sharedDiskP533Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP533Value3_0
  · exact sharedDiskP533Value3_1
  · exact sharedDiskP533Value3_2
  · exact sharedDiskP533Value3_3
  · exact sharedDiskP533Value3_4
  · exact sharedDiskP533Value3_5
  · exact sharedDiskP533Value3_6
  · exact sharedDiskP533Value3_7
private theorem sharedDiskP533Value4_0 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP533Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value4_1 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP533Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value4_2 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP533Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value4_3 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP533Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value4_4 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP533Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value4_5 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP533Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value4_6 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP533Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value4_7 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP533Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP533Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 4 j)=sharedDiskP533Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP533Value4_0
  · exact sharedDiskP533Value4_1
  · exact sharedDiskP533Value4_2
  · exact sharedDiskP533Value4_3
  · exact sharedDiskP533Value4_4
  · exact sharedDiskP533Value4_5
  · exact sharedDiskP533Value4_6
  · exact sharedDiskP533Value4_7
private theorem sharedDiskP533Value5_0 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP533Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value5_1 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP533Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value5_2 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP533Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value5_3 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP533Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value5_4 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP533Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value5_5 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP533Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value5_6 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP533Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value5_7 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP533Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP533Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 5 j)=sharedDiskP533Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP533Value5_0
  · exact sharedDiskP533Value5_1
  · exact sharedDiskP533Value5_2
  · exact sharedDiskP533Value5_3
  · exact sharedDiskP533Value5_4
  · exact sharedDiskP533Value5_5
  · exact sharedDiskP533Value5_6
  · exact sharedDiskP533Value5_7
private theorem sharedDiskP533Value6_0 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP533Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value6_1 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP533Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value6_2 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP533Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value6_3 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP533Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value6_4 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP533Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value6_5 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP533Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value6_6 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP533Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value6_7 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP533Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP533Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 6 j)=sharedDiskP533Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP533Value6_0
  · exact sharedDiskP533Value6_1
  · exact sharedDiskP533Value6_2
  · exact sharedDiskP533Value6_3
  · exact sharedDiskP533Value6_4
  · exact sharedDiskP533Value6_5
  · exact sharedDiskP533Value6_6
  · exact sharedDiskP533Value6_7
private theorem sharedDiskP533Value7_0 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP533Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value7_1 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP533Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value7_2 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP533Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value7_3 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP533Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value7_4 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP533Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value7_5 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP533Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value7_6 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP533Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value7_7 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP533Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP533Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 7 j)=sharedDiskP533Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP533Value7_0
  · exact sharedDiskP533Value7_1
  · exact sharedDiskP533Value7_2
  · exact sharedDiskP533Value7_3
  · exact sharedDiskP533Value7_4
  · exact sharedDiskP533Value7_5
  · exact sharedDiskP533Value7_6
  · exact sharedDiskP533Value7_7
private theorem sharedDiskP533Value8_0 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP533Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value8_1 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP533Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value8_2 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP533Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value8_3 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP533Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value8_4 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP533Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value8_5 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP533Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value8_6 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP533Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP533Value8_7 : truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP533Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP533Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points 8 j)=sharedDiskP533Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP533Value8_0
  · exact sharedDiskP533Value8_1
  · exact sharedDiskP533Value8_2
  · exact sharedDiskP533Value8_3
  · exact sharedDiskP533Value8_4
  · exact sharedDiskP533Value8_5
  · exact sharedDiskP533Value8_6
  · exact sharedDiskP533Value8_7
theorem sharedDiskP533Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP533Params (sharedChord521Gauss8Points i j)=sharedDiskP533Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP533Values0_eq
  · exact sharedDiskP533Values1_eq
  · exact sharedDiskP533Values2_eq
  · exact sharedDiskP533Values3_eq
  · exact sharedDiskP533Values4_eq
  · exact sharedDiskP533Values5_eq
  · exact sharedDiskP533Values6_eq
  · exact sharedDiskP533Values7_eq
  · exact sharedDiskP533Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP533Box : HorizontalRectangle := ⟨(323/400),(81/100),(12647178627601/21990232555520),(12690128300561/21990232555520),(556020503720199761724882756414543/2596148429267413814265248164610048),(2583005832625637183361366110612559/2596148429267413814265248164610048),(-4468142107046308774112928667534313/1298074214633706907132624082305024),(-3427928489920653655456180948173801/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP533Grid : CGrid := momentChordGrid sharedDiskP533Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP533Columns : containedInReported sharedDiskP533Grid.re sharedDiskP533Box.reLo sharedDiskP533Box.reHi=true ∧ containedInReported sharedDiskP533Grid.im sharedDiskP533Box.imLo sharedDiskP533Box.imHi=true := by
  rw [sharedDiskP533Grid,momentChordGrid_eq_tabulated sharedDiskP533Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP533Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP533Values_eq]
  decide +kernel
theorem sharedDiskP533Sound : sharedDiskP533Box.Sound := by
  intro t a tl tu al au
  change (((323/400):ℚ):ℝ)≤t at tl
  change t≤(((81/100):ℚ):ℝ) at tu
  change (((12647178627601/21990232555520):ℚ):ℝ)≤a at al
  change a≤(((12690128300561/21990232555520):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP533Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(323/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((81/100):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(12647178627601/21990232555520))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((12690128300561/21990232555520):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP533Columns.1 sharedDiskP533Columns.2
def sharedDiskP533Rows : List SignRow := [positive_533.toSignRow]
theorem sharedDiskP533Rows_actual : ∀ r∈sharedDiskP533Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP533Rows.all (sharedDiskP533Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP533Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP534Params : ChordParams := ⟨⟨(-25302720466469937003073),(-25002555585015811786045),true⟩,⟨1973508874088075380808962,1988757822372385457658039,true⟩,⟨128568873720225976659649,130439837225964425271640,true⟩,⟨233323424300753679479538,236285120274886512819488,true⟩,⟨340585450477607737998369,342707124362711310257161,true⟩,⟨1159357832673738857952708,1159933940327980834267532,true⟩,⟨(-2249407373817189008850002),(-2241372338467447847908583),true⟩,⟨⟨1142529913280370356271799,1171105791826329466402488,true⟩,⟨(-18490493),18490493,true⟩⟩⟩
theorem sharedDiskP534Params_ok : chordParams (Grid.ofRats (81/100) (13/16)) (Grid.ofRats (316578000813289/549755813888000) (317651742637289/549755813888000))=sharedDiskP534Params := by decide +kernel
def sharedDiskP534Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3174752047793775793982199),(-2661547378745943323582377),true⟩,⟨(-332869816035093561002654),77858092861272518469209,true⟩⟩
  | 0,1 => ⟨⟨(-2807067170325104298364042),(-2336807953859751045565327),true⟩,⟨(-395148134038917011005056),(-6467809166991580585514),true⟩⟩
  | 0,2 => ⟨⟨(-2542125951321856355654688),(-2105709179954812708775459),true⟩,⟨(-447937674586891109601985),(-80000090261832144861913),true⟩⟩
  | 0,3 => ⟨⟨(-2393274352680809827682143),(-1976624445114881733127038),true⟩,⟨(-480269297810886880847170),(-125266716717280968812449),true⟩⟩
  | 0,4 => ⟨⟨(-3611520907790058229032690),(-3053938447454675327647823),true⟩,⟨(-277082540544497936515050),148325846590064788305925,true⟩⟩
  | 0,5 => ⟨⟨(-4057440429581652961402941),(-3462182322185634752572981),true⟩,⟨(-242014281541179396610757),187889908241275537451798,true⟩⟩
  | 0,6 => ⟨⟨(-4435066384979141766134143),(-3814048445275196311686276),true⟩,⟨(-230673981688271960620402),192104723293087823048029,true⟩⟩
  | 0,7 => ⟨⟨(-4672406031558001419347127),(-4037644684505421213290291),true⟩,⟨(-237047991178728981560258),180205099601566988203586,true⟩⟩
  | 1,0 => ⟨⟨(-1502330365623171643374374),(-1210667321058270370916168),true⟩,⟨(-701516336737998426181551),(-437226367593840642429080),true⟩⟩
  | 1,1 => ⟨⟨(-1308492110121422872872938),(-1044495656908244292075035),true⟩,⟨(-751345427404202701723077),(-508879074207938884515523),true⟩⟩
  | 1,2 => ⟨⟨(-1167888179353843392220542),(-923636122143241973182782),true⟩,⟨(-786381510897793643269263),(-559706839789101416389332),true⟩⟩
  | 1,3 => ⟨⟨(-1087972859831142384993794),(-854759113391012413594935),true⟩,⟨(-805623577129462137269836),(-587841554781212697715780),true⟩⟩
  | 1,4 => ⟨⟨(-1733852999742493589881763),(-1408923310980919212215369),true⟩,⟨(-641372017305143742380184),(-351456415668050589022493),true⟩⟩
  | 1,5 => ⟨⟨(-1975418560663333881042921),(-1616084503473604203407983),true⟩,⟨(-579757922393272827743777),(-264286035756209375736747),true⟩⟩
  | 1,6 => ⟨⟨(-2186943239245265781990479),(-1798147959388921126894062),true⟩,⟨(-527994396904528548401765),(-191642681751423969502385),true⟩⟩
  | 1,7 => ⟨⟨(-2324028118651748533754480),(-1916615097293027478533333),true⟩,⟨(-495943555631622642427224),(-146992763214292725564771),true⟩⟩
  | 2,0 => ⟨⟨(-205472484837972959587333),(-65042693188893561780144),true⟩,⟨(-957792087673879034537617),(-812573401972463736870722),true⟩⟩
  | 2,1 => ⟨⟨(-17723982666808395304091),111500301653509629849248,true⟩,⟨(-967681102081843270565690),(-831548255903261866817623),true⟩⟩
  | 2,2 => ⟨⟨119045619630421023159946,242085600528805926137697,true⟩,⟨(-969121504377498304247148),(-838725635905945859422177),true⟩⟩
  | 2,3 => ⟨⟨197407405272509041457940,317448764846042117785414,true⟩,⟨(-967933315184158809127906),(-840490729709737377592319),true⟩⟩
  | 2,4 => ⟨⟨(-430011679803668110586758),(-272653642341672877032432),true⟩,⟨(-933580829724568018667130),(-775586353328517579804635),true⟩⟩
  | 2,5 => ⟨⟨(-668793113512123271702042),(-489208635408075098461540),true⟩,⟨(-894362947393117377997660),(-719864006215917177262206),true⟩⟩
  | 2,6 => ⟨⟨(-886436863737378602459628),(-680267104383109556203129),true⟩,⟨(-851059144717854277493415),(-655223727733427259441621),true⟩⟩
  | 2,7 => ⟨⟨(-1031931231902756655253361),(-806360802378936711346859),true⟩,⟨(-818746706334046405748552),(-607145798539732885521038),true⟩⟩
  | 3,0 => ⟨⟨1121666935000904188921089,1249787979478339328642370,true⟩,⟨(-923651626222949698298617),(-798231872317809615153513),true⟩⟩
  | 3,1 => ⟨⟨1343164237458001924634651,1477996915598715826968964,true⟩,⟨(-937221775575055392910354),(-807348135992921345976832),true⟩⟩
  | 3,2 => ⟨⟨1513524127407095009829089,1654967656149454184111052,true⟩,⟨(-966980584148567972163178),(-831993902306786811459434),true⟩⟩
  | 3,3 => ⟨⟨1615206377138288674824182,1761302398865339404314088,true⟩,⟨(-995256579994446624536388),(-856393610546359679308228),true⟩⟩
  | 3,4 => ⟨⟨870339426612241601531450,993017332424460041379553,true⟩,⟨(-930014769654845641702022),(-807177720721909917053557),true⟩⟩
  | 3,5 => ⟨⟨616498300445397515733087,735781100711354598009014,true⟩,⟨(-946603056822343132248181),(-824129713477886396394948),true⟩⟩
  | 3,6 => ⟨⟨396598364057747911063297,514643946611491839265136,true⟩,⟨(-960287592171655477993983),(-836471262049983017865516),true⟩⟩
  | 3,7 => ⟨⟨252720577042498440919349,371582256858543105705305,true⟩,⟨(-966297358069725235684994),(-840303423745224300428855),true⟩⟩
  | 4,0 => ⟨⟨2363732556204119816806271,2595704388860142732243874,true⟩,⟨(-1653419150946572949769860),(-1428777340514407096219170),true⟩⟩
  | 4,1 => ⟨⟨2547110991377515390861249,2823727101519985212902110,true⟩,⟨(-2091233752406211956390790),(-1818281410355560431518403),true⟩⟩
  | 4,2 => ⟨⟨2643623348972022958551464,2966992315382166014279606,true⟩,⟨(-2583989083054176841530650),(-2258524194639031500851399),true⟩⟩
  | 4,3 => ⟨⟨2658244401926966728230341,3016038542707702128487860,true⟩,⟨(-2962209632796140534158716),(-2596955159586868654678022),true⟩⟩
  | 4,4 => ⟨⟨2141778810706691815536153,2338600531312843292555190,true⟩,⟨(-1343564445863896770388853),(-1155442525751111070850974),true⟩⟩
  | 4,5 => ⟨⟨1930886257797220739194517,2103191431211661780845204,true⟩,⟨(-1155919469172920205008802),(-992257566061382279664869),true⟩⟩
  | 4,6 => ⟨⟨1764425414973231091686301,1921392237106884232507737,true⟩,⟨(-1056369424265187505352592),(-907458002425756965016066),true⟩⟩
  | 4,7 => ⟨⟨1664157147031638610545559,1813243271035749949937692,true⟩,⟨(-1012523352236565404495882),(-870981664959456686874720),true⟩⟩
  | 5,0 => ⟨⟨2482146738851700798088564,2928074489215921324164269,true⟩,⟨(-3968146718527449151239827),(-3496975842989864948547129),true⟩⟩
  | 5,1 => ⟨⟨2366362942182020644935952,2838701698368298215517886,true⟩,⟨(-4276195875663148872201742),(-3772166207121836009201204),true⟩⟩
  | 5,2 => ⟨⟨2245471112164107116964424,2739788211627852104529471,true⟩,⟨(-4533753849902692357178372),(-4001977566024495025117883),true⟩⟩
  | 5,3 => ⟨⟨2158255881296035441563845,2666234826444731942658835,true⟩,⟨(-4694174969068610884687087),(-4144962051770548515702092),true⟩⟩
  | 5,4 => ⟨⟨2568247407676528185202554,2987616730108900935626833,true⟩,⟨(-3660765754188621858783379),(-3222115042721724779434727),true⟩⟩
  | 5,5 => ⟨⟨2619571781662991041937130,3015865713464545033405862,true⟩,⟨(-3396304594504826830029023),(-2985487774051691818240553),true⟩⟩
  | 5,6 => ⟨⟨2643970943841043327469366,3023124773447505025341265,true⟩,⟨(-3201810380150088441064658),(-2811414165180497627850724),true⟩⟩
  | 5,7 => ⟨⟨2652779010154343164186118,3022069403505699180485699,true⟩,⟨(-3090755957475844256461951),(-2712012117004660500569310),true⟩⟩
  | 6,0 => ⟨⟨1061898756094730439882431,1679659042302849468539845,true⟩,⟨(-5933438294878289843089039),(-5240947960584559259683724),true⟩⟩
  | 6,1 => ⟨⟨574045758491682071344062,1234099408318720502161162,true⟩,⟨(-6251703161663931986067504),(-5511627421043949251022615),true⟩⟩
  | 6,2 => ⟨⟨125291526907500589548588,826177250936738674836657,true⟩,⟨(-6470665545907553265295133),(-5689790997740048589519364),true⟩⟩
  | 6,3 => ⟨⟨(-172761554140658056737498),553787311215287615103552,true⟩,⟨(-6582675027480438376809890),(-5777864342181947188748885),true⟩⟩
  | 6,4 => ⟨⟨1486470677554790284583674,2068933925017243677467062,true⟩,⟨(-5566475995006313328473625),(-4919433716340747220071260),true⟩⟩
  | 6,5 => ⟨⟨1802627490046365169048743,2354999567591262561495149,true⟩,⟨(-5215377169974425190774841),(-4608450957302741337483998),true⟩⟩
  | 6,6 => ⟨⟨2006555538948579379239549,2535291615732346840696750,true⟩,⟨(-4938049158444931316580009),(-4362056990565544769603739),true⟩⟩
  | 6,7 => ⟨⟨2111710433662162013855509,2626416257969656919678816,true⟩,⟨(-4773207218246872945848455),(-4215354222577835189034362),true⟩⟩
  | 7,0 => ⟨⟨(-2896739163162593845591676),(-1982253088827210050965792),true⟩,⟨(-6582395223018836787776533),(-5656235047313852887648721),true⟩⟩
  | 7,1 => ⟨⟨(-3700430245811232920930389),(-2750306413220169690327289),true⟩,⟨(-6205960452653821711739544),(-5281024953082263735575878),true⟩⟩
  | 7,2 => ⟨⟨(-4289818628558720262342320),(-3322630663517569622461146),true⟩,⟨(-5768919413461252105916104),(-4861487859863411123998446),true⟩⟩
  | 7,3 => ⟨⟨(-4611148617217852647262259),(-3639559743552447550458679),true⟩,⟨(-5447410719181079896335583),(-4558300413108110090731142),true⟩⟩
  | 7,4 => ⟨⟨(-2018906591918336611535165),(-1154953593237793113973618),true⟩,⟨(-6779460886767932132735429),(-5873408832958375022566532),true⟩⟩
  | 7,5 => ⟨⟨(-1232267544284544187079085),(-422223621898066235619990),true⟩,⟨(-6795143494213547022778000),(-5922771071384152518308315),true⟩⟩
  | 7,6 => ⟨⟨(-651872617814513641962701),113687575789039756717526,true⟩,⟨(-6712988319831314326408619),(-5874399812376162240008115),true⟩⟩
  | 7,7 => ⟨⟨(-324733050065721778848891),414559812079040923191800,true⟩,⟨(-6630400634251022794439494),(-5814275678265750254044457),true⟩⟩
  | 8,0 => ⟨⟨(-5596120816851859402249452),(-4766443664785904014517455),true⟩,⟨(-2155736702808101406737534),(-1576012897003560869148169),true⟩⟩
  | 8,1 => ⟨⟨(-5348424863496927049052649),(-4608568214634947723893830),true⟩,⟨(-1216544809796106698714156),(-752127055542754328774729),true⟩⟩
  | 8,2 => ⟨⟨(-5015763724649099062738307),(-4357882572493809207431083),true⟩,⟨(-558228352158693692373824),(-185040852344067541734946),true⟩⟩
  | 8,3 => ⟨⟨(-4770194379743535790034422),(-4164583018670355206065774),true⟩,⟨(-209543766498518758763311),117835101066741922156074,true⟩⟩
  | 8,4 => ⟨⟨(-5609212366032056254951161),(-4703533802831376720794703),true⟩,⟨(-3224449584780346677198968),(-2525607532200945953921157),true⟩⟩
  | 8,5 => ⟨⟨(-5371359049340756576389627),(-4420330616654187768431187),true⟩,⟨(-4195192989983278152593696),(-3402534282902589578877326),true⟩⟩
  | 8,6 => ⟨⟨(-5023780137476905807799024),(-4055044839063165101254452),true⟩,⟨(-4896508051503503674099977),(-4045736014560265688646336),true⟩⟩
  | 8,7 => ⟨⟨(-4755258417537299235851193),(-3783317000373828405856881),true⟩,⟨(-5276580801440500411150835),(-4398533605841689084748054),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP534Value0_0 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP534Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value0_1 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP534Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value0_2 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP534Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value0_3 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP534Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value0_4 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP534Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value0_5 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP534Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value0_6 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP534Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value0_7 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP534Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP534Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 0 j)=sharedDiskP534Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP534Value0_0
  · exact sharedDiskP534Value0_1
  · exact sharedDiskP534Value0_2
  · exact sharedDiskP534Value0_3
  · exact sharedDiskP534Value0_4
  · exact sharedDiskP534Value0_5
  · exact sharedDiskP534Value0_6
  · exact sharedDiskP534Value0_7
private theorem sharedDiskP534Value1_0 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP534Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value1_1 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP534Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value1_2 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP534Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value1_3 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP534Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value1_4 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP534Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value1_5 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP534Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value1_6 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP534Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value1_7 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP534Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP534Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 1 j)=sharedDiskP534Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP534Value1_0
  · exact sharedDiskP534Value1_1
  · exact sharedDiskP534Value1_2
  · exact sharedDiskP534Value1_3
  · exact sharedDiskP534Value1_4
  · exact sharedDiskP534Value1_5
  · exact sharedDiskP534Value1_6
  · exact sharedDiskP534Value1_7
private theorem sharedDiskP534Value2_0 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP534Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value2_1 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP534Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value2_2 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP534Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value2_3 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP534Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value2_4 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP534Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value2_5 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP534Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value2_6 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP534Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value2_7 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP534Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP534Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 2 j)=sharedDiskP534Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP534Value2_0
  · exact sharedDiskP534Value2_1
  · exact sharedDiskP534Value2_2
  · exact sharedDiskP534Value2_3
  · exact sharedDiskP534Value2_4
  · exact sharedDiskP534Value2_5
  · exact sharedDiskP534Value2_6
  · exact sharedDiskP534Value2_7
private theorem sharedDiskP534Value3_0 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP534Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value3_1 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP534Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value3_2 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP534Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value3_3 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP534Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value3_4 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP534Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value3_5 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP534Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value3_6 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP534Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value3_7 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP534Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP534Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 3 j)=sharedDiskP534Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP534Value3_0
  · exact sharedDiskP534Value3_1
  · exact sharedDiskP534Value3_2
  · exact sharedDiskP534Value3_3
  · exact sharedDiskP534Value3_4
  · exact sharedDiskP534Value3_5
  · exact sharedDiskP534Value3_6
  · exact sharedDiskP534Value3_7
private theorem sharedDiskP534Value4_0 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP534Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value4_1 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP534Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value4_2 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP534Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value4_3 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP534Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value4_4 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP534Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value4_5 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP534Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value4_6 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP534Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value4_7 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP534Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP534Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 4 j)=sharedDiskP534Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP534Value4_0
  · exact sharedDiskP534Value4_1
  · exact sharedDiskP534Value4_2
  · exact sharedDiskP534Value4_3
  · exact sharedDiskP534Value4_4
  · exact sharedDiskP534Value4_5
  · exact sharedDiskP534Value4_6
  · exact sharedDiskP534Value4_7
private theorem sharedDiskP534Value5_0 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP534Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value5_1 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP534Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value5_2 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP534Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value5_3 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP534Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value5_4 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP534Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value5_5 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP534Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value5_6 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP534Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value5_7 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP534Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP534Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 5 j)=sharedDiskP534Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP534Value5_0
  · exact sharedDiskP534Value5_1
  · exact sharedDiskP534Value5_2
  · exact sharedDiskP534Value5_3
  · exact sharedDiskP534Value5_4
  · exact sharedDiskP534Value5_5
  · exact sharedDiskP534Value5_6
  · exact sharedDiskP534Value5_7
private theorem sharedDiskP534Value6_0 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP534Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value6_1 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP534Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value6_2 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP534Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value6_3 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP534Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value6_4 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP534Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value6_5 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP534Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value6_6 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP534Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value6_7 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP534Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP534Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 6 j)=sharedDiskP534Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP534Value6_0
  · exact sharedDiskP534Value6_1
  · exact sharedDiskP534Value6_2
  · exact sharedDiskP534Value6_3
  · exact sharedDiskP534Value6_4
  · exact sharedDiskP534Value6_5
  · exact sharedDiskP534Value6_6
  · exact sharedDiskP534Value6_7
private theorem sharedDiskP534Value7_0 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP534Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value7_1 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP534Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value7_2 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP534Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value7_3 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP534Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value7_4 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP534Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value7_5 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP534Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value7_6 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP534Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value7_7 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP534Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP534Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 7 j)=sharedDiskP534Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP534Value7_0
  · exact sharedDiskP534Value7_1
  · exact sharedDiskP534Value7_2
  · exact sharedDiskP534Value7_3
  · exact sharedDiskP534Value7_4
  · exact sharedDiskP534Value7_5
  · exact sharedDiskP534Value7_6
  · exact sharedDiskP534Value7_7
private theorem sharedDiskP534Value8_0 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP534Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value8_1 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP534Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value8_2 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP534Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value8_3 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP534Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value8_4 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP534Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value8_5 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP534Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value8_6 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP534Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP534Value8_7 : truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP534Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP534Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points 8 j)=sharedDiskP534Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP534Value8_0
  · exact sharedDiskP534Value8_1
  · exact sharedDiskP534Value8_2
  · exact sharedDiskP534Value8_3
  · exact sharedDiskP534Value8_4
  · exact sharedDiskP534Value8_5
  · exact sharedDiskP534Value8_6
  · exact sharedDiskP534Value8_7
theorem sharedDiskP534Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP534Params (sharedChord521Gauss8Points i j)=sharedDiskP534Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP534Values0_eq
  · exact sharedDiskP534Values1_eq
  · exact sharedDiskP534Values2_eq
  · exact sharedDiskP534Values3_eq
  · exact sharedDiskP534Values4_eq
  · exact sharedDiskP534Values5_eq
  · exact sharedDiskP534Values6_eq
  · exact sharedDiskP534Values7_eq
  · exact sharedDiskP534Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP534Box : HorizontalRectangle := ⟨(81/100),(13/16),(316578000813289/549755813888000),(317651742637289/549755813888000),(988479281288566928028139321808441/5192296858534827628530496329220096),(5004444222424131462075396549236281/5192296858534827628530496329220096),(-1116057549387138096422949033794201/324518553658426726783156020576256),(-858352993677021611304140576840345/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP534Grid : CGrid := momentChordGrid sharedDiskP534Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP534Columns : containedInReported sharedDiskP534Grid.re sharedDiskP534Box.reLo sharedDiskP534Box.reHi=true ∧ containedInReported sharedDiskP534Grid.im sharedDiskP534Box.imLo sharedDiskP534Box.imHi=true := by
  rw [sharedDiskP534Grid,momentChordGrid_eq_tabulated sharedDiskP534Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP534Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP534Values_eq]
  decide +kernel
theorem sharedDiskP534Sound : sharedDiskP534Box.Sound := by
  intro t a tl tu al au
  change (((81/100):ℚ):ℝ)≤t at tl
  change t≤(((13/16):ℚ):ℝ) at tu
  change (((316578000813289/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((317651742637289/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP534Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(81/100))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((13/16):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(316578000813289/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((317651742637289/549755813888000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP534Columns.1 sharedDiskP534Columns.2
def sharedDiskP534Rows : List SignRow := [positive_534.toSignRow]
theorem sharedDiskP534Rows_actual : ∀ r∈sharedDiskP534Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP534Rows.all (sharedDiskP534Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP534Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP531Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP532Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP533Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP534Rows_actual
