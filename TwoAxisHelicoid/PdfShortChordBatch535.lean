import TwoAxisHelicoid.PdfSharedChord521Gauss8
import TwoAxisHelicoid.PdfSharedChord521Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP535Params : ChordParams := ⟨⟨(-25604614254005397721842),(-25302720466469937002539),true⟩,⟨1964060212051558948485285,1979233167688728020690743,true⟩,⟨129094322182385871492545,130965489413026894259335,true⟩,⟨235168949031826395292614,238139101404647656204610,true⟩,⟨342539992156419328419409,344661686901634112322343,true⟩,⟨1158778689298952093542178,1159357832673738857953734,true⟩,⟨(-2241372338467447847917705),(-2233380746894476965331983),true⟩,⟨⟨1141860016663757468111464,1170471711008924660075787,true⟩,⟨(-20992740),20992740,true⟩⟩⟩
theorem sharedDiskP535Params_ok : chordParams (Grid.ofRats (13/16) (163/200)) (Grid.ofRats (950935528075919/1649267441664000) (954156753547919/1649267441664000))=sharedDiskP535Params := by decide +kernel
def sharedDiskP535Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3172670718433233886219139),(-2659712193934271484262609),true⟩,⟨(-330238200093157529294706),80191742592792246066898,true⟩⟩
  | 0,1 => ⟨⟨(-2807851134327071802607203),(-2337475014276492464626788),true⟩,⟨(-391521417990245652892619),(-2852236114759340883979),true⟩⟩
  | 0,2 => ⟨⟨(-2544753452261054754728918),(-2107967713384035938890516),true⟩,⟨(-443610201682207365824423),(-75452588632847908948271),true⟩⟩
  | 0,3 => ⟨⟨(-2396784475375824111215722),(-1979703204320736909282500),true⟩,⟨(-475569149044543578999566),(-120351617339782682852694),true⟩⟩
  | 0,4 => ⟨⟨(-3605599642163472556524765),(-3048687349293568981296338),true⟩,⟨(-275561763873464814836039),149281892503561028105628,true⟩⟩
  | 0,5 => ⟨⟨(-4047163250925556715021814),(-3452973123694552163537043),true⟩,⟨(-241432536776519624522310),187790805523242184264134,true⟩⟩
  | 0,6 => ⟨⟨(-4420813400832818855868589),(-3801149729651680236225705),true⟩,⟨(-230724818081689948156997),191443111078481406559913,true⟩⟩
  | 0,7 => ⟨⟨(-4655532512392525472147211),(-4022295770152653171040745),true⟩,⟨(-237284611919342610463897),179401572743355632714267,true⟩⟩
  | 1,0 => ⟨⟨(-1510347494991054292240455),(-1217716518275978517626507),true⟩,⟨(-695385749671267114495566),(-430370949895261993391640),true⟩⟩
  | 1,1 => ⟨⟨(-1317272742648151091036938),(-1052255832051094354507654),true⟩,⟨(-745204360753834944229135),(-501965481012010942663117),true⟩⟩
  | 1,2 => ⟨⟨(-1177191040746515706536501),(-931895978724980495814186),true⟩,⟨(-780327114439303445231897),(-552861259810287688656352),true⟩⟩
  | 1,3 => ⟨⟨(-1097563522966762470791884),(-863299450316755563664285),true⟩,⟨(-799656797015331406133608),(-581078492663436868990174),true⟩⟩
  | 1,4 => ⟨⟨(-1740872628048947915217453),(-1415070715396416072866758),true⟩,⟨(-635425625650860582704088),(-344876197758764545953697),true⟩⟩
  | 1,5 => ⟨⟨(-1981276487543442148283511),(-1621205894584101812926763),true⟩,⟨(-574166231773492038614483),(-258191413707050602886035),true⟩⟩
  | 1,6 => ⟨⟨(-2191668899974797752246118),(-1802281936770666519827492),true⟩,⟨(-522818703822613970709013),(-186102578574706479836262),true⟩⟩
  | 1,7 => ⟨⟨(-2327958707332132456284135),(-1920058696992155159683154),true⟩,⟨(-491077507662612791026443),(-141860482679414020143407),true⟩⟩
  | 2,0 => ⟨⟨(-217934036616130188664691),(-76953909482626591111185),true⟩,⟨(-954613798141236992672523),(-809090690500531923341612),true⟩⟩
  | 2,1 => ⟨⟨(-30835178571867093628330),98835703475614592626073,true⟩,⟨(-965566076650224713641079),(-829148121134103493350262),true⟩⟩
  | 2,2 => ⟨⟨105517806925739824879027,228917457840423475594063,true⟩,⟨(-967842878315400100871044),(-837168979170249223171652),true⟩⟩
  | 2,3 => ⟨⟨183621509506495404402946,304002456454850606676361,true⟩,⟨(-967150230272791327848590),(-839430925725095214103537),true⟩⟩
  | 2,4 => ⟨⟨(-441699449675918855233640),(-283710598441505544074506),true⟩,⟨(-929299211591712490172089),(-770964831062757910230817),true⟩⟩
  | 2,5 => ⟨⟨(-679838631093476475885574),(-499370821736894184557422),true⟩,⟨(-889188947651479965201861),(-714102569742987361218800),true⟩⟩
  | 2,6 => ⟨⟨(-896733853343113427342074),(-689510935735101552784538),true⟩,⟨(-845444639445068544115925),(-648815106955455899684880),true⟩⟩
  | 2,7 => ⟨⟨(-1041720664134403015404270),(-815096988502994137024583),true⟩,⟨(-812858699186230336537862),(-600460099201239273499454),true⟩⟩
  | 3,0 => ⟨⟨1106135199468261366318679,1234142656379611625333377,true⟩,⟨(-928726622059345425614605),(-803212144902224530151724),true⟩⟩
  | 3,1 => ⟨⟨1327576131409814433484959,1462349015296384648559954,true⟩,⟨(-943689663611425764347700),(-813651407615196090892135),true⟩⟩
  | 3,2 => ⟨⟨1497963835205342743039314,1639405449955139975291844,true⟩,⟨(-974543125821757513261245),(-839325015996900543740579),true⟩⟩
  | 3,3 => ⟨⟨1599670420530916011304694,1745805675994084510041777,true⟩,⟨(-1003496377634251845642994),(-864356496175018514862213),true⟩⟩
  | 3,4 => ⟨⟨855066607573742762895446,977599970899091249385819,true⟩,⟨(-933495094879002196648385),(-810620372461444465324441),true⟩⟩
  | 3,5 => ⟨⟨601715635175649524659623,720855141841782107990636,true⟩,⟨(-948429711357184329527929),(-825953066748991396359469),true⟩⟩
  | 3,6 => ⟨⟨382401180386712495729505,500330467707115718316196,true⟩,⟨(-960658721537351300062414),(-836850097736953572084855),true⟩⟩
  | 3,7 => ⟨⟨238757159706297844442214,357740365333278384258768,true⟩,⟨(-965869228551787529778162),(-839738167150110055605431),true⟩⟩
  | 4,0 => ⟨⟨2346433997463228032255031,2578755547708018991668934,true⟩,⟨(-1668177203511374968683080),(-1442818944931981872485491),true⟩⟩
  | 4,1 => ⟨⟨2527226801903929409279897,2804299609719380865373963,true⟩,⟨(-2108389234698273831584690),(-1834548977275782328582494),true⟩⟩
  | 4,2 => ⟨⟨2620101234165916474890898,2943980388066590353068706,true⟩,⟨(-2602831449939110609727531),(-2276362258381726532443065),true⟩⟩
  | 4,3 => ⟨⟨2631572721579962881075936,2989871876723066781695860,true⟩,⟨(-2981654488660268355050984),(-2615360861493010114743698),true⟩⟩
  | 4,4 => ⟨⟨2125754764183499235339238,2322811545943139584078530,true⟩,⟨(-1355986981969193586619818),(-1167314771582559105512429),true⟩⟩
  | 4,5 => ⟨⟨1915294546802423455878900,2087744205460040565918783,true⟩,⟨(-1166490187121535879051532),(-1002404997893092370020987),true⟩⟩
  | 4,6 => ⟨⟨1748910749412432837116980,1905963677810136397549975,true⟩,⟨(-1065659560032249527337634),(-916407148940669100663399),true⟩⟩
  | 4,7 => ⟨⟨1648631930538474516825712,1797774538788253164826139,true⟩,⟨(-1021099181505943916162035),(-879259268439583385031637),true⟩⟩
  | 5,0 => ⟨⟨2446259634635319713389875,2892475575832377910631296,true⟩,⟨(-3986127854509004402503707),(-3514077482816713991707270),true⟩⟩
  | 5,1 => ⟨⟨2327561678092588587020030,2800057755621413987035735,true⟩,⟨(-4292750549223502609613598),(-3787974173384314379429422),true⟩⟩
  | 5,2 => ⟨⟨2204253014107631786892368,2698591763635275926400534,true⟩,⟨(-4548717434451726956917571),(-4016340994559539667434619),true⟩⟩
  | 5,3 => ⟨⟨2115554699057020014808504,2623457723225403397970200,true⟩,⟨(-4707949510376709111771257),(-4158245714203103123906862),true⟩⟩
  | 5,4 => ⟨⟨2535254060732488922687639,2955010636209048147354593,true⟩,⟨(-3679691501560426238196798),(-3240070530106622451695058),true⟩⟩
  | 5,5 => ⟨⟨2589027473442718338894630,2985770240297558349135415,true⟩,⟨(-3415684162198560220354309),(-3003849591025935000304980),true⟩⟩
  | 5,6 => ⟨⟨2615189059748401563798316,2994823656799839324178816,true⟩,⟨(-3221321357385533655492394),(-2829889395531373567812680),true⟩⟩
  | 5,7 => ⟨⟨2624984546686320607718210,2994768994086426627491951,true⟩,⟨(-3110267190181585082085197),(-2730483498934039849847913),true⟩⟩
  | 6,0 => ⟨⟨1008477158147582032950917,1626051548867133363481157,true⟩,⟨(-5931949373218778062248741),(-5239798260553617304963126),true⟩⟩
  | 6,1 => ⟨⟨519423596942940247427768,1179955597717348972121862,true⟩,⟨(-6243222311209629659575985),(-5503483216306947738035883),true⟩⟩
  | 6,2 => ⟨⟨70704537198625819805102,771642839568110610155095,true⟩,⟨(-6455880593259537789909855),(-5675967058571030260024786),true⟩⟩
  | 6,3 => ⟨⟨(-226987956271510252127439),499506129085525210308695,true⟩,⟨(-6563814194253157825761993),(-5760388889691071845279517),true⟩⟩
  | 6,4 => ⟨⟨1436440838234745270021624,2018083654110737661391223,true⟩,⟨(-5570560820834574682675026),(-4923925968955530376103832),true⟩⟩
  | 6,5 => ⟨⟨1755339027204585905090110,2307239313102514008392821,true⟩,⟨(-5224097611369113563333775),(-4617146637192133812817669),true⟩⟩
  | 6,6 => ⟨⟨1961653237410602236760264,2490144132076957061167066,true⟩,⟨(-4949699586608572873222834),(-4373411946143955106783327),true⟩⟩
  | 6,7 => ⟨⟨2068287776011204220777048,2582865687032128607897197,true⟩,⟨(-4786336606389520320801025),(-4228052034481726088224996),true⟩⟩
  | 7,0 => ⟨⟨(-2929657456763854225656670),(-2018384084153495323491874),true⟩,⟨(-6533406359167237575035608),(-5612506194867851560834071),true⟩⟩
  | 7,1 => ⟨⟨(-3721873984001149410614641),(-2776076876298468960634248),true⟩,⟨(-6152171766071900322472279),(-5233465519679591711596387),true⟩⟩
  | 7,2 => ⟨⟨(-4301196845276215930251227),(-3339155667557749222715294),true⟩,⟨(-5713774470379518160719771),(-4813134144925168529816961),true⟩⟩
  | 7,3 => ⟨⟨(-4616340421011001751918202),(-3650333897405074217114481),true⟩,⟨(-5392669723654898145377942),(-4510566863898488396860356),true⟩⟩
  | 7,4 => ⟨⟨(-2061668014684016674452505),(-1199757307647239737028480),true⟩,⟨(-6738353171188460496310652),(-5836359782128532479867002),true⟩⟩
  | 7,5 => ⟨⟨(-1281501129235443536784153),(-472514730445638031400399),true⟩,⟨(-6762764344847289315812268),(-5893315751046373954540121),true⟩⟩
  | 7,6 => ⟨⟨(-704398922345502936497867),60591276157869514491880,true⟩,⟨(-6687807693282022864477333),(-5851296805635872960968445),true⟩⟩
  | 7,7 => ⟨⟨(-378524667536936079885377),360553564503274072425163,true⟩,⟨(-6609503114568442647808843),(-5794981927145550531901743),true⟩⟩
  | 8,0 => ⟨⟨(-5570907791444321833976171),(-4747142742376665128027570),true⟩,⟨(-2130326955616284187287945),(-1555530836557890219918817),true⟩⟩
  | 8,1 => ⟨⟨(-5323702646638975341432108),(-4588772465572939701583849),true⟩,⟨(-1202660127449710554837654),(-741733565667724918682564),true⟩⟩
  | 8,2 => ⟨⟨(-4994052501789877982330466),(-4340111423970630764828640),true⟩,⟨(-552267327738203445765996),(-181454031628066463547559),true⟩⟩
  | 8,3 => ⟨⟨(-4751132517664426128274338),(-4148809089352039357738820),true⟩,⟨(-207538644813824718583708),118130147146388716745538,true⟩⟩
  | 8,4 => ⟨⟨(-5588329241739237250547466),(-4689120939618703713899603),true⟩,⟨(-3186694563467907891016710),(-2494055914487351543375531),true⟩⟩
  | 8,5 => ⟨⟨(-5358816854763794569390170),(-4414244693525581844189409),true⟩,⟨(-4147950075437417478583312),(-3362222100349473499074334),true⟩⟩
  | 8,6 => ⟨⟨(-5020075778525175687209324),(-4057445321379782789100988),true⟩,⟨(-4844156986938102333205937),(-4000507755960171225792133),true⟩⟩
  | 8,7 => ⟨⟨(-4757482286432427959228425),(-3791312292779435337128845),true⟩,⟨(-5222384711899561958160072),(-4351411084839433955367765),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP535Value0_0 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP535Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value0_1 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP535Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value0_2 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP535Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value0_3 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP535Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value0_4 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP535Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value0_5 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP535Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value0_6 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP535Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value0_7 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP535Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP535Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 0 j)=sharedDiskP535Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP535Value0_0
  · exact sharedDiskP535Value0_1
  · exact sharedDiskP535Value0_2
  · exact sharedDiskP535Value0_3
  · exact sharedDiskP535Value0_4
  · exact sharedDiskP535Value0_5
  · exact sharedDiskP535Value0_6
  · exact sharedDiskP535Value0_7
private theorem sharedDiskP535Value1_0 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP535Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value1_1 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP535Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value1_2 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP535Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value1_3 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP535Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value1_4 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP535Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value1_5 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP535Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value1_6 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP535Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value1_7 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP535Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP535Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 1 j)=sharedDiskP535Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP535Value1_0
  · exact sharedDiskP535Value1_1
  · exact sharedDiskP535Value1_2
  · exact sharedDiskP535Value1_3
  · exact sharedDiskP535Value1_4
  · exact sharedDiskP535Value1_5
  · exact sharedDiskP535Value1_6
  · exact sharedDiskP535Value1_7
private theorem sharedDiskP535Value2_0 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP535Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value2_1 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP535Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value2_2 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP535Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value2_3 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP535Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value2_4 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP535Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value2_5 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP535Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value2_6 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP535Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value2_7 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP535Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP535Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 2 j)=sharedDiskP535Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP535Value2_0
  · exact sharedDiskP535Value2_1
  · exact sharedDiskP535Value2_2
  · exact sharedDiskP535Value2_3
  · exact sharedDiskP535Value2_4
  · exact sharedDiskP535Value2_5
  · exact sharedDiskP535Value2_6
  · exact sharedDiskP535Value2_7
private theorem sharedDiskP535Value3_0 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP535Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value3_1 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP535Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value3_2 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP535Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value3_3 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP535Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value3_4 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP535Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value3_5 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP535Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value3_6 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP535Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value3_7 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP535Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP535Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 3 j)=sharedDiskP535Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP535Value3_0
  · exact sharedDiskP535Value3_1
  · exact sharedDiskP535Value3_2
  · exact sharedDiskP535Value3_3
  · exact sharedDiskP535Value3_4
  · exact sharedDiskP535Value3_5
  · exact sharedDiskP535Value3_6
  · exact sharedDiskP535Value3_7
private theorem sharedDiskP535Value4_0 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP535Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value4_1 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP535Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value4_2 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP535Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value4_3 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP535Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value4_4 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP535Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value4_5 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP535Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value4_6 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP535Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value4_7 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP535Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP535Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 4 j)=sharedDiskP535Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP535Value4_0
  · exact sharedDiskP535Value4_1
  · exact sharedDiskP535Value4_2
  · exact sharedDiskP535Value4_3
  · exact sharedDiskP535Value4_4
  · exact sharedDiskP535Value4_5
  · exact sharedDiskP535Value4_6
  · exact sharedDiskP535Value4_7
private theorem sharedDiskP535Value5_0 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP535Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value5_1 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP535Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value5_2 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP535Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value5_3 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP535Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value5_4 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP535Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value5_5 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP535Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value5_6 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP535Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value5_7 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP535Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP535Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 5 j)=sharedDiskP535Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP535Value5_0
  · exact sharedDiskP535Value5_1
  · exact sharedDiskP535Value5_2
  · exact sharedDiskP535Value5_3
  · exact sharedDiskP535Value5_4
  · exact sharedDiskP535Value5_5
  · exact sharedDiskP535Value5_6
  · exact sharedDiskP535Value5_7
private theorem sharedDiskP535Value6_0 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP535Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value6_1 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP535Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value6_2 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP535Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value6_3 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP535Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value6_4 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP535Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value6_5 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP535Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value6_6 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP535Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value6_7 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP535Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP535Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 6 j)=sharedDiskP535Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP535Value6_0
  · exact sharedDiskP535Value6_1
  · exact sharedDiskP535Value6_2
  · exact sharedDiskP535Value6_3
  · exact sharedDiskP535Value6_4
  · exact sharedDiskP535Value6_5
  · exact sharedDiskP535Value6_6
  · exact sharedDiskP535Value6_7
private theorem sharedDiskP535Value7_0 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP535Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value7_1 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP535Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value7_2 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP535Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value7_3 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP535Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value7_4 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP535Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value7_5 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP535Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value7_6 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP535Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value7_7 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP535Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP535Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 7 j)=sharedDiskP535Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP535Value7_0
  · exact sharedDiskP535Value7_1
  · exact sharedDiskP535Value7_2
  · exact sharedDiskP535Value7_3
  · exact sharedDiskP535Value7_4
  · exact sharedDiskP535Value7_5
  · exact sharedDiskP535Value7_6
  · exact sharedDiskP535Value7_7
private theorem sharedDiskP535Value8_0 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP535Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value8_1 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP535Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value8_2 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP535Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value8_3 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP535Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value8_4 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP535Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value8_5 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP535Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value8_6 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP535Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP535Value8_7 : truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP535Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP535Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points 8 j)=sharedDiskP535Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP535Value8_0
  · exact sharedDiskP535Value8_1
  · exact sharedDiskP535Value8_2
  · exact sharedDiskP535Value8_3
  · exact sharedDiskP535Value8_4
  · exact sharedDiskP535Value8_5
  · exact sharedDiskP535Value8_6
  · exact sharedDiskP535Value8_7
theorem sharedDiskP535Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP535Params (sharedChord521Gauss8Points i j)=sharedDiskP535Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP535Values0_eq
  · exact sharedDiskP535Values1_eq
  · exact sharedDiskP535Values2_eq
  · exact sharedDiskP535Values3_eq
  · exact sharedDiskP535Values4_eq
  · exact sharedDiskP535Values5_eq
  · exact sharedDiskP535Values6_eq
  · exact sharedDiskP535Values7_eq
  · exact sharedDiskP535Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP535Box : HorizontalRectangle := ⟨(13/16),(163/200),(950935528075919/1649267441664000),(954156753547919/1649267441664000),(864522581739742270087471886702787/5192296858534827628530496329220096),(4844250290588774672885013610961091/5192296858534827628530496329220096),(-4460257689725916538656316247555715/1298074214633706907132624082305024),(-3438392732819890314180822768598659/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP535Grid : CGrid := momentChordGrid sharedDiskP535Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP535Columns : containedInReported sharedDiskP535Grid.re sharedDiskP535Box.reLo sharedDiskP535Box.reHi=true ∧ containedInReported sharedDiskP535Grid.im sharedDiskP535Box.imLo sharedDiskP535Box.imHi=true := by
  rw [sharedDiskP535Grid,momentChordGrid_eq_tabulated sharedDiskP535Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP535Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP535Values_eq]
  decide +kernel
theorem sharedDiskP535Sound : sharedDiskP535Box.Sound := by
  intro t a tl tu al au
  change (((13/16):ℚ):ℝ)≤t at tl
  change t≤(((163/200):ℚ):ℝ) at tu
  change (((950935528075919/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((954156753547919/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP535Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(13/16))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((163/200):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(950935528075919/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((954156753547919/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP535Columns.1 sharedDiskP535Columns.2
def sharedDiskP535Rows : List SignRow := [positive_535.toSignRow]
theorem sharedDiskP535Rows_actual : ∀ r∈sharedDiskP535Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP535Rows.all (sharedDiskP535Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP535Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP536Params : ChordParams := ⟨⟨(-25908230510148995606194),(-25604614254005397721302),true⟩,⟨1954652645451651971296857,1969750200713860687522570,true⟩,⟨129616879316904437578960,131488209700395033796279,true⟩,⟨237020897965581237371165,239999471037122261186995,true⟩,⟨344492679484751480959698,346614359643583087595445,true⟩,⟨1158196527203099605177994,1158778689298952093543216,true⟩,⟨(-2233380746894476965341101),(-2225432233195393785325152),true⟩,⟨⟨1141185923335568217808618,1169832772809555550071688,true⟩,⟨(-23815332),23815332,true⟩⟩⟩
theorem sharedDiskP536Params_ok : chordParams (Grid.ofRats (163/200) (327/400)) (Grid.ofRats (952142980288751/1649267441664000) (955364205760751/1649267441664000))=sharedDiskP536Params := by decide +kernel
def sharedDiskP536Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3170540948169602970709882),(-2657796934273951499047853),true⟩,⟨(-327668010810977049932044),82498295012139647902432,true⟩⟩
  | 0,1 => ⟨⟨(-2808566479357081277418745),(-2338047983007696091873567),true⟩,⟨(-387963748671205480748739),724378967327900962689,true⟩⟩
  | 0,2 => ⟨⟨(-2547302086757607804566444),(-2110126099190390273184558),true⟩,⟨(-439354779744157707902886),(-70954452506739383785045),true⟩⟩
  | 0,3 => ⟨⟨(-2400212581355328758393989),(-1982679635496165342260983),true⟩,⟨(-470941539357721613662018),(-115486583942309311000478),true⟩⟩
  | 0,4 => ⟨⟨(-3599663554221310242132933),(-3043382599327069816790412),true⟩,⟨(-274090564440159485938475),150229975921873271533079,true⟩⟩
  | 0,5 => ⟨⟨(-4036916140789901765931987),(-3443748689761470480979977),true⟩,⟨(-240888358950378294030487),187700190232491928980351,true⟩⟩
  | 0,6 => ⟨⟨(-4406635910095613627931845),(-3788276807850365823007865),true⟩,⟨(-230805681055340450914541),190798966710850404677490,true⟩⟩
  | 0,7 => ⟨⟨(-4638765982501306777395570),(-4007001854560838145010345),true⟩,⟨(-237548947634876709452816),178617253692929399198429,true⟩⟩
  | 1,0 => ⟨⟨(-1518269998771594267324131),(-1224659806689514137746716),true⟩,⟨(-689307075826958682834903),(-423553853580853854865160),true⟩⟩
  | 1,1 => ⟨⟨(-1325956937342623354334355),(-1059909441687106072501656),true⟩,⟨(-739104851251566190512435),(-495080786342118443323147),true⟩⟩
  | 1,2 => ⟨⟨(-1186395931098493594419905),(-940048458597985145168463),true⟩,⟨(-774305531165610756715384),(-546036423161983496763504),true⟩⟩
  | 1,3 => ⟨⟨(-1107055225041762893887906),(-871731803525427963972813),true⟩,⟨(-793717441408984925584308),(-574331112436541700217424),true⟩⟩
  | 1,4 => ⟨⟨(-1747799713511172710049106),(-1421112572846854225580734),true⟩,⟨(-629540749759983242473318),(-338342425777152835173639),true⟩⟩
  | 1,5 => ⟨⟨(-1987044552907219325080586),(-1626222154683199081368901),true⟩,⟨(-568642809223744738189648),(-252147853210482181185091),true⟩⟩
  | 1,6 => ⟨⟨(-2196308010468869441904028),(-1806311708447081358676981),true⟩,⟨(-517714550461552704112320),(-180614380616785372029853),true⟩⟩
  | 1,7 => ⟨⟨(-2331805590899141904174261),(-1923399204576960835008633),true⟩,⟨(-486283890973541587135663),(-136779160113800406434027),true⟩⟩
  | 2,0 => ⟨⟨(-230283552613499000702029),(-88744048922879874044957),true⟩,⟨(-951395072090402969913926),(-805558398834000022695142),true⟩⟩
  | 2,1 => ⟨⟨(-43832219916682554155425),86293655005527958170156,true⟩,⟨(-963397157693295444114417),(-826686495104333869270661),true⟩⟩
  | 2,2 => ⟨⟨92103927310877605719538,215871358799544234391135,true⟩,⟨(-966501744165518341716971),(-835543293916100703693316),true⟩⟩
  | 2,3 => ⟨⟨169949168980580355435389,290677338261143299361203,true⟩,⟨(-966300240715040050232005),(-838298283856782855432635),true⟩⟩
  | 2,4 => ⟨⟨(-453279164972136960961209),(-294648998061451751417394),true⟩,⟨(-924995019521136797364897),(-766309731017504460680325),true⟩⟩
  | 2,5 => ⟨⟨(-690778404753886278561503),(-509417774299607198058272),true⟩,⟨(-884011394324673775136026),(-708326160587041348413081),true⟩⟩
  | 2,6 => ⟨⟨(-906928942906309034847187),(-698644779045522713914409),true⟩,⟨(-839842827287383915742798),(-642408315529494533624968),true⟩⟩
  | 2,7 => ⟨⟨(-1051410382959796414010308),(-823724700358539479748305),true⟩,⟨(-806994173296758467459239),(-593786371908042670053916),true⟩⟩
  | 3,0 => ⟨⟨1090663028792208935798679,1218563468585244045169736,true⟩,⟨(-933715365599611816917744),(-808102825712141110905706),true⟩⟩
  | 3,1 => ⟨⟨1312020489452822342206584,1446738436020488229854744,true⟩,⟨(-950072060339091744200253),(-819867219514384826270997),true⟩⟩
  | 3,2 => ⟨⟨1482411411611222570723188,1623854579363267370947601,true⟩,⟨(-982020577983445104170026),(-846570149749857190347856),true⟩⟩
  | 3,3 => ⟨⟨1584126166526945302171700,1730303258125653971477714,true⟩,⟨(-1011650811148546928178246),(-872233794124284020776772),true⟩⟩
  | 3,4 => ⟨⟨839877082980544782717002,962274299224678741031273,true⟩,⟨(-936889873412405581015582),(-813972573487413632355172),true⟩⟩
  | 3,5 => ⟨⟨587032557013198795822430,706038891846643490170532,true⟩,⟨(-950174859059555195795054),(-827688370469445448872391),true⟩⟩
  | 3,6 => ⟨⟨368311795335831492149007,486136332393812309572868,true⟩,⟨(-960955358580347373450535),(-837146392575305997390173),true⟩⟩
  | 3,7 => ⟨⟨224906738372048084960493,344021442030411094983288,true⟩,⟨(-965371344696503815064944),(-839095800697397359676262),true⟩⟩
  | 4,0 => ⟨⟨2328968515305898179227624,2561635159706940406305714,true⟩,⟨(-1682795699011278960736161),(-1456727998213502861919505),true⟩⟩
  | 4,1 => ⟨⟨2507121819637845779778721,2784642333570464312746006,true⟩,⟨(-2125343814527454285981335),(-1850627627530709431970186),true⟩⟩
  | 4,2 => ⟨⟨2596322724628880842669860,2920697973650150739681934,true⟩,⟨(-2621389146669321635171839),(-2293933882300518945850573),true⟩⟩
  | 4,3 => ⟨⟨2604634066693356373212959,2963420146167834193086906,true⟩,⟨(-3000742787179249851137669),(-2633433423763663277436676),true⟩⟩
  | 4,4 => ⟨⟨2109618770230012073259851,2306909053562901009437231,true⟩,⟨(-1368303162875919525064765),(-1179084422421769059046362),true⟩⟩
  | 4,5 => ⟨⟨1899636318962763283977859,2072230880938741773333100,true⟩,⟨(-1176968879573343253325217),(-1012462199787507798948754),true⟩⟩
  | 4,6 => ⟨⟨1733361664943595600328589,1890502322893248142134560,true⟩,⟨(-1074862654632976664459951),(-925269905078619274537185),true⟩⟩
  | 4,7 => ⟨⟨1633090159950764341080619,1782291498794478581145287,true⟩,⟨(-1029589300846106577685028),(-887451234634960951958336),true⟩⟩
  | 5,0 => ⟨⟨2410151288354468476313334,2856627077048570441402444,true⟩,⟨(-4003545639534693120439075),(-3530653815374121385134941),true⟩⟩
  | 5,1 => ⟨⟨2288576492393139219392911,2761198789063571590527396,true⟩,⟨(-4308678724502461535825693),(-3803198086779725100077654),true⟩⟩
  | 5,2 => ⟨⟨2162891452883679216354217,2657218702715577990150442,true⟩,⟨(-4563003676885651338367630),(-4030073031358759599413802),true⟩⟩
  | 5,3 => ⟨⟨2072739757184082758910391,2580532589517477848619826,true⟩,⟨(-4721016447470693218670519),(-4170869781899623845564893),true⟩⟩
  | 5,4 => ⟨⟨2502013559421812769483352,2922132036296355357800211,true⟩,⟨(-3698117975495286144622738),(-3257560287080489824621311),true⟩⟩
  | 5,5 => ⟨⟨2558222308666851090140845,2955391258802224476898431,true⟩,⟨(-3434619411605210969877445),(-3021796751708419528608221),true⟩⟩
  | 5,6 => ⟨⟨2586141113481171566504195,2966235857753002411471901,true⟩,⟨(-3240427851986045063991339),(-2847986979224669121925403),true⟩⟩
  | 5,7 => ⟨⟨2596922852415748535084671,2967181904046098750608917,true⟩,⟨(-3129396338785456653977178),(-2748598038052439737795449),true⟩⟩
  | 6,0 => ⟨⟨955322079425130232665769,1572663870456709694555457,true⟩,⟨(-5929597244772940220010843),(-5237848591775530902127936),true⟩⟩
  | 6,1 => ⟨⟨465217750596998649632836,1126167819637826558994311,true⟩,⟨(-6233891682111964867906409),(-5494560089993259482639160),true⟩⟩
  | 6,2 => ⟨⟨16658967046088334908716,717588780075034258541135,true⟩,⟨(-6440287151296085400730113),(-5661403691436430050776425),true⟩⟩
  | 6,3 => ⟨⟨(-280594820092212129364081),445780946990033392600484,true⟩,⟨(-6544185161860165933413531),(-5742211745995552462944412),true⟩⟩
  | 6,4 => ⟨⟨1386527672026916808172076,1967313007710161374281534,true⟩,⟨(-5573809600387041599694468),(-4927638137174015884110514),true⟩⟩
  | 6,5 => ⟨⟨1708059346548096189782007,2259451063915400895010339,true⟩,⟨(-5232024037884550351372249),(-4625101942683236947212088),true⟩⟩
  | 6,6 => ⟨⟨1916689350846207149560287,2444899372860595625866835,true⟩,⟨(-4960599288190431343943675),(-4384067060036095333964720),true⟩⟩
  | 6,7 => ⟨⟨2024767318453443661427094,2539182544549216225461815,true⟩,⟨(-4798743991666136122599138),(-4240076822420544846429193),true⟩⟩
  | 7,0 => ⟨⟨(-2961641706596303587797047),(-2053611381376520240752507),true⟩,⟨(-6484330610805991545568866),(-5568691776449131979377148),true⟩⟩
  | 7,1 => ⟨⟨(-3742457980354541913354412),(-2800994166466731691263890),true⟩,⟨(-6098549566500709955683091),(-5186043221112773735981081),true⟩⟩
  | 7,2 => ⟨⟨(-4311836985115021089393202),(-3354927390579452003305364),true⟩,⟨(-5658974194298845764368712),(-4765071367432514260601649),true⟩⟩
  | 7,3 => ⟨⟨(-4620890593412253762483272),(-3660437630287113428809271),true⟩,⟨(-5338361198561423660582023),(-4463198580704390532876442),true⟩⟩
  | 7,4 => ⟨⟨(-2103512159220902270257770),(-1243692933068977909084013),true⟩,⟨(-6696894548578022083984243),(-5798989508707503625913825),true⟩⟩
  | 7,5 => ⟨⟨(-1329905335694751841178286),(-522036589590907911543353),true⟩,⟨(-6729826913587696121225789),(-5863351657348866875162663),true⟩⟩
  | 7,6 => ⟨⟨(-756198938502556671068495),8159625617998932293612,true⟩,⟨(-6661942056048031445168671),(-5827569082462428970386969),true⟩⟩
  | 7,7 => ⟨⟨(-431660900027829004230647),307139554306666049084996,true⟩,⟨(-6587861444133967167073211),(-5775008837789868293917439),true⟩⟩
  | 8,0 => ⟨⟨(-5545808409320056669740789),(-4727872054042882031628550),true⟩,⟨(-2105291378010674863831602),(-1535339006405733340429457),true⟩⟩
  | 8,1 => ⟨⟨(-5299148967530891972242125),(-4569073804264023806418217),true⟩,⟨(-1188980267534994114376155),(-731483878304994676828494),true⟩⟩
  | 8,2 => ⟨⟨(-4972491058945535725625640),(-4322434234474149974801566),true⟩,⟨(-546389147996211123116201),(-177908232392757082079541),true⟩⟩
  | 8,3 => ⟨⟨(-4732189273386489253446567),(-4133109154889440200292638),true⟩,⟨(-205557710919681339313129),118432067460353652829785,true⟩⟩
  | 8,4 => ⟨⟨(-5567394600172799529921932),(-4674574818265896055855232),true⟩,⟨(-3149457338582134015431240),(-2462924589980938131888745),true⟩⟩
  | 8,5 => ⟨⟨(-5345996053197575871071511),(-4407813304148656206340690),true⟩,⟨(-4101271908266610795310924),(-3322379112062398636196406),true⟩⟩
  | 8,6 => ⟨⟨(-5015895419514294596735253),(-4059321541120423449026809),true⟩,⟨(-4792330807233303728696698),(-3955720538601615714511942),true⟩⟩
  | 8,7 => ⟨⟨(-4759116269833791730536257),(-3798682385052623997482920),true⟩,⟨(-5168656711053023946189219),(-4304683490448143822015796),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP536Value0_0 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP536Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value0_1 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP536Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value0_2 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP536Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value0_3 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP536Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value0_4 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP536Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value0_5 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP536Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value0_6 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP536Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value0_7 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP536Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP536Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 0 j)=sharedDiskP536Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP536Value0_0
  · exact sharedDiskP536Value0_1
  · exact sharedDiskP536Value0_2
  · exact sharedDiskP536Value0_3
  · exact sharedDiskP536Value0_4
  · exact sharedDiskP536Value0_5
  · exact sharedDiskP536Value0_6
  · exact sharedDiskP536Value0_7
private theorem sharedDiskP536Value1_0 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP536Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value1_1 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP536Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value1_2 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP536Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value1_3 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP536Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value1_4 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP536Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value1_5 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP536Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value1_6 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP536Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value1_7 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP536Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP536Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 1 j)=sharedDiskP536Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP536Value1_0
  · exact sharedDiskP536Value1_1
  · exact sharedDiskP536Value1_2
  · exact sharedDiskP536Value1_3
  · exact sharedDiskP536Value1_4
  · exact sharedDiskP536Value1_5
  · exact sharedDiskP536Value1_6
  · exact sharedDiskP536Value1_7
private theorem sharedDiskP536Value2_0 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP536Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value2_1 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP536Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value2_2 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP536Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value2_3 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP536Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value2_4 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP536Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value2_5 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP536Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value2_6 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP536Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value2_7 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP536Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP536Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 2 j)=sharedDiskP536Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP536Value2_0
  · exact sharedDiskP536Value2_1
  · exact sharedDiskP536Value2_2
  · exact sharedDiskP536Value2_3
  · exact sharedDiskP536Value2_4
  · exact sharedDiskP536Value2_5
  · exact sharedDiskP536Value2_6
  · exact sharedDiskP536Value2_7
private theorem sharedDiskP536Value3_0 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP536Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value3_1 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP536Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value3_2 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP536Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value3_3 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP536Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value3_4 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP536Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value3_5 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP536Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value3_6 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP536Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value3_7 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP536Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP536Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 3 j)=sharedDiskP536Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP536Value3_0
  · exact sharedDiskP536Value3_1
  · exact sharedDiskP536Value3_2
  · exact sharedDiskP536Value3_3
  · exact sharedDiskP536Value3_4
  · exact sharedDiskP536Value3_5
  · exact sharedDiskP536Value3_6
  · exact sharedDiskP536Value3_7
private theorem sharedDiskP536Value4_0 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP536Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value4_1 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP536Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value4_2 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP536Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value4_3 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP536Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value4_4 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP536Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value4_5 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP536Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value4_6 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP536Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value4_7 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP536Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP536Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 4 j)=sharedDiskP536Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP536Value4_0
  · exact sharedDiskP536Value4_1
  · exact sharedDiskP536Value4_2
  · exact sharedDiskP536Value4_3
  · exact sharedDiskP536Value4_4
  · exact sharedDiskP536Value4_5
  · exact sharedDiskP536Value4_6
  · exact sharedDiskP536Value4_7
private theorem sharedDiskP536Value5_0 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP536Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value5_1 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP536Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value5_2 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP536Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value5_3 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP536Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value5_4 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP536Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value5_5 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP536Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value5_6 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP536Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value5_7 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP536Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP536Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 5 j)=sharedDiskP536Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP536Value5_0
  · exact sharedDiskP536Value5_1
  · exact sharedDiskP536Value5_2
  · exact sharedDiskP536Value5_3
  · exact sharedDiskP536Value5_4
  · exact sharedDiskP536Value5_5
  · exact sharedDiskP536Value5_6
  · exact sharedDiskP536Value5_7
private theorem sharedDiskP536Value6_0 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP536Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value6_1 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP536Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value6_2 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP536Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value6_3 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP536Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value6_4 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP536Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value6_5 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP536Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value6_6 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP536Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value6_7 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP536Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP536Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 6 j)=sharedDiskP536Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP536Value6_0
  · exact sharedDiskP536Value6_1
  · exact sharedDiskP536Value6_2
  · exact sharedDiskP536Value6_3
  · exact sharedDiskP536Value6_4
  · exact sharedDiskP536Value6_5
  · exact sharedDiskP536Value6_6
  · exact sharedDiskP536Value6_7
private theorem sharedDiskP536Value7_0 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP536Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value7_1 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP536Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value7_2 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP536Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value7_3 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP536Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value7_4 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP536Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value7_5 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP536Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value7_6 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP536Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value7_7 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP536Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP536Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 7 j)=sharedDiskP536Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP536Value7_0
  · exact sharedDiskP536Value7_1
  · exact sharedDiskP536Value7_2
  · exact sharedDiskP536Value7_3
  · exact sharedDiskP536Value7_4
  · exact sharedDiskP536Value7_5
  · exact sharedDiskP536Value7_6
  · exact sharedDiskP536Value7_7
private theorem sharedDiskP536Value8_0 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP536Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value8_1 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP536Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value8_2 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP536Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value8_3 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP536Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value8_4 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP536Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value8_5 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP536Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value8_6 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP536Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP536Value8_7 : truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP536Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP536Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points 8 j)=sharedDiskP536Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP536Value8_0
  · exact sharedDiskP536Value8_1
  · exact sharedDiskP536Value8_2
  · exact sharedDiskP536Value8_3
  · exact sharedDiskP536Value8_4
  · exact sharedDiskP536Value8_5
  · exact sharedDiskP536Value8_6
  · exact sharedDiskP536Value8_7
theorem sharedDiskP536Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP536Params (sharedChord521Gauss8Points i j)=sharedDiskP536Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP536Values0_eq
  · exact sharedDiskP536Values1_eq
  · exact sharedDiskP536Values2_eq
  · exact sharedDiskP536Values3_eq
  · exact sharedDiskP536Values4_eq
  · exact sharedDiskP536Values5_eq
  · exact sharedDiskP536Values6_eq
  · exact sharedDiskP536Values7_eq
  · exact sharedDiskP536Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP536Box : HorizontalRectangle := ⟨(163/200),(327/400),(952142980288751/1649267441664000),(955364205760751/1649267441664000),(370159021222239635038691980499869/2596148429267413814265248164610048),(2342649559853430550469553099135901/2596148429267413814265248164610048),(-4456190066522731481061812703362119/1298074214633706907132624082305024),(-3442907900233724069475470865628231/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP536Grid : CGrid := momentChordGrid sharedDiskP536Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP536Columns : containedInReported sharedDiskP536Grid.re sharedDiskP536Box.reLo sharedDiskP536Box.reHi=true ∧ containedInReported sharedDiskP536Grid.im sharedDiskP536Box.imLo sharedDiskP536Box.imHi=true := by
  rw [sharedDiskP536Grid,momentChordGrid_eq_tabulated sharedDiskP536Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP536Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP536Values_eq]
  decide +kernel
theorem sharedDiskP536Sound : sharedDiskP536Box.Sound := by
  intro t a tl tu al au
  change (((163/200):ℚ):ℝ)≤t at tl
  change t≤(((327/400):ℚ):ℝ) at tu
  change (((952142980288751/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((955364205760751/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP536Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(163/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((327/400):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(952142980288751/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((955364205760751/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP536Columns.1 sharedDiskP536Columns.2
def sharedDiskP536Rows : List SignRow := [positive_536.toSignRow]
theorem sharedDiskP536Rows_actual : ∀ r∈sharedDiskP536Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP536Rows.all (sharedDiskP536Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP536Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP537Params : ChordParams := ⟨⟨(-26213562742724451955646),(-25908230510148995605648),true⟩,⟨1945285780087896496141177,1960308520608129786705162,true⟩,⟨130136537144050481051479,132007990525431726802671,true⟩,⟨238879272673671686218465,241866230974262099166759,true⟩,⟨346443471812227212909803,348565102380009686125806,true⟩,⟨1157611363486957971833342,1158196527203099605179044,true⟩,⟨(-2225432233195393785334261),(-2217526436123592061329556),true⟩,⟨⟨1140507626726167416756616,1169188974433141903277184,true⟩,⟨(-26996911),26996911,true⟩⟩⟩
theorem sharedDiskP537Params_ok : chordParams (Grid.ofRats (327/400) (41/50)) (Grid.ofRats (953356365604559/1649267441664000) (956577591076559/1649267441664000))=sharedDiskP537Params := by decide +kernel
def sharedDiskP537Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3168364190761274094415701),(-2655802710039556875475538),true⟩,⟨(-325158681542589515455950),84778649219926217482481,true⟩⟩
  | 0,1 => ⟨⟨(-2809214767986427037940288),(-2338527985967128442647901),true⟩,⟨(-384474507230238233315648),4270537303377912905389,true⟩⟩
  | 0,2 => ⟨⟨(-2549773428652575904867658),(-2112185425368564180384581),true⟩,⟨(-435170819144627748386885),(-66504590917958344518689),true⟩⟩
  | 0,3 => ⟨⟨(-2403560208224019983383110),(-1985554797965845052256570),true⟩,⟨(-466385922254384409439319),(-110670605710260603205353),true⟩⟩
  | 0,4 => ⟨⟨(-3593713779459077936601150),(-3038025116460092396859982),true⟩,⟨(-272668541539035697748732),151170671271701583811950,true⟩⟩
  | 0,5 => ⟨⟨(-4026699670991434990858814),(-3434509496201878755996325),true⟩,⟨(-240381561827677851927671),187618312500945853180898,true⟩⟩
  | 0,6 => ⟨⟨(-4392533827951036737977960),(-3775429579127176970067240),true⟩,⟨(-230916546499867905305886),190172344138259574731821,true⟩⟩
  | 0,7 => ⟨⟨(-4622105873675170163206029),(-3991762392934233945887720),true⟩,⟨(-237841019669636517673631),177852161037934240683162,true⟩⟩
  | 1,0 => ⟨⟨(-1526099358000268569526658),(-1231498212125076577032832),true⟩,⟨(-683280382740254708274126),(-416774747379530290574663),true⟩⟩
  | 1,1 => ⟨⟨(-1334546201830532002520762),(-1067457567328929951850633),true⟩,⟨(-733047151078120558427035),(-488224876499895784071345),true⟩⟩
  | 1,2 => ⟨⟨(-1195504389769794060948499),(-948094697700119163064907),true⟩,⟨(-768317148349053367473703),(-539232373475963510811556),true⟩⟩
  | 1,3 => ⟨⟨(-1116449527755657498254212),(-880057344185492423788115),true⟩,⟨(-787805973067345547218410),(-567599544708567582586680),true⟩⟩
  | 1,4 => ⟨⟨(-1754635730658144284910595),(-1427049875756430048230464),true⟩,⟨(-623717250645792438485921),(-331854524739763464375725),true⟩⟩
  | 1,5 => ⟨⟨(-1992724247491914500325096),(-1631134278473410470768004),true⟩,⟨(-563187329623175069553318),(-246154565290446289940243),true⟩⟩
  | 1,6 => ⟨⟨(-2200862085747870562887613),(-1810238295588150847823112),true⟩,⟨(-512681481945133252947392),(-175177160190914742738861),true⟩⟩
  | 1,7 => ⟨⟨(-2335570300144495598773165),(-1926637665884323553788778),true⟩,⟨(-481562185771641365697757),(-131747806564594278180014),true⟩⟩
  | 2,0 => ⟨⟨(-242522847214796054336176),(-100414686866340482215891),true⟩,⟨(-948136881299339335710926),(-801977269673633722124669),true⟩⟩
  | 2,1 => ⟨⟨(-56716917308307464345048),73872558212776182550713,true⟩,⟨(-961175298070886678887426),(-824164115807413633973131),true⟩⟩
  | 2,2 => ⟨⟨78802214342502601975784,202945727007363987186598,true⟩,⟨(-965099006087690763775546),(-833849279890528598173831),true⟩⟩
  | 2,3 => ⟨⟨156388649615268804646786,277471859533172132726379,true⟩,⟨(-965384209818016716860062),(-837093468936405634605873),true⟩⟩
  | 2,4 => ⟨⟨(-464752594518672926558469),(-305470350890685536522472),true⟩,⟨(-920669177039482481465980),(-761621730951501699035472),true⟩⟩
  | 2,5 => ⟨⟨(-701614145387121785766473),(-519350896276274288021716),true⟩,⟨(-878831096693627800976364),(-702535309341304669419364),true⟩⟩
  | 2,6 => ⟨⟨(-917023761498557643299148),(-707669903691386877228747),true⟩,⟨(-834254350918366300210732),(-636003688458510769992527),true⟩⟩
  | 2,7 => ⟨⟨(-1061001967391957753516243),(-832245135309085435833726),true⟩,⟨(-801153643254952523965949),(-587124806570402572836901),true⟩⟩
  | 3,0 => ⟨⟨1075249803926157546976675,1203049888425150997929074,true⟩,⟨(-938617653903621273330338),(-812903581332363969945472),true⟩⟩
  | 3,1 => ⟨⟨1296497077674759936636516,1431165049736415919383460,true⟩,⟨(-956368400206530180431538),(-825994872820221613254612),true⟩⟩
  | 3,2 => ⟨⟨1466866933803649579829996,1608315238686087722540286,true⟩,⟨(-989412067904806341103214),(-853728295861431453086264),true⟩⟩
  | 3,3 => ⟨⟨1568573884114594346897729,1714795537754814449896500,true⟩,⟨(-1019718810308878777958308),(-880024298693543449399797),true⟩⟩
  | 3,4 => ⟨⟨824769837806286771378276,947039380156283250402874,true⟩,⟨(-940199267706735375618494),(-817234358080935656115758),true⟩⟩
  | 3,5 => ⟨⟨572447720504371901996346,691331075783550946698541,true⟩,⟨(-951838976293516675042476),(-829335971750657316438582),true⟩⟩
  | 3,6 => ⟨⟨354328651608456493323313,472060055071194503500693,true⟩,⟨(-961178196515466550402021),(-837360705198353380145914),true⟩⟩
  | 3,7 => ⟨⟨211167607784176270166598,330423910055137611633772,true⟩,⟨(-964804535498429240849079),(-838376985274872527089781),true⟩⟩
  | 4,0 => ⟨⟨2311338541248885383209084,2544345835919655103581030,true⟩,⟨(-1697271509179804375022102),(-1470501217778719644097595),true⟩⟩
  | 4,1 => ⟨⟨2486799939197951970251112,2764759389362373439586892,true⟩,⟨(-2142093617485942954866723),(-1866513310320353538442322),true⟩⟩
  | 4,2 => ⟨⟨2572293618705166940247953,2897151160083616336027921,true⟩,⟨(-2639657938429028053774378),(-2311234606246848785648498),true⟩⟩
  | 4,3 => ⟨⟨2577435836883215725900389,2936691111451563875978150,true⟩,⟨(-3019470414579483178863737),(-2651168446112165550423650),true⟩⟩
  | 4,4 => ⟨⟨2093372336288141194499817,2290894717259320047390052,true⟩,⟨(-1380510618969134881339290),(-1190748962934427198414067),true⟩⟩
  | 4,5 => ⟨⟨1883912506818284964093102,2056652530960363740905800,true⟩,⟨(-1187353765419386086134655),(-1022427249614318081191510),true⟩⟩
  | 4,6 => ⟨⟨1717778727992973564429502,1875008870047789923140959,true⟩,⟨(-1083977322371400130601704),(-934044747354566821255149),true⟩⟩
  | 4,7 => ⟨⟨1617532199310150248700847,1766794641257054524333161,true⟩,⟨(-1037992540141767633052740),(-895556257482502126253198),true⟩⟩
  | 5,0 => ⟨⟨2373833460496706493842724,2820541401447976336574913,true⟩,⟨(-4020398295745565728386626),(-3546702480511266909357247),true⟩⟩
  | 5,1 => ⟨⟨2249420340098533788035543,2722138521348469856798926,true⟩,⟨(-4323980002667737676107451),(-3817836828985226714273791),true⟩⟩
  | 5,2 => ⟨⟨2121400258787609309307939,2615683738670035670544100,true⟩,⟨(-4576613593066569905455769),(-4043173838862382056548038),true⟩⟩
  | 5,3 => ⟨⟨2029825354563246428154352,2537474678879094241362723,true⟩,⟨(-4733377801988485360929608),(-4182835330340470661832390),true⟩⟩
  | 5,4 => ⟨⟨2468536369175052812320453,2888991939819847588827263,true⟩,⟨(-3716042346348497386044672),(-3274581015351976700817581),true⟩⟩
  | 5,5 => ⟨⟨2527165595559934422982150,2924738543432381276564517,true⟩,⟨(-3453106853633128576628606),(-3039325378997183355991854),true⟩⟩
  | 5,6 => ⟨⟨2556835554595085437649494,2937370241540848344374363,true⟩,⟨(-3259126027161996285999638),(-2865702741425349807356541),true⟩⟩
  | 5,7 => ⟨⟨2568601888234084584732115,2939316483525407540134294,true⟩,⟨(-3148139417877033520987919),(-2766351436111688624572619),true⟩⟩
  | 6,0 => ⟨⟨902447813350856649310506,1519511779727692315111277,true⟩,⟨(-5926394942726808144938565),(-5235110201653722659365566),true⟩⟩
  | 6,1 => ⟨⟨411440320891708246243909,1072749748804929461530670,true⟩,⟨(-6223728104712954124287937),(-5484872850728491359726621),true⟩⟩
  | 6,2 => ⟨⟨(-36967086643605317724187),664026316389006488763065,true⟩,⟨(-6423904848940681825795620),(-5646118196952389606968978),true⟩⟩
  | 6,3 => ⟨⟨(-333574750694617043694755),392621125803432983884696,true⟩,⟨(-6523809024649855017928383),(-5723351503308974984939757),true⟩⟩
  | 6,4 => ⟨⟨1336746341574211255069926,1916638581018073448020126,true⟩,⟨(-5576231578138489598587845),(-4930577880899378220636566),true⟩⟩
  | 6,5 => ⟨⟨1660803692325335065293076,2211651291357242110166727,true⟩,⟨(-5239162423625412566696796),(-4632321548273182581558008),true⟩⟩
  | 6,6 => ⟨⟨1871678746421543040647244,2399573282139436215744578,true⟩,⟨(-4970752002066801674602377),(-4394024969712542810536530),true⟩⟩
  | 6,7 => ⟨⟨1981163564729573961266375,2495382327500164614773775,true⟩,⟨(-4810431927124459758490679),(-4251430144884338005089649),true⟩⟩
  | 7,0 => ⟨⟨(-2992705009097729771132368),(-2087945471548825104168321),true⟩,⟨(-6435186981036361421203697),(-5524808181059307619580670),true⟩⟩
  | 7,1 => ⟨⟨(-3762199143244201990554384),(-2825072867344497772008501),true⟩,⟨(-6045106924708298275943084),(-5138769121151238388409838),true⟩⟩
  | 7,2 => ⟨⟨(-4321756959986529738669883),(-3369961843176192110658372),true⟩,⟨(-5604525951775021335782335),(-4717305556452090689018920),true⟩⟩
  | 7,3 => ⟨⟨(-4624816656827035796612819),(-3669886894781598940130949),true⟩,⟨(-5284488999771764481932685),(-4416198532903416155526846),true⟩⟩
  | 7,4 => ⟨⟨(-2144446034076202013334851),(-1286764862433436815506790),true⟩,⟨(-6655107793273436786918491),(-5761317874958507134253978),true⟩⟩
  | 7,5 => ⟨⟨(-1377480948653457000055715),(-570787559123837580300492),true⟩,⟨(-6696354846983793144927115),(-5832899544522949391612952),true⟩⟩
  | 7,6 => ⟨⟨(-807268846783978832716404),(-43446471176243981398480),true⟩,⟨(-6635414177682590230242018),(-5803236687024999638488915),true⟩⟩
  | 7,7 => ⟨⟨(-484135453045359258490891),254326117830986663417958,true⟩,⟨(-6565497340122527175692344),(-5754375546666824777214610),true⟩⟩
  | 8,0 => ⟨⟨(-5520823990113248289378071),(-4708633719639217458979781),true⟩,⟨(-2080623498364247149772815),(-1515431981056489546820534),true⟩⟩
  | 8,1 => ⟨⟨(-5274762680509180057031674),(-4549471854199244827693505),true⟩,⟨(-1175501530918247393507403),(-721375005924141044011702),true⟩⟩
  | 8,2 => ⟨⟨(-4951078002601856956087146),(-4304850147160276246294858),true⟩,⟨(-540592444271215414332031),(-174402451603094811866672),true⟩⟩
  | 8,3 => ⟨⟨(-4713363670947393016411021),(-4117482572699302796042729),true⟩,⟨(-203600710418823639363846),118740967761585546374056,true⟩⟩
  | 8,4 => ⟨⟨(-5546414867834241099938059),(-4659902243343961020032363),true⟩,⟨(-3112730540373732733195211),(-2432207162981076325778627),true⟩⟩
  | 8,5 => ⟨⟨(-5332908631554055935880601),(-4401048093268638380413543),true⟩,⟨(-4055153483000217518885141),(-3283000760024090553171552),true⟩⟩
  | 8,6 => ⟨⟨(-5011254671833271514528776),(-4060688105145047137147370),true⟩,⟨(-4741028575753161270515058),(-3911373213587067231866771),true⟩⟩
  | 8,7 => ⟨⟨(-4760177432735936738128088),(-3805442949536071858425407),true⟩,⟨(-5115399008602802537191882),(-4258352368847025100091627),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP537Value0_0 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP537Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value0_1 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP537Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value0_2 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP537Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value0_3 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP537Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value0_4 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP537Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value0_5 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP537Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value0_6 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP537Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value0_7 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP537Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP537Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 0 j)=sharedDiskP537Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP537Value0_0
  · exact sharedDiskP537Value0_1
  · exact sharedDiskP537Value0_2
  · exact sharedDiskP537Value0_3
  · exact sharedDiskP537Value0_4
  · exact sharedDiskP537Value0_5
  · exact sharedDiskP537Value0_6
  · exact sharedDiskP537Value0_7
private theorem sharedDiskP537Value1_0 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP537Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value1_1 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP537Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value1_2 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP537Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value1_3 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP537Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value1_4 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP537Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value1_5 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP537Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value1_6 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP537Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value1_7 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP537Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP537Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 1 j)=sharedDiskP537Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP537Value1_0
  · exact sharedDiskP537Value1_1
  · exact sharedDiskP537Value1_2
  · exact sharedDiskP537Value1_3
  · exact sharedDiskP537Value1_4
  · exact sharedDiskP537Value1_5
  · exact sharedDiskP537Value1_6
  · exact sharedDiskP537Value1_7
private theorem sharedDiskP537Value2_0 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP537Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value2_1 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP537Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value2_2 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP537Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value2_3 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP537Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value2_4 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP537Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value2_5 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP537Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value2_6 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP537Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value2_7 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP537Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP537Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 2 j)=sharedDiskP537Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP537Value2_0
  · exact sharedDiskP537Value2_1
  · exact sharedDiskP537Value2_2
  · exact sharedDiskP537Value2_3
  · exact sharedDiskP537Value2_4
  · exact sharedDiskP537Value2_5
  · exact sharedDiskP537Value2_6
  · exact sharedDiskP537Value2_7
private theorem sharedDiskP537Value3_0 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP537Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value3_1 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP537Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value3_2 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP537Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value3_3 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP537Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value3_4 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP537Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value3_5 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP537Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value3_6 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP537Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value3_7 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP537Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP537Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 3 j)=sharedDiskP537Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP537Value3_0
  · exact sharedDiskP537Value3_1
  · exact sharedDiskP537Value3_2
  · exact sharedDiskP537Value3_3
  · exact sharedDiskP537Value3_4
  · exact sharedDiskP537Value3_5
  · exact sharedDiskP537Value3_6
  · exact sharedDiskP537Value3_7
private theorem sharedDiskP537Value4_0 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP537Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value4_1 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP537Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value4_2 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP537Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value4_3 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP537Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value4_4 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP537Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value4_5 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP537Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value4_6 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP537Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value4_7 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP537Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP537Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 4 j)=sharedDiskP537Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP537Value4_0
  · exact sharedDiskP537Value4_1
  · exact sharedDiskP537Value4_2
  · exact sharedDiskP537Value4_3
  · exact sharedDiskP537Value4_4
  · exact sharedDiskP537Value4_5
  · exact sharedDiskP537Value4_6
  · exact sharedDiskP537Value4_7
private theorem sharedDiskP537Value5_0 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP537Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value5_1 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP537Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value5_2 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP537Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value5_3 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP537Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value5_4 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP537Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value5_5 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP537Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value5_6 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP537Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value5_7 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP537Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP537Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 5 j)=sharedDiskP537Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP537Value5_0
  · exact sharedDiskP537Value5_1
  · exact sharedDiskP537Value5_2
  · exact sharedDiskP537Value5_3
  · exact sharedDiskP537Value5_4
  · exact sharedDiskP537Value5_5
  · exact sharedDiskP537Value5_6
  · exact sharedDiskP537Value5_7
private theorem sharedDiskP537Value6_0 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP537Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value6_1 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP537Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value6_2 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP537Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value6_3 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP537Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value6_4 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP537Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value6_5 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP537Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value6_6 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP537Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value6_7 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP537Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP537Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 6 j)=sharedDiskP537Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP537Value6_0
  · exact sharedDiskP537Value6_1
  · exact sharedDiskP537Value6_2
  · exact sharedDiskP537Value6_3
  · exact sharedDiskP537Value6_4
  · exact sharedDiskP537Value6_5
  · exact sharedDiskP537Value6_6
  · exact sharedDiskP537Value6_7
private theorem sharedDiskP537Value7_0 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP537Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value7_1 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP537Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value7_2 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP537Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value7_3 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP537Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value7_4 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP537Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value7_5 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP537Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value7_6 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP537Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value7_7 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP537Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP537Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 7 j)=sharedDiskP537Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP537Value7_0
  · exact sharedDiskP537Value7_1
  · exact sharedDiskP537Value7_2
  · exact sharedDiskP537Value7_3
  · exact sharedDiskP537Value7_4
  · exact sharedDiskP537Value7_5
  · exact sharedDiskP537Value7_6
  · exact sharedDiskP537Value7_7
private theorem sharedDiskP537Value8_0 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP537Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value8_1 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP537Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value8_2 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP537Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value8_3 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP537Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value8_4 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP537Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value8_5 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP537Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value8_6 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP537Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP537Value8_7 : truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP537Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP537Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points 8 j)=sharedDiskP537Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP537Value8_0
  · exact sharedDiskP537Value8_1
  · exact sharedDiskP537Value8_2
  · exact sharedDiskP537Value8_3
  · exact sharedDiskP537Value8_4
  · exact sharedDiskP537Value8_5
  · exact sharedDiskP537Value8_6
  · exact sharedDiskP537Value8_7
theorem sharedDiskP537Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP537Params (sharedChord521Gauss8Points i j)=sharedDiskP537Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP537Values0_eq
  · exact sharedDiskP537Values1_eq
  · exact sharedDiskP537Values2_eq
  · exact sharedDiskP537Values3_eq
  · exact sharedDiskP537Values4_eq
  · exact sharedDiskP537Values5_eq
  · exact sharedDiskP537Values6_eq
  · exact sharedDiskP537Values7_eq
  · exact sharedDiskP537Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP537Box : HorizontalRectangle := ⟨(327/400),(41/50),(953356365604559/1649267441664000),(956577591076559/1649267441664000),(1231979517832259724227272038300457/10384593717069655257060992658440192),(4527482739891409456137058188074389/5192296858534827628530496329220096),(-278250060599741562517429009655747/81129638414606681695789005144064),(-215436662036596259685001562040259/81129638414606681695789005144064),true,[]⟩
noncomputable def sharedDiskP537Grid : CGrid := momentChordGrid sharedDiskP537Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP537Columns : containedInReported sharedDiskP537Grid.re sharedDiskP537Box.reLo sharedDiskP537Box.reHi=true ∧ containedInReported sharedDiskP537Grid.im sharedDiskP537Box.imLo sharedDiskP537Box.imHi=true := by
  rw [sharedDiskP537Grid,momentChordGrid_eq_tabulated sharedDiskP537Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP537Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP537Values_eq]
  decide +kernel
theorem sharedDiskP537Sound : sharedDiskP537Box.Sound := by
  intro t a tl tu al au
  change (((327/400):ℚ):ℝ)≤t at tl
  change t≤(((41/50):ℚ):ℝ) at tu
  change (((953356365604559/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((956577591076559/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP537Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(327/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((41/50):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(953356365604559/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((956577591076559/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP537Columns.1 sharedDiskP537Columns.2
def sharedDiskP537Rows : List SignRow := [positive_537.toSignRow]
theorem sharedDiskP537Rows_actual : ∀ r∈sharedDiskP537Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP537Rows.all (sharedDiskP537Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP537Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP538Params : ChordParams := ⟨⟨(-26520604406269676956269),(-26213562742724451955098),true⟩,⟨1935959225915155005170953,1950907730780836543352200,true⟩,⟨130653287909484245837020,132524824547040414403131,true⟩,⟨240744075085571704562993,243739383376390366746064,true⟩,⟨348392329068560496199595,350513875477733377333346,true⟩,⟨1157023215349237634369434,1157611363486957971834394,true⟩,⟨(-2217526436123592061338635),(-2209662999011553951635464),true⟩,⟨⟨1139825120158780571647699,1168540312963555500108672,true⟩,⟨(-30580496),30580496,true⟩⟩⟩
theorem sharedDiskP538Params_ok : chordParams (Grid.ofRats (41/50) (329/400)) (Grid.ofRats (954575690777197/1649267441664000) (957796916249197/1649267441664000))=sharedDiskP538Params := by decide +kernel
def sharedDiskP538Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3166141875794595163860015),(-2653730609767840782577781),true⟩,⟨(-322709660284175944752645),87033686555104857594716,true⟩⟩
  | 0,1 => ⟨⟨(-2809797539107961123424715),(-2338916129234219140504367),true⟩,⟨(-381053088900107368707186),7777083582065214769487,true⟩⟩
  | 0,2 => ⟨⟨(-2552169029196352438275473),(-2114146761462099667122605),true⟩,⟨(-431057742264786156086427),(-62101929391334566696779),true⟩⟩
  | 0,3 => ⟨⟨(-2406880283399184756265618),(-1988329733058623521617896),true⟩,⟨(-461901761537919638640925),(-105806205845740967253680),true⟩⟩
  | 0,4 => ⟨⟨(-3587751432181453062586864),(-3032615798293563709275180),true⟩,⟨(-271295306448386437349732),152104541331067479206368,true⟩⟩
  | 0,5 => ⟨⟨(-4016514400910114094951740),(-3425256003687598295827322),true⟩,⟨(-239911966199898442931750),187545418644402078516361,true⟩⟩
  | 0,6 => ⟨⟨(-4378507069245291098730483),(-3762607938146161205789715),true⟩,⟨(-231057393134369260215835),189563298749169419294435,true⟩⟩
  | 0,7 => ⟨⟨(-4605551626856624638557439),(-3976576844733727752722998),true⟩,⟨(-238160850772466701296693),177106315775222574644987,true⟩⟩
  | 1,0 => ⟨⟨(-1533837029405819378793657),(-1238232736182790969676858),true⟩,⟨(-677305733782813654809844),(-410033294147357683145921),true⟩⟩
  | 1,1 => ⟨⟨(-1343042017128320615832151),(-1074901263115839229882275),true⟩,⟨(-727031505181834009417758),(-481397628246117092460226),true⟩⟩
  | 1,2 => ⟨⟨(-1204517927524249616284316),(-956035802157753559046231),true⟩,⟨(-762362344069553175004867),(-532449142682891396368352),true⟩⟩
  | 1,3 => ⟨⟨(-1125747962992962958808400),(-888277212252852359101312),true⟩,⟨(-781922844575653630170455),(-560883907375575060102733),true⟩⟩
  | 1,4 => ⟨⟨(-1761382131655990068932654),(-1432883595451655655251224),true⟩,⟨(-617954989129664114892906),(-325411918908733721716962),true⟩⟩
  | 1,5 => ⟨⟨(-1998317040699123269972472),(-1635943241765044962532840),true⟩,⟨(-557799471836123895985723),(-240210765859091171615301),true⟩⟩
  | 1,6 => ⟨⟨(-2205332619618075905249268),(-1814062701375557086373234),true⟩,⟨(-507719050800461530500996),(-169789999148354590938341),true⟩⟩
  | 1,7 => ⟨⟨(-2339254344408913680734929),(-1929775108847472239426037),true⟩,⟨(-476911881652122783614489),(-126765445253551860862348),true⟩⟩
  | 2,0 => ⟨⟨(-254653693870002549268442),(-111967356121226300732796),true⟩,⟨(-944840187349166293268511),(-798348033645938238750951),true⟩⟩
  | 2,1 => ⟨⟨(-69491040221663359090426),61570857867653491660558,true⟩,⟨(-958901443166207798165352),(-821581712123839758904351),true⟩⟩
  | 2,2 => ⟨⟨65610941839809872721184,190139028114452763164897,true⟩,⟨(-963635563210761935731965),(-832087630334782519377989),true⟩⟩
  | 2,3 => ⟨⟨142938256956413727321228,264384510877917911818615,true⟩,⟨(-964402997390283331443516),(-835817140907606416276689),true⟩⟩
  | 2,4 => ⟨⟨(-476121467872994055254845),(-316176125499413461835923),true⟩,⟨(-916322595432358377142202),(-756901494197684239176263),true⟩⟩
  | 2,5 => ⟨⟨(-712347527410907659248098),(-529171552597901656356172),true⟩,⟨(-873648851191960075795604),(-696730531407308310447082),true⟩⟩
  | 2,6 => ⟨⟨(-927019905145063928365843),(-716587544394491320044505),true⟩,⟨(-828679840923122444171487),(-629601546246403963568504),true⟩⟩
  | 2,7 => ⟨⟨(-1070496965746258216347302),(-840659458528838354079495),true⟩,⟨(-795337612860470093923747),(-580475579777748297554761),true⟩⟩
  | 3,0 => ⟨⟨1059894929148688570945395,1187601413158964081767738,true⟩,⟨(-943433299352730946310360),(-817614092827246981793036),true⟩⟩
  | 3,1 => ⟨⟨1281005682978605131376492,1415628750616516334851140,true⟩,⟨(-962578136562728167424711),(-832033686639484544895855),true⟩⟩
  | 3,2 => ⟨⟨1451330499287636023595559,1592787643941249525713376,true⟩,⟨(-996716744430491721240123),(-860798467078553670551764),true⟩⟩
  | 3,3 => ⟨⟨1553013863083485494981541,1699282929618805030200562,true⟩,⟨(-1027699328155886335649662),(-887726826150988900052670),true⟩⟩
  | 3,4 => ⟨⟨809743884751099689940813,931894306244987221143042,true⟩,⟨(-943423450984608049145567),(-820405770318611107137347),true⟩⟩
  | 3,5 => ⟨⟨557959812805803191938608,676730454024666689032053,true⟩,⟨(-953422545050404400568331),(-830896222013090147434764),true⟩⟩
  | 3,6 => ⟨⟨340450228190410811137199,458100189731003005234312,true⟩,⟨(-961327929509451028557806),(-837493593457981956111586),true⟩⟩
  | 3,7 => ⟨⟨197538101743130093085550,317030132381799474078072,true⟩,⟨(-964169627578798458601263),(-837525229018672813270515),true⟩⟩
  | 4,0 => ⟨⟨2293546555795067385823202,2526890240802636578519702,true⟩,⟨(-1711601564783602218753700),(-1484135375388140565497580),true⟩⟩
  | 4,1 => ⟨⟨2466265117446351763132372,2744654962067509858705896,true⟩,⟨(-2158634864447746234631298),(-1882202062964266288469011),true⟩⟩
  | 4,2 => ⟨⟨2548019778969050106464542,2873346108240045498142091,true⟩,⟨(-2657633736696372953173437),(-2328260106180707665992827),true⟩⟩
  | 4,3 => ⟨⟨2549985485486900743275866,2909692596956242150156256,true⟩,⟨(-3037833447134533086746683),(-2668561705752952941557598),true⟩⟩
  | 4,4 => ⟨⟨2077017005270749826110903,2274770238597070802105565,true⟩,⟨(-1392607020365391319870954),(-1202305914425637320905037),true⟩⟩
  | 4,5 => ⟨⟨1868124069726951065148508,2041010257822766718732423,true⟩,⟨(-1197643094118441859095107),(-1032298253657005044610247),true⟩⟩
  | 4,6 => ⟨⟨1702162527686239614184686,1859484041378432034174085,true⟩,⟨(-1093002203726401646678311),(-942730176817284819966542),true⟩⟩
  | 4,7 => ⟨⟨1601958433911600217205265,1751284479139451504380812,true⟩,⟨(-1046307753428067289884550),(-903573053667938140999968),true⟩⟩
  | 5,0 => ⟨⟨2337317875078081103734317,2784230933534978117322413,true⟩,⟨(-4036684348022870294715366),(-3562221403299084313594937),true⟩⟩
  | 5,1 => ⟨⟨2210106092456289646400081,2682890603385384363402716,true⟩,⟨(-4338654313275906087301641),(-3831889591971815178928725),true⟩⟩
  | 5,2 => ⟨⟨2079793131719493488945696,2574001462062849537843608,true⟩,⟨(-4589548542246004848382319),(-4055643904920987642545315),true⟩⟩
  | 5,3 => ⟨⟨1986825627514724169573813,2494299092616835854464918,true⟩,⟨(-4745035944476261292184351),(-4194143766354927870389216),true⟩⟩
  | 5,4 => ⟨⟨2434832956793634607288747,2855601369784914485502269,true⟩,⟨(-3733462055792678969519498),(-3291129671574717831637960),true⟩⟩
  | 5,5 => ⟨⟨2495866668890999586625110,2893821906835655781360880,true⟩,⟨(-3471143240593424443802474),(-3056431822125039010770923),true⟩⟩
  | 5,6 => ⟨⟨2527280873477323903943311,2908235725318349614476420,true⟩,⟨(-3277412264636645399842484),(-2883032711830585226784823),true⟩⟩
  | 5,7 => ⟨⟨2540029662469998098575439,2911181140821295669154264,true⟩,⟨(-3166492647358337669912817),(-2783739586850211709381411),true⟩⟩
  | 6,0 => ⟨⟨849868176733870077704101,1466610575609473683441327,true⟩,⟨(-5922355727967503608033616),(-5231594558412732576614892),true⟩⟩
  | 6,1 => ⟨⟨358102859700165980933035,1019714517345646982231093,true⟩,⟨(-6212748520227966528708146),(-5474436413892852231524705),true⟩⟩
  | 6,2 => ⟨⟨(-90090274690917132418956),610966108678584457397540,true⟩,⟨(-6406753304709169182054811),(-5630127872880759368948779),true⟩⟩
  | 6,3 => ⟨⟨(-385920942814497512232245),340035432160656143547352,true⟩,⟨(-6502706783166961084098555),(-5703826675952534416133538),true⟩⟩
  | 6,4 => ⟨⟨1287111638288280573345163,1866076598069621622072516,true⟩,⟨(-5577836299148401437861473),(-4932753152408883658907784),true⟩⟩
  | 6,5 => ⟨⟨1613587027054522409655527,2163856190564808193541617,true⟩,⟨(-5245519082105195605143695),(-4638810454142944168819992),true⟩⟩
  | 6,6 => ⟨⟨1826636075552680207023336,2354181596724805655008598,true⟩,⟨(-4980161817457536497956242),(-4403288646692934110114360),true⟩⟩
  | 6,7 => ⟨⟨1937490839324772704746609,2451480363410202596996988,true⟩,⟨(-4821403316173486633886592),(-4262113893486070793184024),true⟩⟩
  | 7,0 => ⟨⟨(-3022860575089870942286171),(-2121397021863782242500046),true⟩,⟨(-6385993848400815743288032),(-5480871254110017924410039),true⟩⟩
  | 7,1 => ⟨⟨(-3781114261909804220418051),(-2848327514630977486833414),true⟩,⟨(-5991856317144054796950677),(-5091653771517845234523869),true⟩⟩
  | 7,2 => ⟨⟨(-4330974409707016731403213),(-3384274834794260010788934),true⟩,⟨(-5550436620569801558937349),(-4669842324979044466202548),true⟩⟩
  | 7,3 => ⟨⟨(-4628135797481410134774859),(-3678697374136373886806570),true⟩,⟨(-5231056585684410608892983),(-4369569355016935859615147),true⟩⟩
  | 7,4 => ⟨⟨(-2184476995470840191858782),(-1328977880640832389798497),true⟩,⟨(-6613015144276428037596322),(-5723364274284477308208724),true⟩⟩
  | 7,5 => ⟨⟨(-1424229255236512207423601),(-618766527098934539829068),true⟩,⟨(-6662371416058133057487583),(-5801979837784965976893496),true⟩⟩
  | 7,6 => ⟨⟨(-857605397002662132000413),(-94350503716051770823509),true⟩,⟨(-6608246601191519182341639),(-5778319466766879227573608),true⟩⟩
  | 7,7 => ⟨⟨(-535942618928828724665587),202120996873740587556563,true⟩,⟨(-6542432383369779658600140),(-5733101074188902731831425),true⟩⟩
  | 8,0 => ⟨⟨(-5495955764195880142561510),(-4689429759491684716644958),true⟩,⟨(-2056316974371720848814389),(-1495804443800085063125507),true⟩⟩
  | 8,1 => ⟨⟨(-5250542641589557512018586),(-4529966224395832218305676),true⟩,⟨(-1162220304745688368873793),(-711404030041571226036900),true⟩⟩
  | 8,2 => ⟨⟨(-4929811961251243794754040),(-4287358314242771199359741),true⟩,⟨(-534875881305901990034735),(-170935709567739762634300),true⟩⟩
  | 8,3 => ⟨⟨(-4694654750108957055067443),(-4101928707413330678709710),true⟩,⟨(-201667396163205873283138),119056951567921746502045,true⟩⟩
  | 8,4 => ⟨⟨(-5525396231210975239055362),(-4645109790185647557094727),true⟩,⟨(-3076506881359999557149874),(-2401897312730526383287905),true⟩⟩
  | 8,5 => ⟨⟨(-5319566221231116364091207),(-4393960386981837226269883),true⟩,⟨(-4009589723440459166584294),(-3244082434290777405600819),true⟩⟩
  | 8,6 => ⟨⟨(-5006168766421674676096656),(-4061559295278341815817862),true⟩,⟨(-4690249114478550585312124),(-3867464433758331657713549),true⟩⟩
  | 8,7 => ⟨⟨(-4760682482465981079421401),(-3811609364681909600352042),true⟩,⟨(-5062613466116284298164003),(-4212418974811520742841955),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP538Value0_0 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP538Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value0_1 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP538Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value0_2 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP538Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value0_3 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP538Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value0_4 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP538Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value0_5 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP538Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value0_6 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP538Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value0_7 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP538Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP538Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 0 j)=sharedDiskP538Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP538Value0_0
  · exact sharedDiskP538Value0_1
  · exact sharedDiskP538Value0_2
  · exact sharedDiskP538Value0_3
  · exact sharedDiskP538Value0_4
  · exact sharedDiskP538Value0_5
  · exact sharedDiskP538Value0_6
  · exact sharedDiskP538Value0_7
private theorem sharedDiskP538Value1_0 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP538Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value1_1 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP538Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value1_2 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP538Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value1_3 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP538Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value1_4 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP538Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value1_5 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP538Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value1_6 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP538Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value1_7 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP538Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP538Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 1 j)=sharedDiskP538Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP538Value1_0
  · exact sharedDiskP538Value1_1
  · exact sharedDiskP538Value1_2
  · exact sharedDiskP538Value1_3
  · exact sharedDiskP538Value1_4
  · exact sharedDiskP538Value1_5
  · exact sharedDiskP538Value1_6
  · exact sharedDiskP538Value1_7
private theorem sharedDiskP538Value2_0 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP538Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value2_1 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP538Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value2_2 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP538Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value2_3 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP538Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value2_4 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP538Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value2_5 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP538Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value2_6 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP538Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value2_7 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP538Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP538Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 2 j)=sharedDiskP538Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP538Value2_0
  · exact sharedDiskP538Value2_1
  · exact sharedDiskP538Value2_2
  · exact sharedDiskP538Value2_3
  · exact sharedDiskP538Value2_4
  · exact sharedDiskP538Value2_5
  · exact sharedDiskP538Value2_6
  · exact sharedDiskP538Value2_7
private theorem sharedDiskP538Value3_0 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP538Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value3_1 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP538Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value3_2 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP538Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value3_3 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP538Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value3_4 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP538Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value3_5 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP538Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value3_6 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP538Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value3_7 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP538Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP538Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 3 j)=sharedDiskP538Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP538Value3_0
  · exact sharedDiskP538Value3_1
  · exact sharedDiskP538Value3_2
  · exact sharedDiskP538Value3_3
  · exact sharedDiskP538Value3_4
  · exact sharedDiskP538Value3_5
  · exact sharedDiskP538Value3_6
  · exact sharedDiskP538Value3_7
private theorem sharedDiskP538Value4_0 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP538Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value4_1 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP538Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value4_2 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP538Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value4_3 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP538Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value4_4 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP538Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value4_5 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP538Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value4_6 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP538Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value4_7 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP538Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP538Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 4 j)=sharedDiskP538Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP538Value4_0
  · exact sharedDiskP538Value4_1
  · exact sharedDiskP538Value4_2
  · exact sharedDiskP538Value4_3
  · exact sharedDiskP538Value4_4
  · exact sharedDiskP538Value4_5
  · exact sharedDiskP538Value4_6
  · exact sharedDiskP538Value4_7
private theorem sharedDiskP538Value5_0 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP538Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value5_1 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP538Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value5_2 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP538Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value5_3 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP538Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value5_4 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP538Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value5_5 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP538Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value5_6 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP538Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value5_7 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP538Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP538Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 5 j)=sharedDiskP538Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP538Value5_0
  · exact sharedDiskP538Value5_1
  · exact sharedDiskP538Value5_2
  · exact sharedDiskP538Value5_3
  · exact sharedDiskP538Value5_4
  · exact sharedDiskP538Value5_5
  · exact sharedDiskP538Value5_6
  · exact sharedDiskP538Value5_7
private theorem sharedDiskP538Value6_0 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP538Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value6_1 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP538Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value6_2 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP538Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value6_3 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP538Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value6_4 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP538Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value6_5 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP538Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value6_6 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP538Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value6_7 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP538Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP538Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 6 j)=sharedDiskP538Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP538Value6_0
  · exact sharedDiskP538Value6_1
  · exact sharedDiskP538Value6_2
  · exact sharedDiskP538Value6_3
  · exact sharedDiskP538Value6_4
  · exact sharedDiskP538Value6_5
  · exact sharedDiskP538Value6_6
  · exact sharedDiskP538Value6_7
private theorem sharedDiskP538Value7_0 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP538Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value7_1 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP538Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value7_2 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP538Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value7_3 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP538Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value7_4 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP538Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value7_5 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP538Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value7_6 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP538Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value7_7 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP538Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP538Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 7 j)=sharedDiskP538Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP538Value7_0
  · exact sharedDiskP538Value7_1
  · exact sharedDiskP538Value7_2
  · exact sharedDiskP538Value7_3
  · exact sharedDiskP538Value7_4
  · exact sharedDiskP538Value7_5
  · exact sharedDiskP538Value7_6
  · exact sharedDiskP538Value7_7
private theorem sharedDiskP538Value8_0 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP538Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value8_1 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP538Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value8_2 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP538Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value8_3 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP538Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value8_4 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP538Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value8_5 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP538Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value8_6 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP538Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP538Value8_7 : truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP538Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP538Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points 8 j)=sharedDiskP538Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP538Value8_0
  · exact sharedDiskP538Value8_1
  · exact sharedDiskP538Value8_2
  · exact sharedDiskP538Value8_3
  · exact sharedDiskP538Value8_4
  · exact sharedDiskP538Value8_5
  · exact sharedDiskP538Value8_6
  · exact sharedDiskP538Value8_7
theorem sharedDiskP538Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP538Params (sharedChord521Gauss8Points i j)=sharedDiskP538Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP538Values0_eq
  · exact sharedDiskP538Values1_eq
  · exact sharedDiskP538Values2_eq
  · exact sharedDiskP538Values3_eq
  · exact sharedDiskP538Values4_eq
  · exact sharedDiskP538Values5_eq
  · exact sharedDiskP538Values6_eq
  · exact sharedDiskP538Values7_eq
  · exact sharedDiskP538Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP538Box : HorizontalRectangle := ⟨(41/50),(329/400),(954575690777197/1649267441664000),(957796916249197/1649267441664000),(122887102076508159357301256841873/1298074214633706907132624082305024),(1092701572853376123677556598074001/1298074214633706907132624082305024),(-1111924229503962012578590210312427/324518553658426726783156020576256),(-862656254202157052963628786567403/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP538Grid : CGrid := momentChordGrid sharedDiskP538Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP538Columns : containedInReported sharedDiskP538Grid.re sharedDiskP538Box.reLo sharedDiskP538Box.reHi=true ∧ containedInReported sharedDiskP538Grid.im sharedDiskP538Box.imLo sharedDiskP538Box.imHi=true := by
  rw [sharedDiskP538Grid,momentChordGrid_eq_tabulated sharedDiskP538Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP538Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP538Values_eq]
  decide +kernel
theorem sharedDiskP538Sound : sharedDiskP538Box.Sound := by
  intro t a tl tu al au
  change (((41/50):ℚ):ℝ)≤t at tl
  change t≤(((329/400):ℚ):ℝ) at tu
  change (((954575690777197/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((957796916249197/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP538Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(41/50))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((329/400):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(954575690777197/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((957796916249197/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP538Columns.1 sharedDiskP538Columns.2
def sharedDiskP538Rows : List SignRow := [positive_538.toSignRow]
theorem sharedDiskP538Rows_actual : ∀ r∈sharedDiskP538Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP538Rows.all (sharedDiskP538Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP538Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP535Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP536Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP537Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP538Rows_actual
