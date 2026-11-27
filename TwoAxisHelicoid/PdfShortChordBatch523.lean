import TwoAxisHelicoid.PdfSharedChord521Gauss8
import TwoAxisHelicoid.PdfSharedChord521Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP523Params : ChordParams := ⟨⟨(-22097370815995689515361),(-21537693856656346368962),true⟩,⟨2077209648620946683115592,2109545289766134735682277,true⟩,⟨121394604228460488833710,125125734608942486330351,true⟩,⟨211138122205625228342508,216861725850158445386360,true⟩,⟨316929627857577113690857,321167090149701553700086,true⟩,⟨1165524391708610427754520,1166604411603411691783160,true⟩,⟨(-2349356313550462509341824),(-2332231125204766268893454),true⟩,⟨⟨1136138487265674358783954,1192373648425024739739172,true⟩,⟨(-4405746),4405746,true⟩⟩⟩
theorem sharedDiskP523Params_ok : chordParams (Grid.ofRats (39/50) (157/200)) (Grid.ofRats (311576652697259/549755813888000) (313724136345259/549755813888000))=sharedDiskP523Params := by decide +kernel
def sharedDiskP523Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3463600989581137493435188),(-2458236717570172129699713),true⟩,⟨(-565553736025695347018044),243519029115493944048900,true⟩⟩
  | 0,1 => ⟨⟨(-3036078567436420604255877),(-2122857604722913488925123),true⟩,⟨(-630087910267411171889908),129300349635807994200519,true⟩⟩
  | 0,2 => ⟨⟨(-2729221894371857899535255),(-1887781839968569612054292),true⟩,⟨(-681574286416361511207090),31436537782778104445405,true⟩⟩
  | 0,3 => ⟨⟨(-2557102089232129109107385),(-1757716032908904313063993),true⟩,⟨(-712001103550648498604200),(-28238187503340783775266),true⟩⟩
  | 0,4 => ⟨⟨(-3973346143310466439305975),(-2871267756539321385233225),true⟩,⟨(-501781291665105006565673),346434863061482526585723,true⟩⟩
  | 0,5 => ⟨⟨(-4494834938593158727429909),(-3309574124077155852540386),true⟩,⟨(-453806429790224943117679),409183114515609407954742,true⟩⟩
  | 0,6 => ⟨⟨(-4936400530546987960819856),(-3693366889519205698403870),true⟩,⟨(-435999542194833406661314),418260259731488674924192,true⟩⟩
  | 0,7 => ⟨⟨(-5214016564312224761758968),(-3940200015156519610064360),true⟩,⟨(-438875523518509608591528),402604056323485887086362,true⟩⟩
  | 1,0 => ⟨⟨(-1543171246934516645467830),(-1000075577338360374118425),true⟩,⟨(-902165735436649839543631),(-407868178940032095249175),true⟩⟩
  | 1,1 => ⟨⟨(-1325903092314217018767444),(-837458752709092978131526),true⟩,⟨(-940456769005602788131450),(-488988944064276815700019),true⟩⟩
  | 1,2 => ⟨⟨(-1168917461451733248987156),(-719170668021876109850183),true⟩,⟨(-966012825445381399845723),(-545238223556514744646116),true⟩⟩
  | 1,3 => ⟨⟨(-1079916109006746209534426),(-651700494495940486524476),true⟩,⟨(-979450574549546473006636),(-575863602930146636890453),true⟩⟩
  | 1,4 => ⟨⟨(-1803981568701076537653280),(-1194476920691825078790076),true⟩,⟨(-853502427532941054744993),(-308221567895751294080723),true⟩⟩
  | 1,5 => ⟨⟨(-2077604759579864643533959),(-1398600743511150700364489),true⟩,⟨(-801262847668398015465232),(-204316589798604294410947),true⟩⟩
  | 1,6 => ⟨⟨(-2318556176114750232262875),(-1579234988400233973207636),true⟩,⟨(-755597976092696465508449),(-115529746478608794186634),true⟩⟩
  | 1,7 => ⟨⟨(-2476954526093842268740556),(-1697536600148733748584436),true⟩,⟨(-726485360128341662306060),(-56981492658926852945542),true⟩⟩
  | 2,0 => ⟨⟨(-117350144778833179071788),144323720138221943381812,true⟩,⟨(-1062812500545298605151156),(-786972047667902740192557),true⟩⟩
  | 2,1 => ⟨⟨82835149385084554823128,325282304719890914240041,true⟩,⟨(-1054911313644072794158296),(-796133661231963366386448),true⟩⟩
  | 2,2 => ⟨⟨227636880041549453020604,463154241365432863119123,true⟩,⟨(-1043189868540788722664432),(-792699272553509672651143),true⟩⟩
  | 2,3 => ⟨⟨309625281233173471248193,542803974945834528951519,true⟩,⟨(-1034912372094258022480200),(-788058221065386543801671),true⟩⟩
  | 2,4 => ⟨⟨(-359054149046928004213657),(-67513249750914516040152),true⟩,⟨(-1058993344706166845688002),(-759418786414027415703911),true⟩⟩
  | 2,5 => ⟨⟨(-617152328493506273829329),(-285877027318442844948157),true⟩,⟨(-1039593949484401409138810),(-710871133753271788213940),true⟩⟩
  | 2,6 => ⟨⟨(-856166917851178032104072),(-478517309831286889183454),true⟩,⟨(-1011097797342634353473941),(-647213744338897561071504),true⟩⟩
  | 2,7 => ⟨⟨(-1017598055422865363779615),(-604250998738463311140323),true⟩,⟨(-988324537030195735762725),(-596648246431405437114742),true⟩⟩
  | 3,0 => ⟨⟨1244854823570958201632929,1499415024911567638716658,true⟩,⟨(-920352137860766507160937),(-676442539317097637708599),true⟩⟩
  | 3,1 => ⟨⟨1461865187746690216236163,1728571543962178307264242,true⟩,⟨(-919882785075812205841425),(-668638998453371041774968),true⟩⟩
  | 3,2 => ⟨⟨1627106392830968913995490,1905598776191676756632191,true⟩,⟨(-939345718798861902836229),(-679454285376251465732522),true⟩⟩
  | 3,3 => ⟨⟨1725241196780154588138352,2012003051059761425139584,true⟩,⟨(-961556782456760847862830),(-695009160485441262992865),true⟩⟩
  | 3,4 => ⟨⟨995027603873561427590797,1239337895980909100865949,true⟩,⟨(-944057296376632868237822),(-704143711878466559441111),true⟩⟩
  | 3,5 => ⟨⟨738714148399713357319648,975997930174086335471915,true⟩,⟨(-979915388460472316072664),(-740190381057082648970219),true⟩⟩
  | 3,6 => ⟨⟨513738919388924274418983,747628067733738585191305,true⟩,⟨(-1011554712143612944534500),(-769205818923309501148291),true⟩⟩
  | 3,7 => ⟨⟨366030954019908097537542,599168384054424151701094,true⟩,⟨(-1029195448193331976037937),(-783787462205985045515167),true⟩⟩
  | 4,0 => ⟨⟨2443356566432103667446651,2892857097360829789548802,true⟩,⟨(-1582371477201201364591657),(-1156194590423366574319958),true⟩⟩
  | 4,1 => ⟨⟨2632029267938316847619210,3166968271021824911155130,true⟩,⟨(-2011948662329068095327334),(-1494570539400792493674901),true⟩⟩
  | 4,2 => ⟨⟨2745927039983804706016917,3371489919198075523081564,true⟩,⟨(-2505423494358492829853722),(-1887531449564445709408913),true⟩⟩
  | 4,3 => ⟨⟨2779618344115837639699514,3472835004899113833155740,true⟩,⟨(-2891592821220256960645913),(-2196438764634983898379714),true⟩⟩
  | 4,4 => ⟨⟨2226737944827671869466323,2609500651373456059733619,true⟩,⟨(-1283995867768970482807597),(-926098223399535293981596),true⟩⟩
  | 4,5 => ⟨⟨2025312585190514038519985,2361650523089881175524569,true⟩,⟨(-1106850024956306602597204),(-794443116196695280455688),true⟩⟩
  | 4,6 => ⟨⟨1867296055513432289698314,2174557332109330959184376,true⟩,⟨(-1015269421888706634557427),(-730234787557048652435776),true⟩⟩
  | 4,7 => ⟨⟨1772062870264994293469106,2064354587872549676760356,true⟩,⟨(-976180975504835196165478),(-704806012501760043152213),true⟩⟩
  | 5,0 => ⟨⟨2669692192760371306689935,3540562833034258388406356,true⟩,⟨(-3953938098509292254699309),(-3047662629546910911746167),true⟩⟩
  | 5,1 => ⟨⟨2576864033582428651733867,3502468229954215271907632,true⟩,⟨(-4291104431310817615933504),(-3317467489278347157360045),true⟩⟩
  | 5,2 => ⟨⟨2475540858340489931908330,3447319980313033418051481,true⟩,⟨(-4578031445666527154864717),(-3546718345856140735521558),true⟩⟩
  | 5,3 => ⟨⟨2400542892459179884258920,3401339583229818600046688,true⟩,⟨(-4759287875721214162913720),(-3691327256135564632718360),true⟩⟩
  | 5,4 => ⟨⟨2733813381592453093520334,3550394069028543640065398,true⟩,⟨(-3623405879918595260640451),(-2782875084762911476556604),true⟩⟩
  | 5,5 => ⟨⟨2767300573429599275515155,3537264627796915367201147,true⟩,⟨(-3343346567278957003136849),(-2558413247296030542345116),true⟩⟩
  | 5,6 => ⟨⟨2779386052554616060690962,3515030781009251700259713,true⟩,⟨(-3139763441689079011663951),(-2395250044849298439856798),true⟩⟩
  | 5,7 => ⟨⟨2781519184863594426432223,3497526177872701844960544,true⟩,⟨(-3024384449410030316910622),(-2302801725125630199756573),true⟩⟩
  | 6,0 => ⟨⟨1389377956153545631208200,2626695734440175105366194,true⟩,⟨(-6247700283791522988002601),(-4868473792517169956264068),true⟩⟩
  | 6,1 => ⟨⟨907875612128604388877982,2226015908576252975993417,true⟩,⟨(-6672684919425568729538425),(-5192357182827123530961194),true⟩⟩
  | 6,2 => ⟨⟨444951205927769509939115,1835719374390030432318598,true⟩,⟨(-6992209692079552238091708),(-5427338436528375565988444),true⟩⟩
  | 6,3 => ⟨⟨132377540571267588312361,1566984024972997927356644,true⟩,⟨(-7169233702629244500371023),(-5554379763812521295643067),true⟩⟩
  | 6,4 => ⟨⟨1790855301843900662488372,2955060039543106697141533,true⟩,⟨(-5787680755380926970702802),(-4507238795492355941105201),true⟩⟩
  | 6,5 => ⟨⟨2083534818468377565323702,3180535536272385873982008,true⟩,⟨(-5363838423376839160740148),(-4172084747437101517892830),true⟩⟩
  | 6,6 => ⟨⟨2267232885023526034591682,3312624507209835586318434,true⟩,⟨(-5038966829832284194936507),(-3914068148576099786290806),true⟩⟩
  | 6,7 => ⟨⟨2359993113787677558630499,3375172563157947399275184,true⟩,⟨(-4849356271762108205225194),(-3763114394697383951837858),true⟩⟩
  | 7,0 => ⟨⟨(-2930779822961953492732629),(-1053844127524201799380993),true⟩,⟨(-7659404125561054048865100),(-5709262577424891591232785),true⟩⟩
  | 7,1 => ⟨⟨(-3899080640369326113661853),(-1922177166534390587967575),true⟩,⟨(-7366138392858743828199954),(-5391797791755970332671304),true⟩⟩
  | 7,2 => ⟨⟨(-4629593713717589423112786),(-2596401281163851603659848),true⟩,⟨(-6955489406604060765420351),(-4999280078727218052931808),true⟩⟩
  | 7,3 => ⟨⟨(-5036088899086824571031433),(-2981813532296116067156517),true⟩,⟨(-6629465232287313595630177),(-4702508632671856598008536),true⟩⟩
  | 7,4 => ⟨⟨(-1906985752854942889711052),(-159817920469001082271219),true⟩,⟨(-7725161773293739411572676),(-5846218934467079206214699),true⟩⟩
  | 7,5 => ⟨⟨(-1018679296559238455456890),602043993703332566337298,true⟩,⟨(-7598614866823225257420112),(-5814842579972038409256613),true⟩⟩
  | 7,6 => ⟨⟨(-381117340850749800003493),1138582817465784252522547,true⟩,⟨(-7400610383404100285135926),(-5704314239288074384756977),true⟩⟩
  | 7,7 => ⟨⟨(-28645860189676735086578),1430704857685992581658050,true⟩,⟨(-7249483751394372389945576),(-5608946010401450001171016),true⟩⟩
  | 8,0 => ⟨⟨(-6376402967539926647881562),(-4578538518943176686575266),true⟩,⟨(-2823253885823824465387917),(-1545214502203223695824257),true⟩⟩
  | 8,1 => ⟨⟨(-6078992221655540774423395),(-4480339255640654697131498),true⟩,⟨(-1664277668198795275948240),(-645514442539329213049097),true⟩⟩
  | 8,2 => ⟨⟨(-5659934231426364461756696),(-4250048875559362102823264),true⟩,⟨(-847005598789715225125427),(-34531627275682254860258),true⟩⟩
  | 8,3 => ⟨⟨(-5348408018425923575335440),(-4059805682253699483446737),true⟩,⟨(-414910880012866537711152),305828555620259407613223,true⟩⟩
  | 8,4 => ⟨⟨(-6361208715923767319315929),(-4406815830172022440658287),true⟩,⟨(-4117025836829426348556268),(-2580261136929482539344244),true⟩⟩
  | 8,5 => ⟨⟨(-6029220637368478924501035),(-3988538856037917533441804),true⟩,⟨(-5253860441464660726969938),(-3515109140980898523799883),true⟩⟩
  | 8,6 => ⟨⟨(-5568349804957015015030885),(-3504216278982082170553126),true⟩,⟨(-6040929885583269226289293),(-4184624612810702909415051),true⟩⟩
  | 8,7 => ⟨⟨(-5220539885186260679345588),(-3160065273309044431289910),true⟩,⟨(-6450466969358387443024677),(-4542972544076210268593255),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP523Value0_0 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP523Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value0_1 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP523Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value0_2 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP523Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value0_3 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP523Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value0_4 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP523Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value0_5 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP523Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value0_6 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP523Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value0_7 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP523Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP523Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 0 j)=sharedDiskP523Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP523Value0_0
  · exact sharedDiskP523Value0_1
  · exact sharedDiskP523Value0_2
  · exact sharedDiskP523Value0_3
  · exact sharedDiskP523Value0_4
  · exact sharedDiskP523Value0_5
  · exact sharedDiskP523Value0_6
  · exact sharedDiskP523Value0_7
private theorem sharedDiskP523Value1_0 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP523Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value1_1 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP523Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value1_2 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP523Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value1_3 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP523Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value1_4 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP523Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value1_5 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP523Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value1_6 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP523Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value1_7 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP523Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP523Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 1 j)=sharedDiskP523Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP523Value1_0
  · exact sharedDiskP523Value1_1
  · exact sharedDiskP523Value1_2
  · exact sharedDiskP523Value1_3
  · exact sharedDiskP523Value1_4
  · exact sharedDiskP523Value1_5
  · exact sharedDiskP523Value1_6
  · exact sharedDiskP523Value1_7
private theorem sharedDiskP523Value2_0 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP523Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value2_1 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP523Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value2_2 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP523Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value2_3 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP523Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value2_4 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP523Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value2_5 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP523Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value2_6 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP523Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value2_7 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP523Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP523Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 2 j)=sharedDiskP523Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP523Value2_0
  · exact sharedDiskP523Value2_1
  · exact sharedDiskP523Value2_2
  · exact sharedDiskP523Value2_3
  · exact sharedDiskP523Value2_4
  · exact sharedDiskP523Value2_5
  · exact sharedDiskP523Value2_6
  · exact sharedDiskP523Value2_7
private theorem sharedDiskP523Value3_0 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP523Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value3_1 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP523Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value3_2 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP523Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value3_3 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP523Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value3_4 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP523Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value3_5 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP523Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value3_6 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP523Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value3_7 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP523Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP523Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 3 j)=sharedDiskP523Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP523Value3_0
  · exact sharedDiskP523Value3_1
  · exact sharedDiskP523Value3_2
  · exact sharedDiskP523Value3_3
  · exact sharedDiskP523Value3_4
  · exact sharedDiskP523Value3_5
  · exact sharedDiskP523Value3_6
  · exact sharedDiskP523Value3_7
private theorem sharedDiskP523Value4_0 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP523Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value4_1 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP523Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value4_2 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP523Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value4_3 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP523Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value4_4 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP523Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value4_5 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP523Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value4_6 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP523Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value4_7 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP523Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP523Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 4 j)=sharedDiskP523Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP523Value4_0
  · exact sharedDiskP523Value4_1
  · exact sharedDiskP523Value4_2
  · exact sharedDiskP523Value4_3
  · exact sharedDiskP523Value4_4
  · exact sharedDiskP523Value4_5
  · exact sharedDiskP523Value4_6
  · exact sharedDiskP523Value4_7
private theorem sharedDiskP523Value5_0 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP523Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value5_1 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP523Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value5_2 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP523Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value5_3 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP523Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value5_4 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP523Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value5_5 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP523Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value5_6 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP523Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value5_7 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP523Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP523Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 5 j)=sharedDiskP523Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP523Value5_0
  · exact sharedDiskP523Value5_1
  · exact sharedDiskP523Value5_2
  · exact sharedDiskP523Value5_3
  · exact sharedDiskP523Value5_4
  · exact sharedDiskP523Value5_5
  · exact sharedDiskP523Value5_6
  · exact sharedDiskP523Value5_7
private theorem sharedDiskP523Value6_0 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP523Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value6_1 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP523Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value6_2 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP523Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value6_3 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP523Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value6_4 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP523Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value6_5 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP523Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value6_6 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP523Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value6_7 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP523Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP523Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 6 j)=sharedDiskP523Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP523Value6_0
  · exact sharedDiskP523Value6_1
  · exact sharedDiskP523Value6_2
  · exact sharedDiskP523Value6_3
  · exact sharedDiskP523Value6_4
  · exact sharedDiskP523Value6_5
  · exact sharedDiskP523Value6_6
  · exact sharedDiskP523Value6_7
private theorem sharedDiskP523Value7_0 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP523Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value7_1 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP523Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value7_2 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP523Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value7_3 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP523Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value7_4 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP523Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value7_5 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP523Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value7_6 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP523Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value7_7 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP523Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP523Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 7 j)=sharedDiskP523Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP523Value7_0
  · exact sharedDiskP523Value7_1
  · exact sharedDiskP523Value7_2
  · exact sharedDiskP523Value7_3
  · exact sharedDiskP523Value7_4
  · exact sharedDiskP523Value7_5
  · exact sharedDiskP523Value7_6
  · exact sharedDiskP523Value7_7
private theorem sharedDiskP523Value8_0 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP523Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value8_1 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP523Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value8_2 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP523Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value8_3 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP523Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value8_4 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP523Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value8_5 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP523Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value8_6 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP523Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP523Value8_7 : truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP523Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP523Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points 8 j)=sharedDiskP523Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP523Value8_0
  · exact sharedDiskP523Value8_1
  · exact sharedDiskP523Value8_2
  · exact sharedDiskP523Value8_3
  · exact sharedDiskP523Value8_4
  · exact sharedDiskP523Value8_5
  · exact sharedDiskP523Value8_6
  · exact sharedDiskP523Value8_7
theorem sharedDiskP523Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP523Params (sharedChord521Gauss8Points i j)=sharedDiskP523Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP523Values0_eq
  · exact sharedDiskP523Values1_eq
  · exact sharedDiskP523Values2_eq
  · exact sharedDiskP523Values3_eq
  · exact sharedDiskP523Values4_eq
  · exact sharedDiskP523Values5_eq
  · exact sharedDiskP523Values6_eq
  · exact sharedDiskP523Values7_eq
  · exact sharedDiskP523Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP523Box : HorizontalRectangle := ⟨(39/50),(157/200),(311576652697259/549755813888000),(313724136345259/549755813888000),(149507095926594128664479731260251/5192296858534827628530496329220096),(2292162490299962213787104624240343/1298074214633706907132624082305024),(-5075733938838634399285360090741353/1298074214633706907132624082305024),(-2769269344472076339527262668913257/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP523Grid : CGrid := momentChordGrid sharedDiskP523Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP523Columns : containedInReported sharedDiskP523Grid.re sharedDiskP523Box.reLo sharedDiskP523Box.reHi=true ∧ containedInReported sharedDiskP523Grid.im sharedDiskP523Box.imLo sharedDiskP523Box.imHi=true := by
  rw [sharedDiskP523Grid,momentChordGrid_eq_tabulated sharedDiskP523Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP523Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP523Values_eq]
  decide +kernel
theorem sharedDiskP523Sound : sharedDiskP523Box.Sound := by
  intro t a tl tu al au
  change (((39/50):ℚ):ℝ)≤t at tl
  change t≤(((157/200):ℚ):ℝ) at tu
  change (((311576652697259/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((313724136345259/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP523Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(39/50))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((157/200):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(311576652697259/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((313724136345259/549755813888000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP523Columns.1 sharedDiskP523Columns.2
def sharedDiskP523Rows : List SignRow := [positive_523.toSignRow]
theorem sharedDiskP523Rows_actual : ∀ r∈sharedDiskP523Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP523Rows.all (sharedDiskP523Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP523Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP524Params : ChordParams := ⟨⟨(-22379905656825861486005),(-22097370815995689514886),true⟩,⟨2070345596467991685853661,2086388577253012008159967,true⟩,⟨123157294146707374846868,125023894432129142671427,true⟩,⟨215221409650986888016459,218096527882230195126668,true⟩,⟨320947412203275573741925,323066827278700928140234,true⟩,⟨1164979551464025777527072,1165524391708610427755438,true⟩,⟨(-2332231125204766268902722),(-2323740444737597358018605),true⟩,⟨⟨1148999441969017335886945,1177179986338261201651911,true⟩,⟨(-4974297),4974297,true⟩⟩⟩
theorem sharedDiskP524Params_ok : chordParams (Grid.ofRats (157/200) (63/80)) (Grid.ofRats (938043425991851/1649267441664000) (941264651463851/1649267441664000))=sharedDiskP524Params := by decide +kernel
def sharedDiskP524Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3192562825128391347604212),(-2675234352532873834283720),true⟩,⟨(-362700334663939462448802),52819706697952005084329,true⟩⟩
  | 0,1 => ⟨⟨(-2795091718345710102959695),(-2324699601048726706189972),true⟩,⟨(-435359684971373085625010),(-45156387535907026801773),true⟩⟩
  | 0,2 => ⟨⟨(-2511455551864394012657806),(-2077362365092617168516096),true⟩,⟨(-495313914930397777961703),(-127865792446531375680042),true⟩⟩
  | 0,3 => ⟨⟨(-2353307426504704412499788),(-1939962044574500197930330),true⟩,⟨(-531388299615621429428430),(-177403618071067070220350),true⟩⟩
  | 0,4 => ⟨⟨(-3669652246586071938348160),(-3103280106657009358975885),true⟩,⟨(-295114501927693923089901),138191937065594937864638,true⟩⟩
  | 0,5 => ⟨⟨(-4161730515005517712637369),(-3553319939537684880654514),true⟩,⟨(-249944377766559730574589),189289648835391000213184,true⟩⟩
  | 0,6 => ⟨⟨(-4581810942897202498533367),(-3944448598695611021692960),true⟩,⟨(-232358326504438940921338),199670770725391710746312,true⟩⟩
  | 0,7 => ⟨⟨(-4847157523377721237716656),(-4194281715981076706079979),true⟩,⟨(-236202526278246812639325),189294540818090795329125,true⟩⟩
  | 1,0 => ⟨⟨(-1416609848317906721311683),(-1134105680740101810566991),true⟩,⟨(-765659075163043862180601),(-507956231269196311976210),true⟩⟩
  | 1,1 => ⟨⟨(-1215029163736843612036500),(-960773385878129920934035),true⟩,⟨(-814980441648531440159379),(-579621858942872212881473),true⟩⟩
  | 1,2 => ⟨⟨(-1069110041114611805209525),(-834858545421783690291452),true⟩,⟨(-848637722644071835244652),(-629284773280776088056901),true⟩⟩
  | 1,3 => ⟨⟨(-986256367442831151922196),(-763134510753420460621719),true⟩,⟨(-866689918485106548164861),(-656296071703479938158994),true⟩⟩
  | 1,4 => ⟨⟨(-1658225100005683229464448),(-1341409363280751670935662),true⟩,⟨(-704249397842368876331604),(-419938592176092904913224),true⟩⟩
  | 1,5 => ⟨⟨(-1911552502352131024354314),(-1558854904127578865229026),true⟩,⟨(-639503823609640530009040),(-328217498649809610679831),true⟩⟩
  | 1,6 => ⟨⟨(-2134576812907974800021559),(-1750838392034938151144656),true⟩,⟨(-583791455361758882229273),(-250109481232697826062616),true⟩⟩
  | 1,7 => ⟨⟨(-2279765294869316287512459),(-1876265270265269198532001),true⟩,⟨(-548709029722290475476518),(-201344791330429625236882),true⟩⟩
  | 2,0 => ⟨⟨(-74263900719856680480825),61331578856420173272827,true⟩,⟨(-987129572231904685027998),(-844501307401988253064907),true⟩⟩
  | 2,1 => ⟨⟨119659567465268073236772,245271198896158737433335,true⟩,⟨(-985652094740861632220474),(-851998621230796684781585),true⟩⟩
  | 2,2 => ⟨⟨261009904212900090718747,381775480974124154806845,true⟩,⟨(-978267288923118675665306),(-849724869653192625489290),true⟩⟩
  | 2,3 => ⟨⟨341271270198137115921485,461070366427364813025042,true⟩,⟨(-972336132186025653953075),(-845501246862462315493959),true⟩⟩
  | 2,4 => ⟨⟨(-306771095091085097300320),(-155199325065578453107559),true⟩,⟨(-974943000120799345536291),(-819794894917842948339433),true⟩⟩
  | 2,5 => ⟨⟨(-553284081723631130173342),(-380910343359088254414713),true⟩,⟨(-945945582531088399855667),(-775380639627733214216096),true⟩⟩
  | 2,6 => ⟨⟨(-777478091439401241191248),(-581473062586703727018809),true⟩,⟨(-907751544969504433119350),(-719325735109334954175166),true⟩⟩
  | 2,7 => ⟨⟨(-928181160676301569810384),(-712744209759662538790579),true⟩,⟨(-878796583896802193183868),(-674609169151207985866086),true⟩⟩
  | 3,0 => ⟨⟨1280414274479506827339150,1410013631673052145149380,true⟩,⟨(-868213581110630539314463),(-743585498372287144080226),true⟩⟩
  | 3,1 => ⟨⟨1500898025892008942015215,1636573502137036251649603,true⟩,⟨(-867978820774566935955155),(-739671738412436456960199),true⟩⟩
  | 3,2 => ⟨⟨1669558160659984724735295,1811186760601089451496393,true⟩,⟨(-886882483965729579000794),(-754189969038890614216437),true⟩⟩
  | 3,3 => ⟨⟨1770066056775904840504453,1915886767964842467308933,true⟩,⟨(-908415331424520868158986),(-772338018383445240809756),true⟩⟩
  | 3,4 => ⟨⟨1027893299526114721024464,1152462766989553501777747,true⟩,⟨(-890478695021976097681618),(-767776187117109737880771),true⟩⟩
  | 3,5 => ⟨⟨770123284050900715027615,891382173032129830525607,true⟩,⟨(-923753134268045846859785),(-800980486791184274067387),true⟩⟩
  | 3,6 => ⟨⟨544869712890470220254689,664699866794632807478481,true⟩,⟨(-952327582035860671538967),(-828019930149268901441008),true⟩⟩
  | 3,7 => ⟨⟨397462784719021154841232,517143500784274430991259,true⟩,⟨(-967595213170820296893475),(-841566777117602192295400),true⟩⟩
  | 4,0 => ⟨⟨2527039964759239368317926,2755224137137051155978924,true⟩,⟨(-1498891019905876395479148),(-1281829472993805515632342),true⟩⟩
  | 4,1 => ⟨⟨2733001613918553049499256,3004512307045133163994185,true⟩,⟨(-1909546708694927361486617),(-1646166203168612303400103),true⟩⟩
  | 4,2 => ⟨⟨2863520768880005991307174,3180955711372098188222837,true⟩,⟨(-2380941924601582504471900),(-2066564654206618396803075),true⟩⟩
  | 4,3 => ⟨⟨2908698398363352471124342,3260376005757763864177341,true⟩,⟨(-2749189512868700518972683),(-2395668071767076683723918),true⟩⟩
  | 4,4 => ⟨⟨2295557327925850316339043,2489910665276897231904746,true⟩,⟨(-1214037697690741944818934),(-1031655243212540698712692),true⟩⟩
  | 4,5 => ⟨⟨2082959936822813996845788,2253813898457091850516581,true⟩,⟨(-1045563619060382891425332),(-886262746167315345445026),true⟩⟩
  | 4,6 => ⟨⟨1917571467094492543263956,2073738903321882887882473,true⟩,⟨(-959003773015463019688736),(-813567121629548297512646),true⟩⟩
  | 4,7 => ⟨⟨1818434725079887173436392,1967052917996097278503098,true⟩,⟨(-922325293440164480666615),(-783798718778306740761964),true⟩⟩
  | 5,0 => ⟨⟨2826252478326961782923254,3267606995480385957647407,true⟩,⟨(-3757964560263808863429861),(-3297795331132622262974591),true⟩⟩
  | 5,1 => ⟨⟨2741367242137052538657553,3210263413138031170685918,true⟩,⟨(-4076524078585901979501799),(-3582439714035234768433789),true⟩⟩
  | 5,2 => ⟨⟨2646643248023387300745887,3138736851772547885495754,true⟩,⟨(-4346899780648499343706435),(-3823825313137325097510417),true⟩⟩
  | 5,3 => ⟨⟨2575766222377119286149674,3082418720676692378979304,true⟩,⟨(-4517332136466927091127935),(-3975862022270869048564855),true⟩⟩
  | 5,4 => ⟨⟨2882300844170079849204623,3296293368809137722632022,true⟩,⟨(-3444867500500613428620290),(-3017854633339893828308648),true⟩⟩
  | 5,5 => ⟨⟨2908652178676640589076170,3299118533618311787481942,true⟩,⟨(-3179012208646707867223404),(-2780078080814127174238350),true⟩⟩
  | 5,6 => ⟨⟨2915338614691557449664761,3288467878456488957993861,true⟩,⟨(-2985453738264954824285558),(-2606954662374188925017694),true⟩⟩
  | 5,7 => ⟨⟨2914319664726568667745798,3277522483612594732871684,true⟩,⟨(-2875651348137026333625286),(-2508752967587956053676568),true⟩⟩
  | 6,0 => ⟨⟨1599381274591158728373505,2224018589140556879684866,true⟩,⟨(-5902953868476127262329562),(-5206163383666972859968111),true⟩⟩
  | 6,1 => ⟨⟨1140099441168184950817353,1800804942418005708398496,true⟩,⟨(-6286189845019112005115445),(-5541721377002383218665000),true⟩⟩
  | 6,2 => ⟨⟨698430094638975899187611,1395033177277114491792912,true⟩,⟨(-6569760736290619992897337),(-5783588010876776331995873),true⟩⟩
  | 6,3 => ⟨⟨400040817149424216621578,1124672211106594739761488,true⟩,⟨(-6724360651875646448027558),(-5909912081024224015615414),true⟩⟩
  | 6,4 => ⟨⟨1989594053937352914021327,2577911343621698837322963,true⟩,⟨(-5477857587238525906267969),(-4830158519461849933391004),true⟩⟩
  | 6,5 => ⟨⟨2272454042634704379129026,2827257624572771898900138,true⟩,⟨(-5083455424092194429902920),(-4480000394874525875581159),true⟩⟩
  | 6,6 => ⟨⟨2448782638938525890655550,2977778822151636689365105,true⟩,⟨(-4779703071449665963488069),(-4209692546103605044623953),true⟩⟩
  | 6,7 => ⟨⟨2537256080227542394614345,3051119054071256759785825,true⟩,⟨(-4601909423693855741089315),(-4051270302740389031038354),true⟩⟩
  | 7,0 => ⟨⟨(-2513423776188578721068735),(-1569097509114044876009089),true⟩,⟨(-7062858466648812748807029),(-6084805923237357589983354),true⟩⟩
  | 7,1 => ⟨⟨(-3434926096549972187230334),(-2442461143729979907605128),true⟩,⟨(-6749669647305483548919042),(-5761331922514605578556998),true⟩⟩
  | 7,2 => ⟨⟨(-4131315387033080671196663),(-3112296101719872763272970),true⟩,⟨(-6337317271232730645890113),(-5359369769941121272248795),true⟩⟩
  | 7,3 => ⟨⟨(-4519844547111640924065716),(-3491246152890153767081444),true⟩,⟨(-6017437179555285714039585),(-5054801260317798126984355),true⟩⟩
  | 7,4 => ⟨⟨(-1539594514713343090934551),(-658529625585274916694781),true⟩,⟨(-7165846332766321474442918),(-6221528158129123320282438),true⟩⟩
  | 7,5 => ⟨⟨(-694544368386078248649733),122664797708984109009383,true⟩,⟨(-7082778063189848075101185),(-6184557624782878080419115),true⟩⟩
  | 7,6 => ⟨⟨(-87945725519594897801676),679434620810836728199882,true⟩,⟨(-6921977680486561912198087),(-6066546753245058429493300),true⟩⟩
  | 7,7 => ⟨⟨246495266486945308120630,984910632586167082257602,true⟩,⟨(-6793606717276804306686744),(-5965587301018090505265525),true⟩⟩
  | 8,0 => ⟨⟨(-5854138647904499402164407),(-4960569755117747931154099),true⟩,⟨(-2431934853556820845981475),(-1798072010842318639789732),true⟩⟩
  | 8,1 => ⟨⟨(-5605168538501440807719738),(-4811936012219709037945317),true⟩,⟨(-1367537224983234868987137),(-864681677832074478685283),true⟩⟩
  | 8,2 => ⟨⟨(-5241437028016304412410494),(-4540956980040469956918487),true⟩,⟨(-622722001192424384553697),(-223404010173971527094592),true⟩⟩
  | 8,3 => ⟨⟨(-4967563614959209863231391),(-4326538815087587755697260),true⟩,⟨(-230986842409481257992540),115237714296080357995272,true⟩⟩
  | 8,4 => ⟨⟨(-5813607094376447577539583),(-4838656815302574616541769),true⟩,⟨(-3632155273234941466120752),(-2865697996873380646248905),true⟩⟩
  | 8,5 => ⟨⟨(-5478547200969608250535167),(-4459384239630711737920237),true⟩,⟨(-4699715387596796940885159),(-3832412213046985313626824),true⟩⟩
  | 8,6 => ⟨⟨(-5030924832278100402057464),(-3998751732486048863288919),true⟩,⟨(-5448890576975195668677505),(-4522361327216269376911797),true⟩⟩
  | 8,7 => ⟨⟨(-4696560847410918790568079),(-3665319261580648756508900),true⟩,⟨(-5843516231885165798461082),(-4890901167865007082180385),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP524Value0_0 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP524Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value0_1 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP524Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value0_2 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP524Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value0_3 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP524Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value0_4 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP524Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value0_5 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP524Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value0_6 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP524Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value0_7 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP524Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP524Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 0 j)=sharedDiskP524Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP524Value0_0
  · exact sharedDiskP524Value0_1
  · exact sharedDiskP524Value0_2
  · exact sharedDiskP524Value0_3
  · exact sharedDiskP524Value0_4
  · exact sharedDiskP524Value0_5
  · exact sharedDiskP524Value0_6
  · exact sharedDiskP524Value0_7
private theorem sharedDiskP524Value1_0 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP524Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value1_1 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP524Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value1_2 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP524Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value1_3 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP524Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value1_4 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP524Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value1_5 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP524Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value1_6 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP524Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value1_7 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP524Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP524Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 1 j)=sharedDiskP524Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP524Value1_0
  · exact sharedDiskP524Value1_1
  · exact sharedDiskP524Value1_2
  · exact sharedDiskP524Value1_3
  · exact sharedDiskP524Value1_4
  · exact sharedDiskP524Value1_5
  · exact sharedDiskP524Value1_6
  · exact sharedDiskP524Value1_7
private theorem sharedDiskP524Value2_0 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP524Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value2_1 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP524Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value2_2 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP524Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value2_3 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP524Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value2_4 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP524Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value2_5 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP524Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value2_6 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP524Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value2_7 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP524Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP524Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 2 j)=sharedDiskP524Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP524Value2_0
  · exact sharedDiskP524Value2_1
  · exact sharedDiskP524Value2_2
  · exact sharedDiskP524Value2_3
  · exact sharedDiskP524Value2_4
  · exact sharedDiskP524Value2_5
  · exact sharedDiskP524Value2_6
  · exact sharedDiskP524Value2_7
private theorem sharedDiskP524Value3_0 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP524Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value3_1 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP524Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value3_2 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP524Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value3_3 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP524Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value3_4 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP524Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value3_5 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP524Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value3_6 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP524Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value3_7 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP524Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP524Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 3 j)=sharedDiskP524Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP524Value3_0
  · exact sharedDiskP524Value3_1
  · exact sharedDiskP524Value3_2
  · exact sharedDiskP524Value3_3
  · exact sharedDiskP524Value3_4
  · exact sharedDiskP524Value3_5
  · exact sharedDiskP524Value3_6
  · exact sharedDiskP524Value3_7
private theorem sharedDiskP524Value4_0 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP524Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value4_1 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP524Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value4_2 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP524Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value4_3 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP524Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value4_4 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP524Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value4_5 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP524Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value4_6 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP524Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value4_7 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP524Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP524Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 4 j)=sharedDiskP524Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP524Value4_0
  · exact sharedDiskP524Value4_1
  · exact sharedDiskP524Value4_2
  · exact sharedDiskP524Value4_3
  · exact sharedDiskP524Value4_4
  · exact sharedDiskP524Value4_5
  · exact sharedDiskP524Value4_6
  · exact sharedDiskP524Value4_7
private theorem sharedDiskP524Value5_0 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP524Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value5_1 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP524Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value5_2 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP524Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value5_3 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP524Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value5_4 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP524Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value5_5 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP524Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value5_6 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP524Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value5_7 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP524Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP524Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 5 j)=sharedDiskP524Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP524Value5_0
  · exact sharedDiskP524Value5_1
  · exact sharedDiskP524Value5_2
  · exact sharedDiskP524Value5_3
  · exact sharedDiskP524Value5_4
  · exact sharedDiskP524Value5_5
  · exact sharedDiskP524Value5_6
  · exact sharedDiskP524Value5_7
private theorem sharedDiskP524Value6_0 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP524Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value6_1 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP524Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value6_2 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP524Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value6_3 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP524Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value6_4 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP524Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value6_5 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP524Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value6_6 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP524Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value6_7 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP524Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP524Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 6 j)=sharedDiskP524Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP524Value6_0
  · exact sharedDiskP524Value6_1
  · exact sharedDiskP524Value6_2
  · exact sharedDiskP524Value6_3
  · exact sharedDiskP524Value6_4
  · exact sharedDiskP524Value6_5
  · exact sharedDiskP524Value6_6
  · exact sharedDiskP524Value6_7
private theorem sharedDiskP524Value7_0 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP524Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value7_1 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP524Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value7_2 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP524Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value7_3 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP524Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value7_4 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP524Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value7_5 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP524Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value7_6 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP524Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value7_7 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP524Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP524Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 7 j)=sharedDiskP524Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP524Value7_0
  · exact sharedDiskP524Value7_1
  · exact sharedDiskP524Value7_2
  · exact sharedDiskP524Value7_3
  · exact sharedDiskP524Value7_4
  · exact sharedDiskP524Value7_5
  · exact sharedDiskP524Value7_6
  · exact sharedDiskP524Value7_7
private theorem sharedDiskP524Value8_0 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP524Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value8_1 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP524Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value8_2 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP524Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value8_3 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP524Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value8_4 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP524Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value8_5 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP524Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value8_6 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP524Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP524Value8_7 : truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP524Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP524Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points 8 j)=sharedDiskP524Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP524Value8_0
  · exact sharedDiskP524Value8_1
  · exact sharedDiskP524Value8_2
  · exact sharedDiskP524Value8_3
  · exact sharedDiskP524Value8_4
  · exact sharedDiskP524Value8_5
  · exact sharedDiskP524Value8_6
  · exact sharedDiskP524Value8_7
theorem sharedDiskP524Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP524Params (sharedChord521Gauss8Points i j)=sharedDiskP524Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP524Values0_eq
  · exact sharedDiskP524Values1_eq
  · exact sharedDiskP524Values2_eq
  · exact sharedDiskP524Values3_eq
  · exact sharedDiskP524Values4_eq
  · exact sharedDiskP524Values5_eq
  · exact sharedDiskP524Values6_eq
  · exact sharedDiskP524Values7_eq
  · exact sharedDiskP524Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP524Box : HorizontalRectangle := ⟨(157/200),(63/80),(938043425991851/1649267441664000),(941264651463851/1649267441664000),(1150989680834289764192083644068585/2596148429267413814265248164610048),(3291802087612595023048331437355753/2596148429267413814265248164610048),(-1119083904206447061827739057705845/324518553658426726783156020576256),(-844965051492809368098332828291957/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP524Grid : CGrid := momentChordGrid sharedDiskP524Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP524Columns : containedInReported sharedDiskP524Grid.re sharedDiskP524Box.reLo sharedDiskP524Box.reHi=true ∧ containedInReported sharedDiskP524Grid.im sharedDiskP524Box.imLo sharedDiskP524Box.imHi=true := by
  rw [sharedDiskP524Grid,momentChordGrid_eq_tabulated sharedDiskP524Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP524Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP524Values_eq]
  decide +kernel
theorem sharedDiskP524Sound : sharedDiskP524Box.Sound := by
  intro t a tl tu al au
  change (((157/200):ℚ):ℝ)≤t at tl
  change t≤(((63/80):ℚ):ℝ) at tu
  change (((938043425991851/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((941264651463851/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP524Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(157/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((63/80):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(938043425991851/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((941264651463851/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP524Columns.1 sharedDiskP524Columns.2
def sharedDiskP524Rows : List SignRow := [positive_524.toSignRow]
theorem sharedDiskP524Rows_actual : ∀ r∈sharedDiskP524Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP524Rows.all (sharedDiskP524Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP524Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP525Params : ChordParams := ⟨⟨(-22664230446148547725878),(-22379905656825861485524),true⟩,⟨2060463328523315447774682,2076424006931416098460709,true⟩,⟨123711163376091030685001,125578396892454454394792,true⟩,⟨217002703057124835193188,219886647226183635987966,true⟩,⟨322918130443892280342563,325037946209692020327265,true⟩,⟨1164431511842829890738504,1164979551464025777528000,true⟩,⟨(-2323740444737597358027860),(-2315297141274614372030079),true⟩,⟨⟨1148371170256283556168064,1176594347422517623442541,true⟩,⟨(-5693216),5693216,true⟩⟩⟩
theorem sharedDiskP525Params_ok : chordParams (Grid.ofRats (63/80) (79/100)) (Grid.ofRats (939185997747569/1649267441664000) (942407223219569/1649267441664000))=sharedDiskP525Params := by decide +kernel
def sharedDiskP525Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3191051595900752055065910),(-2674266106885328476549585),true⟩,⟨(-359419792247537774261816),55478059569808359375650,true⟩⟩
  | 0,1 => ⟨⟨(-2796653408928046080312852),(-2326374163218923710546607),true⟩,⟨(-431005150867735739788679),(-41062498639980386096961),true⟩⟩
  | 0,2 => ⟨⟨(-2514888851007685044689897),(-2080686565368926565983589),true⟩,⟨(-490230717449871391742020),(-122901915026383366178784),true⟩⟩
  | 0,3 => ⟨⟨(-2357727418052793241473337),(-1944126611841138817056524),true⟩,⟨(-525930341123592657612359),(-171929201910785769231333),true⟩⟩
  | 0,4 => ⟨⟨(-3663946725560663857913954),(-3098621142612586592961038),true⟩,⟨(-293073018080781209869958),139262055757349347283060,true⟩⟩
  | 0,5 => ⟨⟨(-4151187118012260955292205),(-3544292925475512688075476),true⟩,⟨(-248975005868907966375191),189120389781625697275681,true⟩⟩
  | 0,6 => ⟨⟨(-4566788986583569372658679),(-3931290664195133696928744),true⟩,⟨(-232040531917351437376795),198837117774657879459695,true⟩⟩
  | 0,7 => ⟨⟨(-4829180724581192477060316),(-4178351893528943065950123),true⟩,⟨(-236162823538988900031519),188299387609237781824696,true⟩⟩
  | 1,0 => ⟨⟨(-1425660619262747297390488),(-1142276323114205601905567),true⟩,⟨(-759014177185715473415438),(-500700914789313494813756),true⟩⟩
  | 1,1 => ⟨⟨(-1224863611643848193668633),(-969665411769511176878382),true⟩,⟨(-808439498354839515733193),(-572415400309987112210714),true⟩⟩
  | 1,2 => ⟨⟨(-1079484295468340450194813),(-844261951567189840746911),true⟩,⟨(-842278772160752245857342),(-622237017325171325365939),true⟩⟩
  | 1,3 => ⟨⟨(-996929856416830353678955),(-772826743653923559570647),true⟩,⟨(-860476846303564360377976),(-649386454359774398592602),true⟩⟩
  | 1,4 => ⟨⟨(-1666256671998090547579901),(-1348671968731287210566217),true⟩,⟨(-697680372030313517522013),(-412862633847344849195832),true⟩⟩
  | 1,5 => ⟨⟨(-1918396157874978629181285),(-1565086882062616049346651),true⟩,⟨(-633210740967619277842122),(-321567871051454680387747),true⟩⟩
  | 1,6 => ⟨⟨(-2140256359991563020991062),(-1756074894984321924702807),true⟩,⟨(-577873692568086079698109),(-243997182071176014912068),true⟩⟩
  | 1,7 => ⟨⟨(-2284622223824450069612043),(-1880801567773280073394866),true⟩,⟨(-543087942432396226347624),(-195645769108485991875297),true⟩⟩
  | 2,0 => ⟨⟨(-87955567437509271841520),48064010403744588136827,true⟩,⟨(-984411453885052975551262),(-841557999805961632538204),true⟩⟩
  | 2,1 => ⟨⟨105350304744164995919041,231282891486685341096864,true⟩,⟨(-984130107652448206562774),(-850256024882601026050591),true⟩⟩
  | 2,2 => ⟨⟨246235873224880508627496,367056881401626311375539,true⟩,⟨(-977664585757551219351830),(-849054060662950413490354),true⟩⟩
  | 2,3 => ⟨⟨326480268050937909058527,446082633090176025250504,true⟩,⟨(-972110241235769449502107),(-845365454066697067794573),true⟩⟩
  | 2,4 => ⟨⟨(-319646296355987226477446),(-167534868756444090572052),true⟩,⟨(-970940794034403567294238),(-815549773877967823135473),true⟩⟩
  | 2,5 => ⟨⟨(-565302140909831736822372),(-392311367345359226658097),true⟩,⟨(-940817342353388245370247),(-769981138725605971044200),true⟩⟩
  | 2,6 => ⟨⟨(-788891799064268705481498),(-591895060183541764431059),true⟩,⟨(-902048383208351663086550),(-712920705215151327590774),true⟩⟩
  | 2,7 => ⟨⟨(-939062113415873634570659),(-722638873262341040341341),true⟩,⟨(-872704707545814503040482),(-667817406760850272220663),true⟩⟩
  | 3,0 => ⟨⟨1264247336168337247283353,1393672067669712704440326,true⟩,⟨(-874136500728660119118107),(-749440095925929243913466),true⟩⟩
  | 3,1 => ⟨⟨1484967528126358630511054,1620540150070024793333476,true⟩,⟨(-875266354947873287289056),(-746807215905544262849547),true⟩⟩
  | 3,2 => ⟨⟨1653918676828602016199545,1795516821264443943483768,true⟩,⟨(-895243242238845946618325),(-762321038100580613029671),true⟩⟩
  | 3,3 => ⟨⟨1754623017265156557292820,1900463401367288505082237,true⟩,⟨(-917444909225885850068112),(-781085769889661031553708),true⟩⟩
  | 3,4 => ⟨⟨1011725123177662494529399,1136069909070682566735234,true⟩,⟨(-894820950885419442785812),(-772122965092883900020424),true⟩⟩
  | 3,5 => ⟨⟨754262954686760112720142,875280603252178426013259,true⟩,⟨(-926419720372243614988532),(-803702365623560920238634),true⟩⟩
  | 3,6 => ⟨⟨529500176142275749791239,649101781493744413539203,true⟩,⟨(-953481484317035254679430),(-829254988257674836905685),true⟩⟩
  | 3,7 => ⟨⟨382501817299574034971099,501975183557060787400454,true⟩,⟨(-967749267590455409688749),(-841809814409453219423507),true⟩⟩
  | 4,0 => ⟨⟨2511532704458185259626030,2740121680099627262610119,true⟩,⟨(-1514860465615290746030743),(-1297005005054601664357241),true⟩⟩
  | 4,1 => ⟨⟨2715524212719921882446556,2987592202947323054052407,true⟩,⟨(-1928478279210485497020780),(-1664081952517838017158477),true⟩⟩
  | 4,2 => ⟨⟨2842864638005035619919887,3160964555587341580808021,true⟩,⟨(-2402366955094428138239377),(-2086793057187151278862819),true⟩⟩
  | 4,3 => ⟨⟨2885087946224053422447552,3237468841396516065256208,true⟩,⟨(-2771932563769333831288304),(-2417124985958391859420952),true⟩⟩
  | 4,4 => ⟨⟨2280727353426095376799457,2475339212396606152837750,true⟩,⟨(-1227385283625470029505107),(-1044407636430149751828486),true⟩⟩
  | 4,5 => ⟨⟨2068078437628966314378902,2239079945852825214763166,true⟩,⟨(-1056950255206997729837942),(-897200883602701938484070),true⟩⟩
  | 4,6 => ⟨⟨1902426859778765991632725,2058670994699786076230574,true⟩,⟨(-969082564509957185113552),(-823291218408091997717570),true⟩⟩
  | 4,7 => ⟨⟨1803090119054773795754423,1951748925927778714067185,true⟩,⟨(-931688701993743195648655),(-792856023064769239795726),true⟩⟩
  | 5,0 => ⟨⟨2793226755054783997717845,3235185359290391095598518,true⟩,⟨(-3781412766509670498569585),(-3319955893536193409800293),true⟩⟩
  | 5,1 => ⟨⟨2705129903029490133836855,3174533444862875756718080,true⟩,⟨(-4099246111507140030830789),(-3603955570550024236585411),true⟩⟩
  | 5,2 => ⟨⟨2607642808593408053674074,3100134850462351376402169,true⟩,⟨(-4368612326212512842389012),(-3844435898537393981344394),true⟩⟩
  | 5,3 => ⟨⟨2535018588836738145854541,3041987434788912607498231,true⟩,⟨(-4538211450489207396153175),(-3995722939494698873561703),true⟩⟩
  | 5,4 => ⟨⟨2852349005752001817443255,3267009168242886439740046,true⟩,⟨(-3468569736353644091343988),(-3040229366819886683138184),true⟩⟩
  | 5,5 => ⟨⟨2881217803335402873090314,3272382284255983626456921,true⟩,⟨(-3202589788215713315664513),(-2802323552382621197248120),true⟩⟩
  | 5,6 => ⟨⟨2889668819188324268544423,3263505212043297341435035,true⟩,⟨(-3008750724688804893270338),(-2628932267087082870611716),true⟩⟩
  | 5,7 => ⟨⟨2889620922260876769783558,3253531103693310383954887,true⟩,⟨(-2898719542711999681757546),(-2530514841862047778082584),true⟩⟩
  | 6,0 => ⟨⟨1545377727577819275474513,2169183272981330725000383,true⟩,⟨(-5910031114192937786289160),(-5213571479811333133476821),true⟩⟩
  | 6,1 => ⟨⟨1082104063594910352432319,1742714500406011863917316,true⟩,⟨(-6287093876567288187153918),(-5542887788540168417381175),true⟩⟩
  | 6,2 => ⟨⟨639082336438012137981725,1336447869620137872270329,true⟩,⟨(-6564128698310102551962643),(-5778098116052108263281775),true⟩⟩
  | 6,3 => ⟨⟨340385120350698199402206,1065484612273186753825489,true⟩,⟨(-6714349578344185785618168),(-5900481589887617008819085),true⟩⟩
  | 6,4 => ⟨⟨1939309697486929633730871,2527254912179854439749621,true⟩,⟨(-5490734020818285747771095),(-4842798550958853594766362),true⟩⟩
  | 6,5 => ⟨⟨2225973036561113263260399,2780738035765939255782843,true⟩,⟨(-5100360976197662875622336),(-4496277310119778493102050),true⟩⟩
  | 6,6 => ⟨⟨2405355433868502866672309,2934519945672265772189574,true⟩,⟨(-4798982150556352493191171),(-4228111173646600623704836),true⟩⟩
  | 6,7 => ⟨⟨2495642390788288795243973,3009776937238411192177873,true⟩,⟨(-4622316010743769911306667),(-4070705404074667859360597),true⟩⟩
  | 7,0 => ⟨⟨(-2556363392049516774427085),(-1614789334994889405885521),true⟩,⟨(-7015927897986125600687890),(-6042959807756382817758008),true⟩⟩
  | 7,1 => ⟨⟨(-3465914644765364251396506),(-2477566322435409330588272),true⟩,⟨(-6695077876532883826393187),(-5713132901532150180334149),true⟩⟩
  | 7,2 => ⟨⟨(-4151116275255423974228964),(-3137274291450037662179437),true⟩,⟨(-6279252063623197971688918),(-5308541651625455144880701),true⟩⟩
  | 7,3 => ⟨⟨(-4532490617275270974900362),(-3509659896590859282495221),true⟩,⟨(-5958684292010848097263865),(-5003663423922707211716318),true⟩⟩
  | 7,4 => ⟨⟨(-1591821236621005982470314),(-712153695444345389529935),true⟩,⟨(-7129617409967701368225448),(-6188886397688634540429190),true⟩⟩
  | 7,5 => ⟨⟨(-751989342866394092565857),64690198238429838876878,true⟩,⟨(-7057357799423068154138959),(-6161397626529157819614597),true⟩⟩
  | 7,6 => ⟨⟨(-147387235584637992288940),620162165682892948111724,true⟩,⟨(-6904938423979335766593924),(-6050826923115705157710379),true⟩⟩
  | 7,7 => ⟨⟨186854650549370337000562,925580385683277449835579,true⟩,⟨(-6781362660142289745747150),(-5954153835994402617321182),true⟩⟩
  | 8,0 => ⟨⟨(-5827884543281295630205235),(-4941108046033572608686585),true⟩,⟨(-2402397183057498065973814),(-1774363715908970397154587),true⟩⟩
  | 8,1 => ⟨⟨(-5578698044049344043111789),(-4791152588827943218380192),true⟩,⟨(-1351380132556634577334118),(-852669229870725158224214),true⟩⟩
  | 8,2 => ⟨⟨(-5218146209718413200961315),(-4522197053549875261387865),true⟩,⟨(-615849197414711718049063),(-219346162021418142156040),true⟩⟩
  | 8,3 => ⟨⟨(-4947258193058925463728075),(-4309987914976014193393570),true⟩,⟨(-228724118169310439623570),115470379743766393075537,true⟩⟩
  | 8,4 => ⟨⟨(-5793651761765797220241635),(-4826006808041788251476666),true⟩,⟨(-3588800149644120836915947),(-2829576120067183161010131),true⟩⟩
  | 8,5 => ⟨⟨(-5469535421653038526910970),(-4457469017660889367335096),true⟩,⟨(-4646571973570692025262519),(-3787174349463175076943324),true⟩⟩
  | 8,6 => ⟨⟨(-5032927183844495407050303),(-4007272513478849991286043),true⟩,⟨(-5391303196589076185160057),(-4472712323607791916241413),true⟩⟩
  | 8,7 => ⟨⟨(-4705702594148986957142058),(-3680493374426421518175145),true⟩,⟨(-5784850114333688997479450),(-4839989392371001783152482),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP525Value0_0 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP525Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value0_1 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP525Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value0_2 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP525Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value0_3 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP525Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value0_4 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP525Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value0_5 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP525Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value0_6 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP525Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value0_7 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP525Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP525Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 0 j)=sharedDiskP525Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP525Value0_0
  · exact sharedDiskP525Value0_1
  · exact sharedDiskP525Value0_2
  · exact sharedDiskP525Value0_3
  · exact sharedDiskP525Value0_4
  · exact sharedDiskP525Value0_5
  · exact sharedDiskP525Value0_6
  · exact sharedDiskP525Value0_7
private theorem sharedDiskP525Value1_0 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP525Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value1_1 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP525Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value1_2 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP525Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value1_3 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP525Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value1_4 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP525Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value1_5 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP525Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value1_6 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP525Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value1_7 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP525Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP525Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 1 j)=sharedDiskP525Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP525Value1_0
  · exact sharedDiskP525Value1_1
  · exact sharedDiskP525Value1_2
  · exact sharedDiskP525Value1_3
  · exact sharedDiskP525Value1_4
  · exact sharedDiskP525Value1_5
  · exact sharedDiskP525Value1_6
  · exact sharedDiskP525Value1_7
private theorem sharedDiskP525Value2_0 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP525Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value2_1 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP525Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value2_2 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP525Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value2_3 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP525Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value2_4 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP525Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value2_5 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP525Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value2_6 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP525Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value2_7 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP525Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP525Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 2 j)=sharedDiskP525Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP525Value2_0
  · exact sharedDiskP525Value2_1
  · exact sharedDiskP525Value2_2
  · exact sharedDiskP525Value2_3
  · exact sharedDiskP525Value2_4
  · exact sharedDiskP525Value2_5
  · exact sharedDiskP525Value2_6
  · exact sharedDiskP525Value2_7
private theorem sharedDiskP525Value3_0 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP525Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value3_1 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP525Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value3_2 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP525Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value3_3 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP525Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value3_4 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP525Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value3_5 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP525Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value3_6 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP525Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value3_7 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP525Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP525Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 3 j)=sharedDiskP525Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP525Value3_0
  · exact sharedDiskP525Value3_1
  · exact sharedDiskP525Value3_2
  · exact sharedDiskP525Value3_3
  · exact sharedDiskP525Value3_4
  · exact sharedDiskP525Value3_5
  · exact sharedDiskP525Value3_6
  · exact sharedDiskP525Value3_7
private theorem sharedDiskP525Value4_0 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP525Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value4_1 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP525Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value4_2 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP525Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value4_3 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP525Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value4_4 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP525Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value4_5 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP525Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value4_6 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP525Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value4_7 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP525Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP525Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 4 j)=sharedDiskP525Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP525Value4_0
  · exact sharedDiskP525Value4_1
  · exact sharedDiskP525Value4_2
  · exact sharedDiskP525Value4_3
  · exact sharedDiskP525Value4_4
  · exact sharedDiskP525Value4_5
  · exact sharedDiskP525Value4_6
  · exact sharedDiskP525Value4_7
private theorem sharedDiskP525Value5_0 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP525Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value5_1 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP525Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value5_2 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP525Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value5_3 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP525Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value5_4 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP525Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value5_5 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP525Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value5_6 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP525Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value5_7 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP525Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP525Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 5 j)=sharedDiskP525Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP525Value5_0
  · exact sharedDiskP525Value5_1
  · exact sharedDiskP525Value5_2
  · exact sharedDiskP525Value5_3
  · exact sharedDiskP525Value5_4
  · exact sharedDiskP525Value5_5
  · exact sharedDiskP525Value5_6
  · exact sharedDiskP525Value5_7
private theorem sharedDiskP525Value6_0 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP525Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value6_1 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP525Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value6_2 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP525Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value6_3 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP525Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value6_4 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP525Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value6_5 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP525Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value6_6 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP525Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value6_7 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP525Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP525Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 6 j)=sharedDiskP525Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP525Value6_0
  · exact sharedDiskP525Value6_1
  · exact sharedDiskP525Value6_2
  · exact sharedDiskP525Value6_3
  · exact sharedDiskP525Value6_4
  · exact sharedDiskP525Value6_5
  · exact sharedDiskP525Value6_6
  · exact sharedDiskP525Value6_7
private theorem sharedDiskP525Value7_0 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP525Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value7_1 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP525Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value7_2 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP525Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value7_3 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP525Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value7_4 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP525Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value7_5 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP525Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value7_6 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP525Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value7_7 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP525Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP525Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 7 j)=sharedDiskP525Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP525Value7_0
  · exact sharedDiskP525Value7_1
  · exact sharedDiskP525Value7_2
  · exact sharedDiskP525Value7_3
  · exact sharedDiskP525Value7_4
  · exact sharedDiskP525Value7_5
  · exact sharedDiskP525Value7_6
  · exact sharedDiskP525Value7_7
private theorem sharedDiskP525Value8_0 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP525Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value8_1 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP525Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value8_2 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP525Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value8_3 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP525Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value8_4 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP525Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value8_5 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP525Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value8_6 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP525Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP525Value8_7 : truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP525Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP525Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points 8 j)=sharedDiskP525Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP525Value8_0
  · exact sharedDiskP525Value8_1
  · exact sharedDiskP525Value8_2
  · exact sharedDiskP525Value8_3
  · exact sharedDiskP525Value8_4
  · exact sharedDiskP525Value8_5
  · exact sharedDiskP525Value8_6
  · exact sharedDiskP525Value8_7
theorem sharedDiskP525Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP525Params (sharedChord521Gauss8Points i j)=sharedDiskP525Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP525Values0_eq
  · exact sharedDiskP525Values1_eq
  · exact sharedDiskP525Values2_eq
  · exact sharedDiskP525Values3_eq
  · exact sharedDiskP525Values4_eq
  · exact sharedDiskP525Values5_eq
  · exact sharedDiskP525Values6_eq
  · exact sharedDiskP525Values7_eq
  · exact sharedDiskP525Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP525Box : HorizontalRectangle := ⟨(63/80),(79/100),(939185997747569/1649267441664000),(942407223219569/1649267441664000),(540747795767590585241342176247875/1298074214633706907132624082305024),(1607348003280844736828714053124163/1298074214633706907132624082305024),(-2238896698150800086640940724611283/649037107316853453566312041152512),(-1692573118823643490764057446017235/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP525Grid : CGrid := momentChordGrid sharedDiskP525Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP525Columns : containedInReported sharedDiskP525Grid.re sharedDiskP525Box.reLo sharedDiskP525Box.reHi=true ∧ containedInReported sharedDiskP525Grid.im sharedDiskP525Box.imLo sharedDiskP525Box.imHi=true := by
  rw [sharedDiskP525Grid,momentChordGrid_eq_tabulated sharedDiskP525Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP525Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP525Values_eq]
  decide +kernel
theorem sharedDiskP525Sound : sharedDiskP525Box.Sound := by
  intro t a tl tu al au
  change (((63/80):ℚ):ℝ)≤t at tl
  change t≤(((79/100):ℚ):ℝ) at tu
  change (((939185997747569/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((942407223219569/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP525Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(63/80))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((79/100):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(939185997747569/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((942407223219569/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP525Columns.1 sharedDiskP525Columns.2
def sharedDiskP525Rows : List SignRow := [positive_525.toSignRow]
theorem sharedDiskP525Rows_actual : ∀ r∈sharedDiskP525Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP525Rows.all (sharedDiskP525Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP525Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP526Params : ChordParams := ⟨⟨(-22950339375117034578195),(-22664230446148547725392),true⟩,⟨2050626343948300592768717,2066505384182404042487351,true⟩,⟨124262234709463444206659,126130056502541044998253,true⟩,⟨218790423736316262485562,221683155872557249060131,true⟩,⟨324887433836440007210347,327007610160203003641630,true⟩,⟨1163880288638121005882520,1164431511842829890739442,true⟩,⟨(-2315297141274614372039323),(-2306900797756144512568534),true⟩,⟨⟨1147738762958151773285749,1176003873852944146186457,true⟩,⟨(-6510558),6510558,true⟩⟩⟩
theorem sharedDiskP526Params_ok : chordParams (Grid.ofRats (79/100) (317/400)) (Grid.ofRats (940334442440647/1649267441664000) (943555667912647/1649267441664000))=sharedDiskP526Params := by decide +kernel
def sharedDiskP526Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3189475928979099863653622),(-2673205381392434957229345),true⟩,⟨(-356207232954383488312063),58099231546968550372792,true⟩⟩
  | 0,1 => ⟨⟨(-2798129432262959038294327),(-2327942191629078457272632),true⟩,⟨(-426726693137721180650474),(-37021911998315557840333),true⟩⟩
  | 0,2 => ⟨⟨(-2518227587189342434805209),(-2083898632391275090776850),true⟩,⟨(-485226171646781955625967),(-117996612392093292054127),true⟩⟩
  | 0,3 => ⟨⟨(-2362048710440287514609475),(-1948177172627184008463900),true⟩,⟨(-520550982197016026789005),(-166515732168019336776748),true⟩⟩
  | 0,4 => ⟨⟨(-3658213734744928545396053),(-3093898044750501550806501),true⟩,⟨(-291085858316713494866737),140317736055292838620794,true⟩⟩
  | 0,5 => ⟨⟨(-4140667299533059778185305),(-3535244982382760470626200),true⟩,⟨(-248045502217685073394977),188956869204326766355468,true⟩⟩
  | 0,6 => ⟨⟨(-4551843394708705194447038),(-3918159202537568043603287),true⟩,⟨(-231753178797669610980601),198020476508692849812834,true⟩⟩
  | 0,7 => ⟨⟨(-4811317138268291084107112),(-4162482758059788925337869),true⟩,⟨(-236150711330486545964151),187323401730695061070128,true⟩⟩
  | 1,0 => ⟨⟨(-1434600435440507815986164),(-1150329276038507493812425),true⟩,⟨(-752420227853406867453912),(-493486833062902596241440),true⟩⟩
  | 1,1 => ⟨⟨(-1234584874209778967308182),(-978438335530552609409025),true⟩,⟨(-801937119133448564792079),(-565238366543541265150324),true⟩⟩
  | 1,2 => ⟨⟨(-1089743384958471767714111),(-853544748270396880464896),true⟩,⟨(-835948176400987958335137),(-615208836232418527046742),true⟩⟩
  | 1,3 => ⟨⟨(-1007486888881833672122198),(-782397321275757120446426),true⟩,⟨(-854285929012833313318280),(-642490425073391199984308),true⟩⟩
  | 1,4 => ⟨⟨(-1674179570606119998498927),(-1355817784018047981634750),true⟩,⟨(-691174201367379046104371),(-405838773801744401630453),true⟩⟩
  | 1,5 => ⟨⟨(-1925133736912802565508848),(-1571202614010330752872850),true⟩,⟨(-626989381288110018928624),(-314977437992385847412190),true⟩⟩
  | 1,6 => ⟨⟨(-2145832917833583516110098),(-1761195882767316777356918),true⟩,⟨(-572032432586296207029271),(-237946595621918943802058),true⟩⟩
  | 1,7 => ⟨⟨(-2289378842502545926392874),(-1885223231157634895005014),true⟩,⟨(-537545022497343760653187),(-190008291400253026554603),true⟩⟩
  | 2,0 => ⟨⟨(-101514503640709531599786),34936602529408039976491,true⟩,⟨(-981642584912513801123597),(-838556991068069840076040),true⟩⟩
  | 2,1 => ⟨⟨91175155760719349955425,217435749760392546335911,true⟩,⟨(-982544271654960196633127),(-848444046720103514897640),true⟩⟩
  | 2,2 => ⟨⟨231595926639661024119651,352481942510161223081771,true⟩,⟨(-976990054457354621914903),(-848304741334355706685291),true⟩⟩
  | 2,3 => ⟨⟨311819535155875922192821,431237381687297404680461,true⟩,⟨(-971810661632507052845850),(-845147799452051074795469),true⟩⟩
  | 2,4 => ⟨⟨(-332393294952900613530663),(-179734203050817779325160),true⟩,⟨(-966906047829992431434349),(-811263450461730894505953),true⟩⟩
  | 2,5 => ⟨⟨(-577197716197512073825294),(-403580737752448907641025),true⟩,⟨(-935677552854188891135686),(-764559739916328213463809),true⟩⟩
  | 2,6 => ⟨⟨(-800185232974669603857893),(-602192205563197043519796),true⟩,⟨(-896350739153699925758226),(-706513273201572924781220),true⟩⟩
  | 2,7 => ⟨⟨(-949825627891085527489166),(-732411068957151545505864),true⟩,⟨(-866630489447141171122148),(-661034896703989467161228),true⟩⟩
  | 3,0 => ⟨⟨1248147551755968822046629,1377403404426163499543708,true⟩,⟨(-879976060535403567204545),(-755209253474105199102921),true⟩⟩
  | 3,1 => ⟨⟨1469073072464034865045618,1604546717159529217255066,true⟩,⟨(-882475093535911226334974),(-753863210277810077281908),true⟩⟩
  | 3,2 => ⟨⟨1638287492965970785451638,1779857556572204136613436,true⟩,⟨(-903528803353630128334071),(-770377304156633436314784),true⟩⟩
  | 3,3 => ⟨⟨1739170218412221793489062,1885031725838204109474866,true⟩,⟨(-926401067059734641723839),(-789761156461690344463643),true⟩⟩
  | 3,4 => ⟨⟨995652067079750058839975,1119779905183358339611987,true⟩,⟨(-899076659282184560119898),(-776379522693775534833802),true⟩⟩
  | 3,5 => ⟨⟨738517652494462835901716,859303629843507614199915,true⟩,⟨(-929000376170600400356846),(-806332995910694405514828),true⟩⟩
  | 3,6 => ⟨⟨514256234398467555496807,633640307055907895793849,true⟩,⟨(-954554035642350854218267),(-830401902090396365783575),true⟩⟩
  | 3,7 => ⟨⟨367670249052379186460114,486948157346040888908616,true⟩,⟨(-967827182150916598152765),(-841968924554386183537692),true⟩⟩
  | 4,0 => ⟨⟨2495837171175499080168158,2724824789925027205902338,true⟩,⟨(-1530724613492377369260318),(-1312083515532567118188275),true⟩⟩
  | 4,1 => ⟨⟨2697790999857996422423360,2970405460731898480666745,true⟩,⟨(-1947252579850014349944275),(-1681853764218424443247680),true⟩⟩
  | 4,2 => ⟨⟨2821898502413914944849660,3140646930929109483797303,true⟩,⟨(-2423557369707941464965555),(-2106806727986188466099930),true⟩⟩
  | 4,3 => ⟨⟨2861140609299758157067938,3214203723654340008768511,true⟩,⟨(-2794370417491993218127821),(-2438302237414427291659065),true⟩⟩
  | 4,4 => ⟨⟨2265772462084347010296175,2460639902393139579811596,true⟩,⟨(-1240652218707496579863856),(-1057084415828078222065553),true⟩⟩
  | 4,5 => ⟨⟨2053122676272106986959868,2224270867766899924264639,true⟩,⟨(-1068264249237115957275641),(-908069458513950584755274),true⟩⟩
  | 4,6 => ⟨⟨1887243506058279066805405,2043564749780184908419534,true⟩,⟨(-979089543928803130067793),(-832945435482880082011412),true⟩⟩
  | 4,7 => ⟨⟨1787726571860933504989938,1936427064570779539075243,true⟩,⟨(-940979383183569145422561),(-801841949897733246946328),true⟩⟩
  | 5,0 => ⟨⟨2759862007131939953882033,3202390695688595446945391,true⟩,⟨(-3804332655868975148297337),(-3341630901108003356348278),true⟩⟩
  | 5,1 => ⟨⟨2668576430196568268574572,3138449393987504433926976,true⟩,⟨(-4121364727427511007874459),(-3624916478517779415009768),true⟩⟩
  | 5,2 => ⟨⟨2568355408422687722881641,3061204750741645145593691,true⟩,⟨(-4389657704234721028097139),(-3864432602444723199701584),true⟩⟩
  | 5,3 => ⟨⟨2494007224257882771062215,3001249376767482969816046,true⟩,⟨(-4558383863341313115645633),(-4014933229304039213863417),true⟩⟩
  | 5,4 => ⟨⟨2822047084166107325842710,3237344876725213883537590,true⟩,⟨(-3491816177020684649816954),(-3062185523848730711433524),true⟩⟩
  | 5,5 => ⟨⟨2853432414163947864785783,3245268441374158918462372,true⟩,⟨(-3225771244521675317388996),(-2824205526303131450698336),true⟩⟩
  | 5,6 => ⟨⟨2863652029609006254246794,3238171464766048363181365,true⟩,⟨(-3031693507847087716906853),(-2650585042581721461416571),true⟩⟩
  | 5,7 => ⟨⟨2864579180867050951673509,3229174045300257530308583,true⟩,⟨(-2921456630021802594767199),(-2551973179499601779806761),true⟩⟩
  | 6,0 => ⟨⟨1491462843718318174805774,2114384484711463613243808,true⟩,⟨(-5916136708240233481946699),(-5220082965227642503406226),true⟩⟩
  | 6,1 => ⟨⟨1024372756686099762815699,1684824676379839050300106,true⟩,⟨(-6286990336924747267910819),(-5543130168151700925520389),true⟩⟩
  | 6,2 => ⟨⟨580147614764865794407138,1278196641348045398316583,true⟩,⟨(-6557495643601573649851369),(-5771699506608196083780939),true⟩⟩
  | 6,3 => ⟨⟨281237058584112248350018,1006724300423813214399111,true⟩,⟨(-6703358301832584509172458),(-5890162860499492202800819),true⟩⟩
  | 6,4 => ⟨⟨1888971075397789762156101,2476493126555685762775505,true⟩,⟨(-5502701935901570119750621),(-4854601067746861310585802),true⟩⟩
  | 6,5 => ⟨⟨2179334505553596501285241,2734012436618196599807143,true⟩,⟨(-5116434179698331050549371),(-4511787452865676109160748),true⟩⟩
  | 6,6 => ⟨⟨2361707967654702280421331,2890995049149803755458449,true⟩,⟨(-4817494571781754458500468),(-4245823880098065506953779),true⟩⟩
  | 6,7 => ⟨⟨2453777941872229055071485,2968140112904752625461122,true⟩,⟨(-4641996209049725306538472),(-4089471850470095186259155),true⟩⟩
  | 7,0 => ⟨⟨(-2598248764530993516387855),(-1659486752797072305332377),true⟩,⟨(-6968683990359184178788543),(-6000832501178168792363890),true⟩⟩
  | 7,1 => ⟨⟨(-3495870603788616769254169),(-2511672911484174810807283),true⟩,⟨(-6640485453665605831802117),(-5664928945161809958077885),true⟩⟩
  | 7,2 => ⟨⟨(-4169986026984131229897806),(-3161329470967288756109408),true⟩,⟨(-6221426712640456910237885),(-5257917616478864453081659),true⟩⟩
  | 7,3 => ⟨⟨(-4544301309348419974231404),(-3527229320356536580916499),true⟩,⟨(-5900299307584444319453044),(-4952839189066701823451569),true⟩⟩
  | 7,4 => ⟨⟨(-1643084841357712160956874),(-764892249965366432332886),true⟩,⟨(-7092780673815867426151542),(-6155699234519497576298252),true⟩⟩
  | 7,5 => ⟨⟨(-808629371072808025501811),7438489697705927717225,true⟩,⟨(-7031124419564206484373387),(-6137505234551327913861534),true⟩⟩
  | 7,6 => ⟨⟨(-206175754452663495288153),561458694166168588791977,true⟩,⟨(-6886977449207672837011499),(-6034274181238503563145912),true⟩⟩
  | 7,7 => ⟨⟨127768183039058025385300,866723555324125545728682,true⟩,⟨(-6768153708894462566769198),(-5941846786924522689620497),true⟩⟩
  | 8,0 => ⟨⟨(-5801724991414851038155439),(-4921648937283029184885274),true⟩,⟨(-2373306078711715121452391),(-1751006383294128740508585),true⟩⟩
  | 8,1 => ⟨⟨(-5552407483492145348522384),(-4770468993138162583006519),true⟩,⟨(-1335470145924312097063099),(-840834703255088096644006),true⟩⟩
  | 8,2 => ⟨⟨(-5195020413156388881360429),(-4503540173563626108067487),true⟩,⟨(-609074983324717264753695),(-215340809279988268536894),true⟩⟩
  | 8,3 => ⟨⟨(-4927082089382978689699727),(-4293517861151098575183700),true⟩,⟨(-226488567709974070120353),115708721875463844571725,true⟩⟩
  | 8,4 => ⟨⟨(-5773565460114038931937939),(-4813141145011470373313497),true⟩,⟨(-3546040622240303124600569),(-2793942312331745775262039),true⟩⟩
  | 8,5 => ⟨⟨(-5460103490370673724410817),(-4455072665150979265897584),true⟩,⟨(-4594037352486829608090966),(-3742446658835451919468634),true⟩⟩
  | 8,6 => ⟨⟨(-5034275163170132484524768),(-4015104250482152146609902),true⟩,⟨(-5334233360236333201167227),(-4423502048308397243023399),true⟩⟩
  | 8,7 => ⟨⟨(-4714063628864551581665844),(-3694869384631064161502448),true⟩,⟨(-5726606861419719186468007),(-4789437659306244383918602),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP526Value0_0 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP526Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value0_1 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP526Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value0_2 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP526Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value0_3 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP526Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value0_4 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP526Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value0_5 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP526Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value0_6 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP526Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value0_7 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP526Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP526Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 0 j)=sharedDiskP526Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP526Value0_0
  · exact sharedDiskP526Value0_1
  · exact sharedDiskP526Value0_2
  · exact sharedDiskP526Value0_3
  · exact sharedDiskP526Value0_4
  · exact sharedDiskP526Value0_5
  · exact sharedDiskP526Value0_6
  · exact sharedDiskP526Value0_7
private theorem sharedDiskP526Value1_0 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP526Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value1_1 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP526Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value1_2 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP526Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value1_3 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP526Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value1_4 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP526Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value1_5 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP526Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value1_6 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP526Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value1_7 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP526Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP526Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 1 j)=sharedDiskP526Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP526Value1_0
  · exact sharedDiskP526Value1_1
  · exact sharedDiskP526Value1_2
  · exact sharedDiskP526Value1_3
  · exact sharedDiskP526Value1_4
  · exact sharedDiskP526Value1_5
  · exact sharedDiskP526Value1_6
  · exact sharedDiskP526Value1_7
private theorem sharedDiskP526Value2_0 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP526Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value2_1 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP526Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value2_2 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP526Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value2_3 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP526Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value2_4 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP526Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value2_5 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP526Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value2_6 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP526Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value2_7 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP526Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP526Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 2 j)=sharedDiskP526Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP526Value2_0
  · exact sharedDiskP526Value2_1
  · exact sharedDiskP526Value2_2
  · exact sharedDiskP526Value2_3
  · exact sharedDiskP526Value2_4
  · exact sharedDiskP526Value2_5
  · exact sharedDiskP526Value2_6
  · exact sharedDiskP526Value2_7
private theorem sharedDiskP526Value3_0 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP526Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value3_1 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP526Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value3_2 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP526Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value3_3 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP526Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value3_4 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP526Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value3_5 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP526Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value3_6 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP526Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value3_7 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP526Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP526Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 3 j)=sharedDiskP526Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP526Value3_0
  · exact sharedDiskP526Value3_1
  · exact sharedDiskP526Value3_2
  · exact sharedDiskP526Value3_3
  · exact sharedDiskP526Value3_4
  · exact sharedDiskP526Value3_5
  · exact sharedDiskP526Value3_6
  · exact sharedDiskP526Value3_7
private theorem sharedDiskP526Value4_0 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP526Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value4_1 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP526Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value4_2 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP526Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value4_3 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP526Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value4_4 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP526Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value4_5 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP526Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value4_6 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP526Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value4_7 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP526Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP526Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 4 j)=sharedDiskP526Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP526Value4_0
  · exact sharedDiskP526Value4_1
  · exact sharedDiskP526Value4_2
  · exact sharedDiskP526Value4_3
  · exact sharedDiskP526Value4_4
  · exact sharedDiskP526Value4_5
  · exact sharedDiskP526Value4_6
  · exact sharedDiskP526Value4_7
private theorem sharedDiskP526Value5_0 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP526Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value5_1 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP526Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value5_2 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP526Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value5_3 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP526Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value5_4 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP526Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value5_5 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP526Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value5_6 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP526Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value5_7 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP526Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP526Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 5 j)=sharedDiskP526Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP526Value5_0
  · exact sharedDiskP526Value5_1
  · exact sharedDiskP526Value5_2
  · exact sharedDiskP526Value5_3
  · exact sharedDiskP526Value5_4
  · exact sharedDiskP526Value5_5
  · exact sharedDiskP526Value5_6
  · exact sharedDiskP526Value5_7
private theorem sharedDiskP526Value6_0 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP526Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value6_1 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP526Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value6_2 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP526Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value6_3 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP526Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value6_4 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP526Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value6_5 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP526Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value6_6 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP526Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value6_7 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP526Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP526Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 6 j)=sharedDiskP526Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP526Value6_0
  · exact sharedDiskP526Value6_1
  · exact sharedDiskP526Value6_2
  · exact sharedDiskP526Value6_3
  · exact sharedDiskP526Value6_4
  · exact sharedDiskP526Value6_5
  · exact sharedDiskP526Value6_6
  · exact sharedDiskP526Value6_7
private theorem sharedDiskP526Value7_0 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP526Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value7_1 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP526Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value7_2 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP526Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value7_3 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP526Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value7_4 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP526Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value7_5 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP526Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value7_6 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP526Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value7_7 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP526Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP526Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 7 j)=sharedDiskP526Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP526Value7_0
  · exact sharedDiskP526Value7_1
  · exact sharedDiskP526Value7_2
  · exact sharedDiskP526Value7_3
  · exact sharedDiskP526Value7_4
  · exact sharedDiskP526Value7_5
  · exact sharedDiskP526Value7_6
  · exact sharedDiskP526Value7_7
private theorem sharedDiskP526Value8_0 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP526Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value8_1 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP526Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value8_2 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP526Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value8_3 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP526Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value8_4 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP526Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value8_5 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP526Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value8_6 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP526Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP526Value8_7 : truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP526Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP526Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points 8 j)=sharedDiskP526Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP526Value8_0
  · exact sharedDiskP526Value8_1
  · exact sharedDiskP526Value8_2
  · exact sharedDiskP526Value8_3
  · exact sharedDiskP526Value8_4
  · exact sharedDiskP526Value8_5
  · exact sharedDiskP526Value8_6
  · exact sharedDiskP526Value8_7
theorem sharedDiskP526Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP526Params (sharedChord521Gauss8Points i j)=sharedDiskP526Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP526Values0_eq
  · exact sharedDiskP526Values1_eq
  · exact sharedDiskP526Values2_eq
  · exact sharedDiskP526Values3_eq
  · exact sharedDiskP526Values4_eq
  · exact sharedDiskP526Values5_eq
  · exact sharedDiskP526Values6_eq
  · exact sharedDiskP526Values7_eq
  · exact sharedDiskP526Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP526Box : HorizontalRectangle := ⟨(79/100),(317/400),(940334442440647/1649267441664000),(943555667912647/1649267441664000),(1019442392921126264162181132281727/2596148429267413814265248164610048),(3130567261539891137418853048608639/2596148429267413814265248164610048),(-1118838559863352136793220462835575/324518553658426726783156020576256),(-848436627255603530701372846405495/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP526Grid : CGrid := momentChordGrid sharedDiskP526Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP526Columns : containedInReported sharedDiskP526Grid.re sharedDiskP526Box.reLo sharedDiskP526Box.reHi=true ∧ containedInReported sharedDiskP526Grid.im sharedDiskP526Box.imLo sharedDiskP526Box.imHi=true := by
  rw [sharedDiskP526Grid,momentChordGrid_eq_tabulated sharedDiskP526Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP526Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP526Values_eq]
  decide +kernel
theorem sharedDiskP526Sound : sharedDiskP526Box.Sound := by
  intro t a tl tu al au
  change (((79/100):ℚ):ℝ)≤t at tl
  change t≤(((317/400):ℚ):ℝ) at tu
  change (((940334442440647/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((943555667912647/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP526Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(79/100))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((317/400):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(940334442440647/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((943555667912647/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP526Columns.1 sharedDiskP526Columns.2
def sharedDiskP526Rows : List SignRow := [positive_526.toSignRow]
theorem sharedDiskP526Rows_actual : ∀ r∈sharedDiskP526Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP526Rows.all (sharedDiskP526Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP526Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP523Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP524Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP525Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP526Rows_actual
