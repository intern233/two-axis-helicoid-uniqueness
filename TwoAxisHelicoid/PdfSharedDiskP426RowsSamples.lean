import TwoAxisHelicoid.PdfSharedChord426Gauss6

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP426Params : ChordParams := ⟨⟨(-345593024327194788380),(-184485526382058978665),true⟩,⟨4890977202058095631860303,5282028500099138606137905,true⟩,⟨14393066522661517287478,19977627682885095001446,true⟩,⟨15306780829461186851226,21152666515733736234608,true⟩,⟨29859796183080192785445,40873896097551540352028,true⟩,⟨1208234831097376280809650,1208556904859308391327148,true⟩,⟨(-5310200690561149554750878),(-4929586583359509071715779),true⟩,⟨⟨1174318179689008906542939,1243532110774639539400148,true⟩,⟨(-47),47,true⟩⟩⟩
theorem sharedDiskP426Params_ok : chordParams (Grid.ofRats (143/400) (77/200)) (Grid.ofRats (1105678609191/2199023255552) (3326240168225/6597069766656))=sharedDiskP426Params := by decide +kernel
def sharedDiskP426Values (i : Fin 14) (j : Fin 6) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-29989294749710370881269171),1485298440188096612514647,true⟩,⟨(-12931679814454829402767851),22434163528896094009093663,true⟩⟩
  | 0,1 => ⟨⟨(-26212786591017293161741095),1173958748725555740672788,true⟩,⟨(-12712969170702099154233277),17803828303397091786464748,true⟩⟩
  | 0,2 => ⟨⟨(-23717479444373457017729990),973152724032802280382238,true⟩,⟨(-12394509860455215694487217),14920923333943229941305108,true⟩⟩
  | 0,3 => ⟨⟨(-33506708508639424315748536),1585531170337116483168758,true⟩,⟨(-12517245499524302537284894),26821450006387230250978039,true⟩⟩
  | 0,4 => ⟨⟨(-35428254077954192590108008),1114961637579696067180694,true⟩,⟨(-11383520861355059874756031),28621379106981562937854766,true⟩⟩
  | 0,5 => ⟨⟨(-35979095707999505443110675),415558951171878088364039,true⟩,⟨(-10283355941626929140199860),28249383980431239437338094,true⟩⟩
  | 1,0 => ⟨⟨(-13597114776210319175649722),1758273556646889742482195,true⟩,⟨(-10411952363651450939009350),5001749781902725883530963,true⟩⟩
  | 1,1 => ⟨⟨(-11234240227286770207922757),2032306017482541369899731,true⟩,⟨(-9854858836669724907365436),3144814823028682149151858,true⟩⟩
  | 1,2 => ⟨⟨(-9922648542453808794754257),2210844760515874039403582,true⟩,⟨(-9535893577629844798595690),2315419232758826287653924,true⟩⟩
  | 1,3 => ⟨⟨(-16801665063425154260203286),1431804694399824043917214,true⟩,⟨(-11123139464194376061120674),7813854922291833730912505,true⟩⟩
  | 1,4 => ⟨⟨(-20138191935104892920607650),1086033624939244526536884,true⟩,⟨(-11791891345150041264505231),11073426037656887737861782,true⟩⟩
  | 1,5 => ⟨⟨(-22496966447616465500920381),885566533894240573098815,true⟩,⟨(-12205361458883669359818880),13569650746522120851212088,true⟩⟩
  | 2,0 => ⟨⟨(-2480798880949935198044776),4199509994906619314796050,true⟩,⟨(-7583058425079405894726589),(-564716325730258585699456),true⟩⟩
  | 2,1 => ⟨⟨(-997436118721334377072753),4949891674905892096654680,true⟩,⟨(-7156587673686952867202200),(-703878850022018358448467),true⟩⟩
  | 2,2 => ⟨⟨(-151695899656691650732872),5440033752353581685821230,true⟩,⟨(-6908829933709914712235901),(-753605076319544685887315),true⟩⟩
  | 2,3 => ⟨⟨(-4547995265475844746581905),3391536194111963270452421,true⟩,⟨(-8158432268470183153285053),(-197655541722026747840808),true⟩⟩
  | 2,4 => ⟨⟨(-6980838375715786239147579),2733829677080972576684220,true⟩,⟨(-8803775659699045675709503),664356120866367098975746,true⟩⟩
  | 2,5 => ⟨⟨(-9035407712414047609002185),2347818527506886813509084,true⟩,⟨(-9317556769041703438879760),1788866756826622768251859,true⟩⟩
  | 3,0 => ⟨⟨3750388329623119771955407,9840876569383953470815947,true⟩,⟨(-5497606200387056208414101),(-568383843135253768552755),true⟩⟩
  | 3,1 => ⟨⟨4749310758001868934082360,11113204611946450858039355,true⟩,⟨(-5103165900894190505163270),(-411577658783649465594965),true⟩⟩
  | 3,2 => ⟨⟨5338367077377412119840612,11868283236604698489535973,true⟩,⟨(-4864422196622238008038909),(-306041176566755515421561),true⟩⟩
  | 3,3 => ⟨⟨2486951272663387248241048,8272292915143387474276266,true⟩,⟨(-5979009354130932838073546),(-715891683213184559108768),true⟩⟩
  | 3,4 => ⟨⟨1218593374515748595340378,6788296050424145459581405,true⟩,⟨(-6442127094441684201816717),(-786876322981230232739192),true⟩⟩
  | 3,5 => ⟨⟨303747648032749880275888,5807639521048161607535166,true⟩,⟨(-6762297005527351710811342),(-775553269744866697205503),true⟩⟩
  | 4,0 => ⟨⟨9262452588363631533891220,16710900374641987366841720,true⟩,⟨(-3081198603902283554780504),619833206890061078951905,true⟩⟩
  | 4,1 => ⟨⟨10047304486654384192473008,17553514090559451048199628,true⟩,⟨(-2637299081460377426721077),848259201211730037726073,true⟩⟩
  | 4,2 => ⟨⟨10443271293541890520688884,17934813074949735772968778,true⟩,⟨(-2383414858745086733870743),971473170060399127785682,true⟩⟩
  | 4,3 => ⟨⟨8093845454578852218356195,15338469453981333721725146,true⟩,⟨(-3663311933614173131759439),305944036247176656415687,true⟩⟩
  | 4,4 => ⟨⟨6768552538781014860394351,13692700993726104864063745,true⟩,⟨(-4261874765593945771563609),(-17485018143347580710105),true⟩⟩
  | 4,5 => ⟨⟨5753609040746671696895222,12400386642479750612756924,true⟩,⟨(-4693080447364436515326431),(-226663129877414756447556),true⟩⟩
  | 5,0 => ⟨⟨11355491291725113622963355,17550292531427681873392938,true⟩,⟨(-849622814875323847925056),1463102255870816193696726,true⟩⟩
  | 5,1 => ⟨⟨10974901879302334257803230,16537218461783141347776013,true⟩,⟨(-571412248669993597948074),1455793874245925910523072,true⟩⟩
  | 5,2 => ⟨⟨10638843570220435904764776,15789679954891098613771970,true⟩,⟨(-431998935503666467393796),1426917746647032997159041,true⟩⟩
  | 5,3 => ⟨⟨11473014650955432282756755,18317152790883395060551457,true⟩,⟨(-1278591635298811865853641),1391507244733452466097052,true⟩⟩
  | 5,4 => ⟨⟨11166022252715130764943272,18451953430301401651160905,true⟩,⟨(-1792872655197056113898918),1225933434604009326256828,true⟩⟩
  | 5,5 => ⟨⟨10689650127474383727449537,18147325600587997167318665,true⟩,⟨(-2208140515633567880708110),1052313981766360723715075,true⟩⟩
  | 6,0 => ⟨⟨6574083209836433116883651,8640391564575401379984171,true⟩,⟨71241738987652671407987,857839865218253316173684,true⟩⟩
  | 6,1 => ⟨⟨5398428112081576097983618,6843878495252015279745824,true⟩,⟨92021811798589475718944,678923262504423650863047,true⟩⟩
  | 6,2 => ⟨⟨4742159851686882925332890,5878400947771402685898736,true⟩,⟨93030033295196464591468,579381040543996706969999,true⟩⟩
  | 6,3 => ⟨⟨8092590291627569182277553,11099908576683602561035936,true⟩,⟨(-3739930218092083542806),1086560402828469710038014,true⟩⟩
  | 6,4 => ⟨⟨9506371730815835864486746,13574723707630720021130245,true⟩,⟨(-165671003815074737801555),1288890722202522193595941,true⟩⟩
  | 6,5 => ⟨⟨10354871382572694597116089,15201896520562622450667160,true⟩,⟨(-344357676473688311253192),1396352039183886668891435,true⟩⟩
  | 7,0 => ⟨⟨2340695200449612719830950,3208216966070490474495738,true⟩,⟨308894749518223331713,314310372716390059345270,true⟩⟩
  | 7,1 => ⟨⟨1913333268368273488207536,2729035915815966953698134,true⟩,⟨(-31233384928686515036475),259531277767220068636058,true⟩⟩
  | 7,2 => ⟨⟨1707650076192228041403521,2503053017146872612870546,true⟩,⟨(-53942224753037420369000),230496439281165268600844,true⟩⟩
  | 7,3 => ⟨⟨3007190662268892242137365,3950792104947362535726030,true⟩,⟨33410050746099415967820,392397080922515956813991,true⟩⟩
  | 7,4 => ⟨⟨3796402449109233801866571,4812054789427121998038101,true⟩,⟨65123003908696611203956,477436023531902713808162,true⟩⟩
  | 7,5 => ⟨⟨4419674023231629835190706,5478449912284214777750941,true⟩,⟨86794997436375333395205,539977499842708818386741,true⟩⟩
  | 8,0 => ⟨⟨1410119465524724361040077,2241719789271582530526252,true⟩,⟨(-148569250841955409908795),172149276412983269853502,true⟩⟩
  | 8,1 => ⟨⟨1393085020938274763577406,2287220775111468308685156,true⟩,⟨(-209298351428243606256467),155044264247204779005557,true⟩⟩
  | 8,2 => ⟨⟨1408852477402924425079441,2370619964097411047759156,true⟩,⟨(-269432124387301977889116),142020479915573591643007,true⟩⟩
  | 8,3 => ⟨⟨1475887003185793025410789,2274478176740632809024493,true⟩,⟨(-105017913560617490327905),190771155247026237067289,true⟩⟩
  | 8,4 => ⟨⟨1568420008624946123694149,2358310808879371256702344,true⟩,⟨(-77778312833092502387021),208420483900989447616528,true⟩⟩
  | 8,5 => ⟨⟨1643580572881451137110141,2434987656363343656973214,true⟩,⟨(-63510228682733193591822),220718373392810516625917,true⟩⟩
  | 9,0 => ⟨⟨1605613775898358462182437,2964073805545127608087243,true⟩,⟨(-633546693119801021437616),76314057934398358453602,true⟩⟩
  | 9,1 => ⟨⟨1743846302428598824464856,3381059470484691884251650,true⟩,⟨(-917258912189309135151095),25300775385959656059290,true⟩⟩
  | 9,2 => ⟨⟨1863216559099301341608618,3773697416427423876960241,true⟩,⟨(-1215652754598966751021776),(-27180696034985724844703),true⟩⟩
  | 9,3 => ⟨⟨1502881186263129246676942,2666058262056659073450206,true⟩,⟨(-448878993934674830697230),108996335885451182672152,true⟩⟩
  | 9,4 => ⟨⟨1445699697580247132815870,2495203725067523494045169,true⟩,⟨(-346630538169973390665817),127330659609001642606591,true⟩⟩
  | 9,5 => ⟨⟨1421586632690664453820017,2416835157116996166911745,true⟩,⟨(-298823370301614500470767),136265781135640322470045,true⟩⟩
  | 10,0 => ⟨⟨2247360194202432679902356,5700571101010645269420338,true⟩,⟨(-3150467605074350939958564),(-352261047140301005137953),true⟩⟩
  | 10,1 => ⟨⟨2286476518932157867781233,6836325030565383022720092,true⟩,⟨(-4677997412701704780862440),(-590504933197625366307219),true⟩⟩
  | 10,2 => ⟨⟨2185090020253708710308584,7814797291794251270002550,true⟩,⟨(-6247641092719020926923914),(-815429103101132726957719),true⟩⟩
  | 10,3 => ⟨⟨2114583613309894867259485,4808049957572696500443461,true⟩,⟨(-2155114863784739544893691),(-187330873869229311207042),true⟩⟩
  | 10,4 => ⟨⟨1989196858072573226710826,4242548801670983098609069,true⟩,⟨(-1613566018476311154019648),(-95216867272826785189308),true⟩⟩
  | 10,5 => ⟨⟨1914669906394203217589783,3956795980274140517591693,true⟩,⟨(-1365599437683898405008059),(-52802109634167064351888),true⟩⟩
  | 11,0 => ⟨⟨101952677759306387647389,11501165649761026653095288,true⟩,⟨(-14999948669136131617673137),(-1739255721538841619314109),true⟩⟩
  | 11,1 => ⟨⟨(-3547708799106134251208977),12872972078897290103749862,true⟩,⟨(-20690879909910904427503902),(-2061108409259648627642479),true⟩⟩
  | 11,2 => ⟨⟨(-7438377673103669452466188),13630170955877045875267488,true⟩,⟨(-25485180870008691722980087),(-2194762634339388634360380),true⟩⟩
  | 11,3 => ⟨⟨1358987176322307560487938,10016621453694822137577104,true⟩,⟨(-10811641325949516023664711),(-1362445552789355230038688),true⟩⟩
  | 11,4 => ⟨⟨1904689796934358374269608,8878747513027991605247992,true⟩,⟨(-8254801338135301110240506),(-1074782573663155090529966),true⟩⟩
  | 11,5 => ⟨⟨2095371110947179510404606,8243540649538899053383255,true⟩,⟨(-7016371641103911509813282),(-918407350681099533141435),true⟩⟩
  | 12,0 => ⟨⟨(-28054131863779364904253575),13459906872236711717455158,true⟩,⟨(-40690019698592965324712260),(-1330601351894427375412086),true⟩⟩
  | 12,1 => ⟨⟨(-37832792361900128233992133),12107930717631348702632828,true⟩,⟨(-44608005793187114252158487),613623225604772178635648,true⟩⟩
  | 12,2 => ⟨⟨(-44970435611309413691836498),10762182430277167174730938,true⟩,⟨(-46162795515593421631246099),3147297466313247557886068,true⟩⟩
  | 12,3 => ⟨⟨(-18870047491199701845204685),14078728523090860389604449,true⟩,⟨(-35263757834895554006458471),(-2043533176652231886653439),true⟩⟩
  | 12,4 => ⟨⟨(-12583036483528051855336360),14054129378979147979928417,true⟩,⟨(-30428308223996343279420431),(-2196008961426999218115069),true⟩⟩
  | 12,5 => ⟨⟨(-9380717652788112407096715),13848722577411202646650425,true⟩,⟨(-27517309683930114216886273),(-2212834927635481782067429),true⟩⟩
  | 13,0 => ⟨⟨(-63860540143808650421411246),2264472867940547249027678,true⟩,⟨(-32298987145406957318719489),31454078896327231463082415,true⟩⟩
  | 13,1 => ⟨⟨(-56262069054007371056519169),2325117766340941700877642,true⟩,⟨(-21027686593016323065356369),37056429761603754457289393,true⟩⟩
  | 13,2 => ⟨⟨(-49048011359170369811283017),2289776737071259902351171,true⟩,⟨(-13888968965304247839570208),37831929047285709227474449,true⟩⟩
  | 13,3 => ⟨⟨(-62998407377440029311587977),4541096850716162250090684,true⟩,⟨(-42020244211475322776902652),20895502505698552245845744,true⟩⟩
  | 13,4 => ⟨⟨(-55365155523021827945987659),8040987806859743561788968,true⟩,⟨(-46115446320095456154714405),10953101998260470867851652,true⟩⟩
  | 13,5 => ⟨⟨(-48578602855425552821137126),9947585798242499225704804,true⟩,⟨(-46512443319701764998042457),5378939680078199130445831,true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP426Value0_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 0 (0:Fin 6))=sharedDiskP426Values 0 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value0_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 0 (1:Fin 6))=sharedDiskP426Values 0 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value0_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 0 (2:Fin 6))=sharedDiskP426Values 0 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value0_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 0 (3:Fin 6))=sharedDiskP426Values 0 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value0_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 0 (4:Fin 6))=sharedDiskP426Values 0 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value0_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 0 (5:Fin 6))=sharedDiskP426Values 0 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values0_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 0 j)=sharedDiskP426Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value0_0
  · exact sharedDiskP426Value0_1
  · exact sharedDiskP426Value0_2
  · exact sharedDiskP426Value0_3
  · exact sharedDiskP426Value0_4
  · exact sharedDiskP426Value0_5
private theorem sharedDiskP426Value1_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 1 (0:Fin 6))=sharedDiskP426Values 1 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value1_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 1 (1:Fin 6))=sharedDiskP426Values 1 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value1_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 1 (2:Fin 6))=sharedDiskP426Values 1 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value1_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 1 (3:Fin 6))=sharedDiskP426Values 1 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value1_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 1 (4:Fin 6))=sharedDiskP426Values 1 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value1_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 1 (5:Fin 6))=sharedDiskP426Values 1 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values1_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 1 j)=sharedDiskP426Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value1_0
  · exact sharedDiskP426Value1_1
  · exact sharedDiskP426Value1_2
  · exact sharedDiskP426Value1_3
  · exact sharedDiskP426Value1_4
  · exact sharedDiskP426Value1_5
private theorem sharedDiskP426Value2_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 2 (0:Fin 6))=sharedDiskP426Values 2 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value2_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 2 (1:Fin 6))=sharedDiskP426Values 2 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value2_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 2 (2:Fin 6))=sharedDiskP426Values 2 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value2_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 2 (3:Fin 6))=sharedDiskP426Values 2 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value2_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 2 (4:Fin 6))=sharedDiskP426Values 2 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value2_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 2 (5:Fin 6))=sharedDiskP426Values 2 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values2_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 2 j)=sharedDiskP426Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value2_0
  · exact sharedDiskP426Value2_1
  · exact sharedDiskP426Value2_2
  · exact sharedDiskP426Value2_3
  · exact sharedDiskP426Value2_4
  · exact sharedDiskP426Value2_5
private theorem sharedDiskP426Value3_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 3 (0:Fin 6))=sharedDiskP426Values 3 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value3_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 3 (1:Fin 6))=sharedDiskP426Values 3 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value3_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 3 (2:Fin 6))=sharedDiskP426Values 3 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value3_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 3 (3:Fin 6))=sharedDiskP426Values 3 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value3_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 3 (4:Fin 6))=sharedDiskP426Values 3 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value3_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 3 (5:Fin 6))=sharedDiskP426Values 3 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values3_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 3 j)=sharedDiskP426Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value3_0
  · exact sharedDiskP426Value3_1
  · exact sharedDiskP426Value3_2
  · exact sharedDiskP426Value3_3
  · exact sharedDiskP426Value3_4
  · exact sharedDiskP426Value3_5
private theorem sharedDiskP426Value4_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 4 (0:Fin 6))=sharedDiskP426Values 4 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value4_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 4 (1:Fin 6))=sharedDiskP426Values 4 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value4_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 4 (2:Fin 6))=sharedDiskP426Values 4 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value4_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 4 (3:Fin 6))=sharedDiskP426Values 4 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value4_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 4 (4:Fin 6))=sharedDiskP426Values 4 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value4_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 4 (5:Fin 6))=sharedDiskP426Values 4 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values4_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 4 j)=sharedDiskP426Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value4_0
  · exact sharedDiskP426Value4_1
  · exact sharedDiskP426Value4_2
  · exact sharedDiskP426Value4_3
  · exact sharedDiskP426Value4_4
  · exact sharedDiskP426Value4_5
private theorem sharedDiskP426Value5_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 5 (0:Fin 6))=sharedDiskP426Values 5 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value5_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 5 (1:Fin 6))=sharedDiskP426Values 5 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value5_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 5 (2:Fin 6))=sharedDiskP426Values 5 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value5_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 5 (3:Fin 6))=sharedDiskP426Values 5 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value5_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 5 (4:Fin 6))=sharedDiskP426Values 5 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value5_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 5 (5:Fin 6))=sharedDiskP426Values 5 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values5_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 5 j)=sharedDiskP426Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value5_0
  · exact sharedDiskP426Value5_1
  · exact sharedDiskP426Value5_2
  · exact sharedDiskP426Value5_3
  · exact sharedDiskP426Value5_4
  · exact sharedDiskP426Value5_5
private theorem sharedDiskP426Value6_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 6 (0:Fin 6))=sharedDiskP426Values 6 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value6_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 6 (1:Fin 6))=sharedDiskP426Values 6 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value6_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 6 (2:Fin 6))=sharedDiskP426Values 6 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value6_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 6 (3:Fin 6))=sharedDiskP426Values 6 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value6_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 6 (4:Fin 6))=sharedDiskP426Values 6 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value6_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 6 (5:Fin 6))=sharedDiskP426Values 6 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values6_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 6 j)=sharedDiskP426Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value6_0
  · exact sharedDiskP426Value6_1
  · exact sharedDiskP426Value6_2
  · exact sharedDiskP426Value6_3
  · exact sharedDiskP426Value6_4
  · exact sharedDiskP426Value6_5
private theorem sharedDiskP426Value7_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 7 (0:Fin 6))=sharedDiskP426Values 7 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value7_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 7 (1:Fin 6))=sharedDiskP426Values 7 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value7_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 7 (2:Fin 6))=sharedDiskP426Values 7 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value7_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 7 (3:Fin 6))=sharedDiskP426Values 7 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value7_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 7 (4:Fin 6))=sharedDiskP426Values 7 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value7_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 7 (5:Fin 6))=sharedDiskP426Values 7 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values7_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 7 j)=sharedDiskP426Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value7_0
  · exact sharedDiskP426Value7_1
  · exact sharedDiskP426Value7_2
  · exact sharedDiskP426Value7_3
  · exact sharedDiskP426Value7_4
  · exact sharedDiskP426Value7_5
private theorem sharedDiskP426Value8_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 8 (0:Fin 6))=sharedDiskP426Values 8 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value8_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 8 (1:Fin 6))=sharedDiskP426Values 8 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value8_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 8 (2:Fin 6))=sharedDiskP426Values 8 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value8_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 8 (3:Fin 6))=sharedDiskP426Values 8 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value8_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 8 (4:Fin 6))=sharedDiskP426Values 8 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value8_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 8 (5:Fin 6))=sharedDiskP426Values 8 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values8_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 8 j)=sharedDiskP426Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value8_0
  · exact sharedDiskP426Value8_1
  · exact sharedDiskP426Value8_2
  · exact sharedDiskP426Value8_3
  · exact sharedDiskP426Value8_4
  · exact sharedDiskP426Value8_5
private theorem sharedDiskP426Value9_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 9 (0:Fin 6))=sharedDiskP426Values 9 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value9_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 9 (1:Fin 6))=sharedDiskP426Values 9 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value9_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 9 (2:Fin 6))=sharedDiskP426Values 9 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value9_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 9 (3:Fin 6))=sharedDiskP426Values 9 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value9_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 9 (4:Fin 6))=sharedDiskP426Values 9 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value9_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 9 (5:Fin 6))=sharedDiskP426Values 9 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values9_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 9 j)=sharedDiskP426Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value9_0
  · exact sharedDiskP426Value9_1
  · exact sharedDiskP426Value9_2
  · exact sharedDiskP426Value9_3
  · exact sharedDiskP426Value9_4
  · exact sharedDiskP426Value9_5
private theorem sharedDiskP426Value10_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 10 (0:Fin 6))=sharedDiskP426Values 10 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value10_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 10 (1:Fin 6))=sharedDiskP426Values 10 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value10_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 10 (2:Fin 6))=sharedDiskP426Values 10 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value10_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 10 (3:Fin 6))=sharedDiskP426Values 10 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value10_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 10 (4:Fin 6))=sharedDiskP426Values 10 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value10_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 10 (5:Fin 6))=sharedDiskP426Values 10 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values10_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 10 j)=sharedDiskP426Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value10_0
  · exact sharedDiskP426Value10_1
  · exact sharedDiskP426Value10_2
  · exact sharedDiskP426Value10_3
  · exact sharedDiskP426Value10_4
  · exact sharedDiskP426Value10_5
private theorem sharedDiskP426Value11_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 11 (0:Fin 6))=sharedDiskP426Values 11 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value11_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 11 (1:Fin 6))=sharedDiskP426Values 11 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value11_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 11 (2:Fin 6))=sharedDiskP426Values 11 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value11_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 11 (3:Fin 6))=sharedDiskP426Values 11 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value11_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 11 (4:Fin 6))=sharedDiskP426Values 11 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value11_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 11 (5:Fin 6))=sharedDiskP426Values 11 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values11_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 11 j)=sharedDiskP426Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value11_0
  · exact sharedDiskP426Value11_1
  · exact sharedDiskP426Value11_2
  · exact sharedDiskP426Value11_3
  · exact sharedDiskP426Value11_4
  · exact sharedDiskP426Value11_5
private theorem sharedDiskP426Value12_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 12 (0:Fin 6))=sharedDiskP426Values 12 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value12_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 12 (1:Fin 6))=sharedDiskP426Values 12 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value12_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 12 (2:Fin 6))=sharedDiskP426Values 12 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value12_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 12 (3:Fin 6))=sharedDiskP426Values 12 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value12_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 12 (4:Fin 6))=sharedDiskP426Values 12 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value12_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 12 (5:Fin 6))=sharedDiskP426Values 12 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values12_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 12 j)=sharedDiskP426Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value12_0
  · exact sharedDiskP426Value12_1
  · exact sharedDiskP426Value12_2
  · exact sharedDiskP426Value12_3
  · exact sharedDiskP426Value12_4
  · exact sharedDiskP426Value12_5
private theorem sharedDiskP426Value13_0 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 13 (0:Fin 6))=sharedDiskP426Values 13 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value13_1 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 13 (1:Fin 6))=sharedDiskP426Values 13 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value13_2 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 13 (2:Fin 6))=sharedDiskP426Values 13 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value13_3 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 13 (3:Fin 6))=sharedDiskP426Values 13 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value13_4 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 13 (4:Fin 6))=sharedDiskP426Values 13 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP426Value13_5 : truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 13 (5:Fin 6))=sharedDiskP426Values 13 (5:Fin 6) := by decide +kernel
theorem sharedDiskP426Values13_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points 13 j)=sharedDiskP426Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP426Value13_0
  · exact sharedDiskP426Value13_1
  · exact sharedDiskP426Value13_2
  · exact sharedDiskP426Value13_3
  · exact sharedDiskP426Value13_4
  · exact sharedDiskP426Value13_5
theorem sharedDiskP426Values_eq : ∀ (i : Fin 14) (j : Fin 6), truncatedChordCell 1 sharedDiskP426Params (sharedChord426Gauss6Points i j)=sharedDiskP426Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP426Values0_eq
  · exact sharedDiskP426Values1_eq
  · exact sharedDiskP426Values2_eq
  · exact sharedDiskP426Values3_eq
  · exact sharedDiskP426Values4_eq
  · exact sharedDiskP426Values5_eq
  · exact sharedDiskP426Values6_eq
  · exact sharedDiskP426Values7_eq
  · exact sharedDiskP426Values8_eq
  · exact sharedDiskP426Values9_eq
  · exact sharedDiskP426Values10_eq
  · exact sharedDiskP426Values11_eq
  · exact sharedDiskP426Values12_eq
  · exact sharedDiskP426Values13_eq

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP426Values_eq
