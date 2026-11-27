import TwoAxisHelicoid.PdfSharedChord469Gauss8
import TwoAxisHelicoid.PdfSharedChord469Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP482Params : ChordParams := ⟨⟨(-6156447082510568838150),(-5887045039874982984299),true⟩,⟨3014249798312010424003718,3052366959187656230641603,true⟩,⟨72763400037145370964973,75274490758917349006489,true⟩,⟨96798231151105973703312,99898882296140414678077,true⟩,⟨167869760917054960540587,171705880293433018810565,true⟩,⟨1196675311086726712813858,1197208787375325067472074,true⟩,⟨(-3187408755280903418040542),(-3159215433649026129332623),true⟩,⟨⟨1179726154222244465280513,1214116809812390094980324,true⟩,⟨(-48),48,true⟩⟩⟩
theorem sharedDiskP482Params_ok : chordParams (Grid.ofRats (59/100) (119/200)) (Grid.ofRats (1156300018531/2199023255552) (1160594985827/2199023255552))=sharedDiskP482Params := by decide +kernel
def sharedDiskP482Values (i : Fin 15) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-6480344043314888200610540),(-3990531672874157161699314),true⟩,⟨(-1046368676038089448939768),1106350170126643787227832,true⟩⟩
  | 0,1 => ⟨⟨(-6131281166801333344916079),(-3709239955350861401620416),true⟩,⟨(-1081676368086536742397110),1035701168416851458102725,true⟩⟩
  | 0,2 => ⟨⟨(-5862224354591167517764336),(-3499110310490300988392212),true⟩,⟨(-1112456472164039198770558),968302957385426569461221,true⟩⟩
  | 0,3 => ⟨⟨(-5703294467702777566599167),(-3377753330390244186445086),true⟩,⟨(-1130947061679613672736736),923501227905974260140338,true⟩⟩
  | 0,4 => ⟨⟨(-6865545835022164282095570),(-4309755531412937366788972),true⟩,⟨(-1015103452519173571921011),1160853661560223040479937,true⟩⟩
  | 0,5 => ⟨⟨(-7233706910274546447090588),(-4626100144631176229307717),true⟩,⟨(-989528491943480394744743),1188613163333736119608704,true⟩⟩
  | 0,6 => ⟨⟨(-7530826755918319224313455),(-4891890001860676544956240),true⟩,⟨(-972481797787942995553186),1192941295974360698568877,true⟩⟩
  | 0,7 => ⟨⟨(-7712119494328441375944247),(-5058625400739551088125132),true⟩,⟨(-963860383603760325474702),1187446190123247747591388,true⟩⟩
  | 1,0 => ⟨⟨(-4604346422909332722153943),(-2590112104278293198339910),true⟩,⟨(-1262303988091865582475450),547253947142553390524288,true⟩⟩
  | 1,1 => ⟨⟨(-4326338205951805654634379),(-2403530969598524151605140),true⟩,⟨(-1295860733246969563068428),439755293740293453817305,true⟩⟩
  | 1,2 => ⟨⟨(-4115167022847500757288793),(-2264718828392003527040919),true⟩,⟨(-1321266839352338946771691),354108256049674483164769,true⟩⟩
  | 1,3 => ⟨⟨(-3991618062735011054310873),(-2184566886044786418266792),true⟩,⟨(-1336072385469154055926391),302588173172023168533974,true⟩⟩
  | 1,4 => ⟨⟨(-4916854578206053425677131),(-2805593368036924943063083),true⟩,⟨(-1224576656991935491402130),659936866828093090956650,true⟩⟩
  | 1,5 => ⟨⟨(-5221641490966982615557531),(-3022005835925132991657244),true⟩,⟨(-1187973590093808632630569),766885956946513658427098,true⟩⟩
  | 1,6 => ⟨⟨(-5472199035808749867891026),(-3204853787906172344652852),true⟩,⟨(-1158153154763290083473265),852116326262388216944744,true⟩⟩
  | 1,7 => ⟨⟨(-5627116196926153393099749),(-3320297576262666071403310),true⟩,⟨(-1139877392930067235076209),900768807801748357356192,true⟩⟩
  | 2,0 => ⟨⟨(-3157158841829105650414804),(-1659255467175164096585137),true⟩,⟨(-1433761917306325264394724),(-64313775159760751112921),true⟩⟩
  | 2,1 => ⟨⟨(-2951807963863364335821841),(-1531926957280593713260782),true⟩,⟨(-1456931262164170131537119),(-154519227603296048217900),true⟩⟩
  | 2,2 => ⟨⟨(-2798241994675665064100709),(-1436010768020225345535535),true⟩,⟨(-1474003992108084361895425),(-219557461268828069640917),true⟩⟩
  | 2,3 => ⟨⟨(-2708593626961023760676613),(-1380096455987626715002889),true⟩,⟨(-1483756710942391554727381),(-257455198820020197789409),true⟩⟩
  | 2,4 => ⟨⟨(-3391470423324164590472265),(-1804477583698828382364763),true⟩,⟨(-1406892416765496596160676),40812770637866643167247,true⟩⟩
  | 2,5 => ⟨⟨(-3622069081331194667283844),(-1948918094441722072253915),true⟩,⟨(-1379953369582263773805299),143292821001373490481376,true⟩⟩
  | 2,6 => ⟨⟨(-3813437626713487246395299),(-2070230702619053567379702),true⟩,⟨(-1357318202754817092484817),226669019628301547205227,true⟩⟩
  | 2,7 => ⟨⟨(-3932695560969133286600044),(-2146598634245851356886014),true⟩,⟨(-1343113579292594757743969),277683507727789366939127,true⟩⟩
  | 3,0 => ⟨⟨(-2103798784572032408560262),(-1001728483507993958748905),true⟩,⟨(-1543693184749546891654605),(-507221922267210052155974),true⟩⟩
  | 3,1 => ⟨⟨(-1953101127246045220017339),(-906375721948890417629361),true⟩,⟨(-1556435631186843147118869),(-566493709454841710221776),true⟩⟩
  | 3,2 => ⟨⟨(-1838712322007210969402929),(-833455533444352421179119),true⟩,⟨(-1565388841164353701931306),(-610282821149098379211555),true⟩⟩
  | 3,3 => ⟨⟨(-1771725430823902217940508),(-789985694685796334296665),true⟩,⟨(-1571166121973976825849236),(-635325351747028176262653),true⟩⟩
  | 3,4 => ⟨⟨(-2273860383959386747930116),(-1108627669421972024764620),true⟩,⟨(-1528095253125391805288479),(-438561022201991911499471),true⟩⟩
  | 3,5 => ⟨⟨(-2440900407952325658208264),(-1213121983307590204832121),true⟩,⟨(-1511723194846074740255568),(-369709443569924490039525),true⟩⟩
  | 3,6 => ⟨⟨(-2579472919919466174351383),(-1299588948241898479954147),true⟩,⟨(-1497481486433786825678447),(-311820904617822857848433),true⟩⟩
  | 3,7 => ⟨⟨(-2665876839511722747581420),(-1353462542463225839615286),true⟩,⟨(-1488341587433592470546949),(-275475573108997332456803),true⟩⟩
  | 4,0 => ⟨⟨(-310256080930056758524057),243568447980728796884892,true⟩,⟨(-1588884834852033638900250),(-1004468075158273700109739),true⟩⟩
  | 4,1 => ⟨⟨(-7075320896939982328761),490182667350112307976234,true⟩,⟨(-1552902544292958655343928),(-1019467381876889703567254),true⟩⟩
  | 4,2 => ⟨⟨208982625680466515453288,677038038824913758546600,true⟩,⟨(-1515905403747708596053450),(-1013359924498133078637979),true⟩⟩
  | 4,3 => ⟨⟨328910869943543451281089,784241565023580480793965,true⟩,⟨(-1491986396297204476632485),(-1004650856892559759134795),true⟩⟩
  | 4,4 => ⟨⟨(-678996240944484068609734),(-37650870712975929933296),true⟩,⟨(-1610367016301722530113976),(-952712483754484196654560),true⟩⟩
  | 4,5 => ⟨⟨(-1077681695473730580716406),(-324407813295786230326879),true⟩,⟨(-1610601743369086178029202),(-862459375574791558444083),true⟩⟩
  | 4,6 => ⟨⟨(-1445248262256036428682968),(-574768906372497000848247),true⟩,⟨(-1594951090369709582585716),(-750365529271060060597501),true⟩⟩
  | 4,7 => ⟨⟨(-1692415419904603075635279),(-738238098916996076670112),true⟩,⟨(-1577644784121202617084073),(-664392495092777717407212),true⟩⟩
  | 5,0 => ⟨⟨1589497092682792738303003,1981410742624875901715663,true⟩,⟨(-1057553354317303960878254),(-687065272401740915624172),true⟩⟩
  | 5,1 => ⟨⟨1835019629217925783479333,2217018791525284619728396,true⟩,⟨(-932769920449247253575488),(-583261713920762281776093),true⟩⟩
  | 5,2 => ⟨⟨2002695432346897905186229,2377277377886895236371482,true⟩,⟨(-839814150576340749166962),(-505145064609810644991504),true⟩⟩
  | 5,3 => ⟨⟨2093477956388044436974232,2463658443819394919643993,true⟩,⟨(-786675943980727407467353),(-460345304864550417249418),true⟩⟩
  | 5,4 => ⟨⟨1278161168988748834942804,1682387503665960403602758,true⟩,⟨(-1197257407995704730892926),(-800392761145905065571959),true⟩⟩
  | 5,5 => ⟨⟨935542093000948015209059,1354770078032963825602291,true⟩,⟨(-1326987565371597463584847),(-900030999256743392358052),true⟩⟩
  | 5,6 => ⟨⟨621430042831202823333412,1057361048931973985589233,true⟩,⟨(-1423017853469587417491545),(-966282353813824512494110),true⟩⟩
  | 5,7 => ⟨⟨410332405278990039872847,859823127507276593116695,true⟩,⟨(-1474800845135740496515437),(-996312067499556624870077),true⟩⟩
  | 6,0 => ⟨⟨2796391499016525256203864,3102659668512114261000073,true⟩,⟨(-275647786338935824621972),(-37375215875112245968258),true⟩⟩
  | 6,1 => ⟨⟨2863665293259837937684435,3153724230028363447392053,true⟩,⟨(-210798643236952706741535),11523876726252393761050,true⟩⟩
  | 6,2 => ⟨⟨2898160126254817457212737,3176887140451305748977787,true⟩,⟨(-179733522511251884067936),32602588016905881519682,true⟩⟩
  | 6,3 => ⟨⟨2914209391537344339477147,3186927203342591706244721,true⟩,⟨(-169139208292505394400703),38238709669705282342748,true⟩⟩
  | 6,4 => ⟨⟨2677600113014007941525892,3002838725122117605798598,true⟩,⟨(-380866677709043309354089),(-121338819372845692306371),true⟩⟩
  | 6,5 => ⟨⟨2503060884847528061777787,2846681109691906948473424,true⟩,⟨(-517007383855007854144056),(-233603123367873099637085),true⟩⟩
  | 6,6 => ⟨⟨2305581024965413833376550,2663806101814839664712316,true⟩,⟨(-653887595046049074461603),(-348360848635292094343006),true⟩⟩
  | 6,7 => ⟨⟨2154988298492320919486819,2521977566229187388576516,true⟩,⟨(-749469820690987687652312),(-428954040834861606798970),true⟩⟩
  | 7,0 => ⟨⟨3042076849358016850335333,3363511570603089256682587,true⟩,⟨(-320071281206448413702423),(-74966496785925039841886),true⟩⟩
  | 7,1 => ⟨⟨3141189479663120459699694,3497455253953798472206280,true⟩,⟨(-463250485152733858697041),(-185840777836268235400914),true⟩⟩
  | 7,2 => ⟨⟨3260818965322297446849240,3658129776678058261354963,true⟩,⟨(-640269658423531833977408),(-323175161537315010745680),true⟩⟩
  | 7,3 => ⟨⟨3355451557313562552313710,3786158394781491140535882,true⟩,⟨(-788978109571441637078841),(-438680368126738199548721),true⟩⟩
  | 7,4 => ⟨⟨2980257822052843049831854,3277599062952716600818948,true⟩,⟨(-228731781762841293350812),(-4633300071411544411437),true⟩⟩
  | 7,5 => ⟨⟨2947745065656115684477219,3230627189838120694340949,true⟩,⟨(-182873452993405432019045),30123245762404290336235,true⟩⟩
  | 7,6 => ⟨⟨2930202283746562050426583,3205491929690670112871901,true⟩,⟨(-167736028173700584296437),40387426680138530497115,true⟩⟩
  | 7,7 => ⟨⟨2920260541305088514375165,3192282651633468079813080,true⟩,⟨(-166792947191134432369284),39748234763552696943598,true⟩⟩
  | 8,0 => ⟨⟨3896302218239452841616826,4579588067397570842256603,true⟩,⟨(-2002057316298112220417501),(-1382916565279671646802045),true⟩⟩
  | 8,1 => ⟨⟨4050461098384873162844636,4868901275155329608955083,true⟩,⟨(-2692273605526417502234528),(-1919639997876955032386603),true⟩⟩
  | 8,2 => ⟨⟨4118311503628683949684707,5082710206213550084320191,true⟩,⟨(-3455943186446595124998956),(-2511584787816369764486644),true⟩⟩
  | 8,3 => ⟨⟨4104997166677408292717240,5179678003875572531048197,true⟩,⟨(-4041126670564012724642691),(-2963353346485977978415670),true⟩⟩
  | 8,4 => ⟨⟨3715647826681046191507932,4295684520953814415234411,true⟩,⟨(-1490967814150153364271791),(-984945434529915058620485),true⟩⟩
  | 8,5 => ⟨⟨3560659366065657839691185,4070545415910861460558906,true⟩,⟨(-1154645846941343596411535),(-723087066655259611723628),true⟩⟩
  | 8,6 => ⟨⟨3452864032581868008427764,3919715209274500707715271,true⟩,⟨(-953820295097430764630359),(-566833360209070890923351),true⟩⟩
  | 8,7 => ⟨⟨3394653860260031001650619,3839648582391487163117935,true⟩,⟨(-853688309870502262056792),(-488974722992412928677176),true⟩⟩
  | 9,0 => ⟨⟨3806499908711096362350433,5174776288213783521103849,true⟩,⟨(-5614802502976232229102960),(-4168088115858764363695979),true⟩⟩
  | 9,1 => ⟨⟨3634418675236421661483873,5094100380605015920773086,true⟩,⟨(-6105418872571893878549756),(-4540031068625847835236847),true⟩⟩
  | 9,2 => ⟨⟨3457759113749324896364225,4994857012013070494900841,true⟩,⟨(-6519923286891708237705114),(-4852667164311972156712092),true⟩⟩
  | 9,3 => ⟨⟨3331244243618395884900597,4917129981126148696005762,true⟩,⟨(-6780371312364403841732044),(-5048284715593484681128150),true⟩⟩
  | 9,4 => ⟨⟨3939010512472626946365413,5217033362947604697387422,true⟩,⟨(-5129971560558148124910380),(-3798700087946418844403787),true⟩⟩
  | 9,5 => ⟨⟨4023475884892380517378911,5224356442767080251889887,true⟩,⟨(-4715963025644074041087016),(-3481961362037893476335869),true⟩⟩
  | 9,6 => ⟨⟨4068706789858424206696554,5213023304176812184820043,true⟩,⟨(-4412993958015217925299946),(-3249469560526169093808862),true⟩⟩
  | 9,7 => ⟨⟨4088190667204753517480003,5200234491781713129747281,true⟩,⟨(-4240472319732912972908472),(-3116830396973406181585196),true⟩⟩
  | 10,0 => ⟨⟨1754781280228568017142183,3742452754275931139627856,true⟩,⟨(-8876089079953619133873697),(-6591399992120789979619587),true⟩⟩
  | 10,1 => ⟨⟨1055079472551991880908251,3165545402512255685920469,true⟩,⟨(-9450410399156535081364751),(-6996678313687728490629260),true⟩⟩
  | 10,2 => ⟨⟨368143356630885219826845,2612353591920063821197374,true⟩,⟨(-9887701137237954322252511),(-7282272256854170211031724),true⟩⟩
  | 10,3 => ⟨⟨(-91263580982421268516917),2235221385189633399438920,true⟩,⟨(-10127465737337478852545441),(-7432227001532142312752165),true⟩⟩
  | 10,4 => ⟨⟨2363005248637019643527451,4225623908318442530262977,true⟩,⟨(-8237115689370573947704228),(-6128055104143427273216653),true⟩⟩
  | 10,5 => ⟨⟨2818372351846273000862124,4566759225307878915786331,true⟩,⟨(-7641165800760785600750231),(-5689629755373671959697728),true⟩⟩
  | 10,6 => ⟨⟨3112127791643016132947495,4773195898680868806394872,true⟩,⟨(-7180116147234521897068969),(-5347171770997983787930225),true⟩⟩
  | 10,7 => ⟨⟨3263917521253356682281131,4874024104211670738902139,true⟩,⟨(-6909388443303448007725705),(-5144935581234972757041011),true⟩⟩
  | 11,0 => ⟨⟨(-2175105838323099759768393),553053798514237483941364,true⟩,⟨(-10772158816971432365826133),(-7728150869981590493116974),true⟩⟩
  | 11,1 => ⟨⟨(-2809207899202826421041951),38689871473838890141814,true⟩,⟨(-10838959562322824352598834),(-7709959208509062724064892),true⟩⟩
  | 11,2 => ⟨⟨(-3326647867271293451977485),(-382726976241299817298990),true⟩,⟨(-10849571985895354797163983),(-7660815837431085241586448),true⟩⟩
  | 11,3 => ⟨⟨(-3643673160515260844750120),(-643008024076582589700400),true⟩,⟨(-10836172077522110231962644),(-7615197738984023139384562),true⟩⟩
  | 11,4 => ⟨⟨(-1524397946293440331321715),1073741458572751668651817,true⟩,⟨(-10642285798289471910442645),(-7698760187170988989420160),true⟩⟩
  | 11,5 => ⟨⟨(-949514243583917620038293),1527553995632749680726038,true⟩,⟨(-10474817634409527962235300),(-7631352677116945225597131),true⟩⟩
  | 11,6 => ⟨⟨(-517801934097317583232756),1882651705769354467027358,true⟩,⟨(-10315214916748861366375030),(-7544541537458530117876706),true⟩⟩
  | 11,7 => ⟨⟨(-267977756222217342356858),2089699963885061630015668,true⟩,⟨(-10208988032588673742268803),(-7481668091546802896874964),true⟩⟩
  | 12,0 => ⟨⟨(-6018493253701274085719843),(-2657292563409381677622725),true⟩,⟨(-10189484200000319255173066),(-6850490414188612636218261),true⟩⟩
  | 12,1 => ⟨⟨(-6640397056125436199095213),(-3209556456049910354831833),true⟩,⟨(-9818796076361245923525122),(-6495379186299162677782363),true⟩⟩
  | 12,2 => ⟨⟨(-7103607218348654184481652),(-3631120255574680182555602),true⟩,⟨(-9463835501667602920747171),(-6170593020001466998852507),true⟩⟩
  | 12,3 => ⟨⟨(-7367241061268562938164859),(-3876101455661336970392765),true⟩,⟨(-9223862755846725430072341),(-5956796846435991722270708),true⟩⟩
  | 12,4 => ⟨⟨(-5319554528734179975262805),(-2050975687922445766263620),true⟩,⟨(-10491764823874711477842397),(-7161903670896820192392812),true⟩⟩
  | 12,5 => ⟨⟨(-4651559605424379730509561),(-1482835889618407433622695),true⟩,⟨(-10687589977676666024545885),(-7387870023691991711605177),true⟩⟩
  | 12,6 => ⟨⟨(-4118915585640343641613382),(-1036585467307950985908066),true⟩,⟨(-10786796011338018881957085),(-7524045188269698599995230),true⟩⟩
  | 12,7 => ⟨⟨(-3798514100147369213833384),(-770785695236521396593530),true⟩,⟨(-10824001246870615302580571),(-7588540832849924477575838),true⟩⟩
  | 13,0 => ⟨⟨(-8804508199983029608744832),(-5357290034918160900805639),true⟩,⟨(-6887468969630861805914656),(-4010122858682352638431344),true⟩⟩
  | 13,1 => ⟨⟨(-9002986700430566912630708),(-5624829639357370636154021),true⟩,⟨(-6103445408300611750319857),(-3383129993981060760036124),true⟩⟩
  | 13,2 => ⟨⟨(-9089749037232972640855109),(-5782458933608670926701004),true⟩,⟨(-5459906968806417653473678),(-2872491546956993735177519),true⟩⟩
  | 13,3 => ⟨⟨(-9108518784938160236519450),(-5853535514615515652225102),true⟩,⟨(-5066026029142805589486019),(-2565194994570364136787828),true⟩⟩
  | 13,4 => ⟨⟨(-8488268125683640278389753),(-4991293119036853790220780),true⟩,⟨(-7676684818439534501667175),(-4647174645218222269872035),true⟩⟩
  | 13,5 => ⟨⟨(-8098879726476555215118663),(-4584611994348143759137059),true⟩,⟨(-8349802202595180676973623),(-5205129071528852747103748),true⟩⟩
  | 13,6 => ⟨⟨(-7732878016725209951020928),(-4223814146202714309450990),true⟩,⟨(-8832715576777718006265451),(-5615869187171891284156055),true⟩⟩
  | 13,7 => ⟨⟨(-7490314277843756404698355),(-3991996333231239488729981),true⟩,⟨(-9100541738678344460843415),(-5848386747732687230412763),true⟩⟩
  | 14,0 => ⟨⟨(-8486757398564496605276757),(-5818228016111061687041489),true⟩,⟨(-2202368195578914557390152),(-447894058038276569096442),true⟩⟩
  | 14,1 => ⟨⟨(-8107179149426929572803248),(-5647180350360079354954023),true⟩,⟨(-1492015754081828198806995),55842877943669636574359,true⟩⟩
  | 14,2 => ⟨⟨(-7758935465008365908811503),(-5471742896764282919246419),true⟩,⟨(-974774928576547176464975),444398892134149826146973,true⟩⟩
  | 14,3 => ⟨⟨(-7532001706388022065604988),(-5350380260691157482419661),true⟩,⟨(-684401215473100163860615),666294910920054788745019,true⟩⟩
  | 14,4 => ⟨⟨(-8804920616388907597952466),(-5929413010202541678395179),true⟩,⟨(-3022724242016209594492736),(-1032871080725666760272755),true⟩⟩
  | 14,5 => ⟨⟨(-9004615637772488746399076),(-5957829215015519668867494),true⟩,⟨(-3826398406620746255263852),(-1623166941448075021184877),true⟩⟩
  | 14,6 => ⟨⟨(-9089838579030022528273327),(-5925286366209176312573147),true⟩,⟨(-4478372941014875265837532),(-2113900573769968257133743),true⟩⟩
  | 14,7 => ⟨⟨(-9108510552148979684483228),(-5881434117428409911325059),true⟩,⟨(-4874095351196922982270907),(-2416861079391490674879616),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP482Value0_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 0 (0:Fin 8))=sharedDiskP482Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value0_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 0 (1:Fin 8))=sharedDiskP482Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value0_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 0 (2:Fin 8))=sharedDiskP482Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value0_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 0 (3:Fin 8))=sharedDiskP482Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value0_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 0 (4:Fin 8))=sharedDiskP482Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value0_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 0 (5:Fin 8))=sharedDiskP482Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value0_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 0 (6:Fin 8))=sharedDiskP482Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value0_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 0 (7:Fin 8))=sharedDiskP482Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 0 j)=sharedDiskP482Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value0_0
  · exact sharedDiskP482Value0_1
  · exact sharedDiskP482Value0_2
  · exact sharedDiskP482Value0_3
  · exact sharedDiskP482Value0_4
  · exact sharedDiskP482Value0_5
  · exact sharedDiskP482Value0_6
  · exact sharedDiskP482Value0_7
private theorem sharedDiskP482Value1_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 1 (0:Fin 8))=sharedDiskP482Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value1_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 1 (1:Fin 8))=sharedDiskP482Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value1_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 1 (2:Fin 8))=sharedDiskP482Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value1_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 1 (3:Fin 8))=sharedDiskP482Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value1_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 1 (4:Fin 8))=sharedDiskP482Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value1_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 1 (5:Fin 8))=sharedDiskP482Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value1_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 1 (6:Fin 8))=sharedDiskP482Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value1_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 1 (7:Fin 8))=sharedDiskP482Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 1 j)=sharedDiskP482Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value1_0
  · exact sharedDiskP482Value1_1
  · exact sharedDiskP482Value1_2
  · exact sharedDiskP482Value1_3
  · exact sharedDiskP482Value1_4
  · exact sharedDiskP482Value1_5
  · exact sharedDiskP482Value1_6
  · exact sharedDiskP482Value1_7
private theorem sharedDiskP482Value2_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 2 (0:Fin 8))=sharedDiskP482Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value2_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 2 (1:Fin 8))=sharedDiskP482Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value2_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 2 (2:Fin 8))=sharedDiskP482Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value2_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 2 (3:Fin 8))=sharedDiskP482Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value2_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 2 (4:Fin 8))=sharedDiskP482Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value2_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 2 (5:Fin 8))=sharedDiskP482Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value2_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 2 (6:Fin 8))=sharedDiskP482Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value2_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 2 (7:Fin 8))=sharedDiskP482Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 2 j)=sharedDiskP482Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value2_0
  · exact sharedDiskP482Value2_1
  · exact sharedDiskP482Value2_2
  · exact sharedDiskP482Value2_3
  · exact sharedDiskP482Value2_4
  · exact sharedDiskP482Value2_5
  · exact sharedDiskP482Value2_6
  · exact sharedDiskP482Value2_7
private theorem sharedDiskP482Value3_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 3 (0:Fin 8))=sharedDiskP482Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value3_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 3 (1:Fin 8))=sharedDiskP482Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value3_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 3 (2:Fin 8))=sharedDiskP482Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value3_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 3 (3:Fin 8))=sharedDiskP482Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value3_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 3 (4:Fin 8))=sharedDiskP482Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value3_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 3 (5:Fin 8))=sharedDiskP482Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value3_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 3 (6:Fin 8))=sharedDiskP482Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value3_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 3 (7:Fin 8))=sharedDiskP482Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 3 j)=sharedDiskP482Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value3_0
  · exact sharedDiskP482Value3_1
  · exact sharedDiskP482Value3_2
  · exact sharedDiskP482Value3_3
  · exact sharedDiskP482Value3_4
  · exact sharedDiskP482Value3_5
  · exact sharedDiskP482Value3_6
  · exact sharedDiskP482Value3_7
private theorem sharedDiskP482Value4_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 4 (0:Fin 8))=sharedDiskP482Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value4_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 4 (1:Fin 8))=sharedDiskP482Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value4_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 4 (2:Fin 8))=sharedDiskP482Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value4_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 4 (3:Fin 8))=sharedDiskP482Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value4_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 4 (4:Fin 8))=sharedDiskP482Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value4_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 4 (5:Fin 8))=sharedDiskP482Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value4_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 4 (6:Fin 8))=sharedDiskP482Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value4_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 4 (7:Fin 8))=sharedDiskP482Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 4 j)=sharedDiskP482Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value4_0
  · exact sharedDiskP482Value4_1
  · exact sharedDiskP482Value4_2
  · exact sharedDiskP482Value4_3
  · exact sharedDiskP482Value4_4
  · exact sharedDiskP482Value4_5
  · exact sharedDiskP482Value4_6
  · exact sharedDiskP482Value4_7
private theorem sharedDiskP482Value5_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 5 (0:Fin 8))=sharedDiskP482Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value5_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 5 (1:Fin 8))=sharedDiskP482Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value5_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 5 (2:Fin 8))=sharedDiskP482Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value5_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 5 (3:Fin 8))=sharedDiskP482Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value5_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 5 (4:Fin 8))=sharedDiskP482Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value5_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 5 (5:Fin 8))=sharedDiskP482Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value5_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 5 (6:Fin 8))=sharedDiskP482Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value5_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 5 (7:Fin 8))=sharedDiskP482Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 5 j)=sharedDiskP482Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value5_0
  · exact sharedDiskP482Value5_1
  · exact sharedDiskP482Value5_2
  · exact sharedDiskP482Value5_3
  · exact sharedDiskP482Value5_4
  · exact sharedDiskP482Value5_5
  · exact sharedDiskP482Value5_6
  · exact sharedDiskP482Value5_7
private theorem sharedDiskP482Value6_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 6 (0:Fin 8))=sharedDiskP482Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value6_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 6 (1:Fin 8))=sharedDiskP482Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value6_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 6 (2:Fin 8))=sharedDiskP482Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value6_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 6 (3:Fin 8))=sharedDiskP482Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value6_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 6 (4:Fin 8))=sharedDiskP482Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value6_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 6 (5:Fin 8))=sharedDiskP482Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value6_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 6 (6:Fin 8))=sharedDiskP482Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value6_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 6 (7:Fin 8))=sharedDiskP482Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 6 j)=sharedDiskP482Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value6_0
  · exact sharedDiskP482Value6_1
  · exact sharedDiskP482Value6_2
  · exact sharedDiskP482Value6_3
  · exact sharedDiskP482Value6_4
  · exact sharedDiskP482Value6_5
  · exact sharedDiskP482Value6_6
  · exact sharedDiskP482Value6_7
private theorem sharedDiskP482Value7_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 7 (0:Fin 8))=sharedDiskP482Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value7_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 7 (1:Fin 8))=sharedDiskP482Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value7_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 7 (2:Fin 8))=sharedDiskP482Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value7_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 7 (3:Fin 8))=sharedDiskP482Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value7_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 7 (4:Fin 8))=sharedDiskP482Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value7_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 7 (5:Fin 8))=sharedDiskP482Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value7_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 7 (6:Fin 8))=sharedDiskP482Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value7_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 7 (7:Fin 8))=sharedDiskP482Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 7 j)=sharedDiskP482Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value7_0
  · exact sharedDiskP482Value7_1
  · exact sharedDiskP482Value7_2
  · exact sharedDiskP482Value7_3
  · exact sharedDiskP482Value7_4
  · exact sharedDiskP482Value7_5
  · exact sharedDiskP482Value7_6
  · exact sharedDiskP482Value7_7
private theorem sharedDiskP482Value8_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 8 (0:Fin 8))=sharedDiskP482Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value8_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 8 (1:Fin 8))=sharedDiskP482Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value8_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 8 (2:Fin 8))=sharedDiskP482Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value8_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 8 (3:Fin 8))=sharedDiskP482Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value8_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 8 (4:Fin 8))=sharedDiskP482Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value8_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 8 (5:Fin 8))=sharedDiskP482Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value8_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 8 (6:Fin 8))=sharedDiskP482Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value8_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 8 (7:Fin 8))=sharedDiskP482Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 8 j)=sharedDiskP482Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value8_0
  · exact sharedDiskP482Value8_1
  · exact sharedDiskP482Value8_2
  · exact sharedDiskP482Value8_3
  · exact sharedDiskP482Value8_4
  · exact sharedDiskP482Value8_5
  · exact sharedDiskP482Value8_6
  · exact sharedDiskP482Value8_7
private theorem sharedDiskP482Value9_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 9 (0:Fin 8))=sharedDiskP482Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value9_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 9 (1:Fin 8))=sharedDiskP482Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value9_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 9 (2:Fin 8))=sharedDiskP482Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value9_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 9 (3:Fin 8))=sharedDiskP482Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value9_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 9 (4:Fin 8))=sharedDiskP482Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value9_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 9 (5:Fin 8))=sharedDiskP482Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value9_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 9 (6:Fin 8))=sharedDiskP482Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value9_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 9 (7:Fin 8))=sharedDiskP482Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 9 j)=sharedDiskP482Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value9_0
  · exact sharedDiskP482Value9_1
  · exact sharedDiskP482Value9_2
  · exact sharedDiskP482Value9_3
  · exact sharedDiskP482Value9_4
  · exact sharedDiskP482Value9_5
  · exact sharedDiskP482Value9_6
  · exact sharedDiskP482Value9_7
private theorem sharedDiskP482Value10_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 10 (0:Fin 8))=sharedDiskP482Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value10_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 10 (1:Fin 8))=sharedDiskP482Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value10_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 10 (2:Fin 8))=sharedDiskP482Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value10_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 10 (3:Fin 8))=sharedDiskP482Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value10_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 10 (4:Fin 8))=sharedDiskP482Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value10_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 10 (5:Fin 8))=sharedDiskP482Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value10_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 10 (6:Fin 8))=sharedDiskP482Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value10_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 10 (7:Fin 8))=sharedDiskP482Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 10 j)=sharedDiskP482Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value10_0
  · exact sharedDiskP482Value10_1
  · exact sharedDiskP482Value10_2
  · exact sharedDiskP482Value10_3
  · exact sharedDiskP482Value10_4
  · exact sharedDiskP482Value10_5
  · exact sharedDiskP482Value10_6
  · exact sharedDiskP482Value10_7
private theorem sharedDiskP482Value11_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 11 (0:Fin 8))=sharedDiskP482Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value11_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 11 (1:Fin 8))=sharedDiskP482Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value11_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 11 (2:Fin 8))=sharedDiskP482Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value11_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 11 (3:Fin 8))=sharedDiskP482Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value11_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 11 (4:Fin 8))=sharedDiskP482Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value11_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 11 (5:Fin 8))=sharedDiskP482Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value11_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 11 (6:Fin 8))=sharedDiskP482Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value11_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 11 (7:Fin 8))=sharedDiskP482Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 11 j)=sharedDiskP482Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value11_0
  · exact sharedDiskP482Value11_1
  · exact sharedDiskP482Value11_2
  · exact sharedDiskP482Value11_3
  · exact sharedDiskP482Value11_4
  · exact sharedDiskP482Value11_5
  · exact sharedDiskP482Value11_6
  · exact sharedDiskP482Value11_7
private theorem sharedDiskP482Value12_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 12 (0:Fin 8))=sharedDiskP482Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value12_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 12 (1:Fin 8))=sharedDiskP482Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value12_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 12 (2:Fin 8))=sharedDiskP482Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value12_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 12 (3:Fin 8))=sharedDiskP482Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value12_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 12 (4:Fin 8))=sharedDiskP482Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value12_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 12 (5:Fin 8))=sharedDiskP482Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value12_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 12 (6:Fin 8))=sharedDiskP482Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value12_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 12 (7:Fin 8))=sharedDiskP482Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 12 j)=sharedDiskP482Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value12_0
  · exact sharedDiskP482Value12_1
  · exact sharedDiskP482Value12_2
  · exact sharedDiskP482Value12_3
  · exact sharedDiskP482Value12_4
  · exact sharedDiskP482Value12_5
  · exact sharedDiskP482Value12_6
  · exact sharedDiskP482Value12_7
private theorem sharedDiskP482Value13_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 13 (0:Fin 8))=sharedDiskP482Values 13 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value13_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 13 (1:Fin 8))=sharedDiskP482Values 13 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value13_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 13 (2:Fin 8))=sharedDiskP482Values 13 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value13_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 13 (3:Fin 8))=sharedDiskP482Values 13 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value13_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 13 (4:Fin 8))=sharedDiskP482Values 13 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value13_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 13 (5:Fin 8))=sharedDiskP482Values 13 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value13_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 13 (6:Fin 8))=sharedDiskP482Values 13 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value13_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 13 (7:Fin 8))=sharedDiskP482Values 13 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values13_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 13 j)=sharedDiskP482Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value13_0
  · exact sharedDiskP482Value13_1
  · exact sharedDiskP482Value13_2
  · exact sharedDiskP482Value13_3
  · exact sharedDiskP482Value13_4
  · exact sharedDiskP482Value13_5
  · exact sharedDiskP482Value13_6
  · exact sharedDiskP482Value13_7
private theorem sharedDiskP482Value14_0 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 14 (0:Fin 8))=sharedDiskP482Values 14 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value14_1 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 14 (1:Fin 8))=sharedDiskP482Values 14 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value14_2 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 14 (2:Fin 8))=sharedDiskP482Values 14 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value14_3 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 14 (3:Fin 8))=sharedDiskP482Values 14 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value14_4 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 14 (4:Fin 8))=sharedDiskP482Values 14 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value14_5 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 14 (5:Fin 8))=sharedDiskP482Values 14 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value14_6 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 14 (6:Fin 8))=sharedDiskP482Values 14 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP482Value14_7 : truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 14 (7:Fin 8))=sharedDiskP482Values 14 (7:Fin 8) := by decide +kernel
theorem sharedDiskP482Values14_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points 14 j)=sharedDiskP482Values 14 j := by
  intro j
  fin_cases j
  · exact sharedDiskP482Value14_0
  · exact sharedDiskP482Value14_1
  · exact sharedDiskP482Value14_2
  · exact sharedDiskP482Value14_3
  · exact sharedDiskP482Value14_4
  · exact sharedDiskP482Value14_5
  · exact sharedDiskP482Value14_6
  · exact sharedDiskP482Value14_7
theorem sharedDiskP482Values_eq : ∀ (i : Fin 15) (j : Fin 8), truncatedChordCell 1 sharedDiskP482Params (sharedChord469Gauss8Points i j)=sharedDiskP482Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP482Values0_eq
  · exact sharedDiskP482Values1_eq
  · exact sharedDiskP482Values2_eq
  · exact sharedDiskP482Values3_eq
  · exact sharedDiskP482Values4_eq
  · exact sharedDiskP482Values5_eq
  · exact sharedDiskP482Values6_eq
  · exact sharedDiskP482Values7_eq
  · exact sharedDiskP482Values8_eq
  · exact sharedDiskP482Values9_eq
  · exact sharedDiskP482Values10_eq
  · exact sharedDiskP482Values11_eq
  · exact sharedDiskP482Values12_eq
  · exact sharedDiskP482Values13_eq
  · exact sharedDiskP482Values14_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP482Box : HorizontalRectangle := ⟨(59/100),(119/200),(1156300018531/2199023255552),(1160594985827/2199023255552),(950560215685430127430746284313605/649037107316853453566312041152512),(3231562298382386184506781455436805/649037107316853453566312041152512),(-651673764614589508377537777481475/162259276829213363391578010288128),(-53842080704930206688075350259459/162259276829213363391578010288128),true,[]⟩
noncomputable def sharedDiskP482Grid : CGrid := momentChordGrid sharedDiskP482Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984)
theorem sharedDiskP482Columns : containedInReported sharedDiskP482Grid.re sharedDiskP482Box.reLo sharedDiskP482Box.reHi=true ∧ containedInReported sharedDiskP482Grid.im sharedDiskP482Box.imLo sharedDiskP482Box.imHi=true := by
  rw [sharedDiskP482Grid,momentChordGrid_eq_tabulated sharedDiskP482Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984) sharedChord469Gauss8Points sharedChord469Gauss8Weights sharedDiskP482Values sharedChord469Gauss8Points_eq sharedChord469Gauss8Weights_eq sharedDiskP482Values_eq]
  decide +kernel
theorem sharedDiskP482Sound : sharedDiskP482Box.Sound := by
  intro t a tl tu al au
  change (((59/100):ℚ):ℝ)≤t at tl
  change t≤(((119/200):ℚ):ℝ) at tu
  change (((1156300018531/2199023255552):ℚ):ℝ)≤a at al
  change a≤(((1160594985827/2199023255552):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP482Params_ok] at ps
  have band := sharedChord469ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((21/40):ℚ)≤(59/100))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((119/200):ℚ)≤(63/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3408482035145/6597069766656):ℚ)≤(1156300018531/2199023255552))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((1160594985827/2199023255552):ℚ)≤(885480886574489/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord469Bd (by decide +kernel) (by decide +kernel) sharedChord469M (by decide +kernel) (sharedChord469Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP482Columns.1 sharedDiskP482Columns.2
def sharedDiskP482Rows : List SignRow := [positive_482.toSignRow]
theorem sharedDiskP482Rows_actual : ∀ r∈sharedDiskP482Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP482Rows.all (sharedDiskP482Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP482Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP484Params : ChordParams := ⟨⟨(-7309733048167206819051),(-6433377908091911306653),true⟩,⟨2876827719854774092652303,3009299416103170375426740,true⟩,⟨73747511652428175321447,82907693388693457979789,true⟩,⟨100308792942684593821765,111925265517153375801302,true⟩,⟨175319939693655813442123,187014629744994917115549,true⟩,⟨1194394218401241957766178,1196127172636380157458790,true⟩,⟨(-3131453615261318551632250),(-3050650489446719328993758),true⟩,⟨⟨1133570432751126674057118,1260065659912235209057743,true⟩,⟨(-74),74,true⟩⟩⟩
theorem sharedDiskP484Params_ok : chordParams (Grid.ofRats (3/5) (123/200)) (Grid.ofRats (865191350615051/1649267441664000) (880967977455467/1649267441664000))=sharedDiskP484Params := by decide +kernel
def sharedDiskP484Values (i : Fin 15) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-9236382161420072835559722),(-2471174356916175769871857),true⟩,⟨(-2817863777442030407624662),3382941679940610076416865,true⟩⟩
  | 0,1 => ⟨⟨(-8845427975756599377597636),(-2270695396077696858272246),true⟩,⟨(-2841109255930604817160973),3273761972895960883445949,true⟩⟩
  | 0,2 => ⟨⟨(-8535066334224154321044040),(-2127569580955900973623230),true⟩,⟨(-2853752304030183497372384),3164016638552635713840222,true⟩⟩
  | 0,3 => ⟨⟨(-8348017388078299157742152),(-2037854563847592562271645),true⟩,⟨(-2858988895267939370505274),3089164239254373711430960,true⟩⟩
  | 0,4 => ⟨⟨(-9652813795397040616072146),(-2712553436938846068917058),true⟩,⟨(-2783798103317119570184910),3457973553296308381371020,true⟩⟩
  | 0,5 => ⟨⟨(-10036656232639975084935413),(-2963453411732653138997121),true⟩,⟨(-2743789638563365609684140),3483573764001363654066274,true⟩⟩
  | 0,6 => ⟨⟨(-10336818702208634704143632),(-3180384823957412114509015),true⟩,⟨(-2706874462754890923276584),3470693078634661471186043,true⟩⟩
  | 0,7 => ⟨⟨(-10515954481443855096682292),(-3319027584098080696730065),true⟩,⟨(-2682603987602408553101566),3447990886962806953738096,true⟩⟩
  | 1,0 => ⟨⟨(-6979315236123392634963253),(-1451414583753533081444874),true⟩,⟨(-2848737493049815159949278),2390396201839033742498566,true⟩⟩
  | 1,1 => ⟨⟨(-6612998084389927067323966),(-1317451262925804953742824),true⟩,⟨(-2833453694888999691674071),2171232902965359582442459,true⟩⟩
  | 1,2 => ⟨⟨(-6329801980348038703842092),(-1219039221365806911482254),true⟩,⟨(-2818598899666721023684784),1995941192175693947072385,true⟩⟩
  | 1,3 => ⟨⟨(-6162233846223820139451610),(-1162695269621379621671395),true⟩,⟨(-2808654481168058491805911),1890321865030155142963394,true⟩⟩
  | 1,4 => ⟨⟨(-7381779568089161139403849),(-1608526737396395929238335),true⟩,⟨(-2859907250271978593647038),2618481082632088596560373,true⟩⟩
  | 1,5 => ⟨⟨(-7764271255470581967983636),(-1768896564253801408435991),true⟩,⟨(-2864509891449432250015670),2819637064008961669894901,true⟩⟩
  | 1,6 => ⟨⟨(-8071096971381369906105949),(-1906342946499178557922477),true⟩,⟨(-2863591225108055420979675),2967610208356562221177386,true⟩⟩
  | 1,7 => ⟨⟨(-8257379529553283380535896),(-1993989650650425200989324),true⟩,⟨(-2860902286767530714670479),3050731134070702097821622,true⟩⟩
  | 2,0 => ⟨⟨(-5000696975573317111278257),(-800964624715749022302465),true⟩,⟨(-2720095558716555885750133),1188596581176469124604547,true⟩⟩
  | 2,1 => ⟨⟨(-4706504485616500957016410),(-714827770984501933858237),true⟩,⟨(-2693150888907896614915260),1028582516383091396941876,true⟩⟩
  | 2,2 => ⟨⟨(-4482830991250732560657191),(-650216551184487754927693),true⟩,⟨(-2671584180617589173927868),906690484448285483149250,true⟩⟩
  | 2,3 => ⟨⟨(-4351884560710340783670546),(-612627081940612954780769),true⟩,⟨(-2658547403244013689324459),835388938682081130555270,true⟩⟩
  | 2,4 => ⟨⟨(-5331002836651183836158552),(-899891063443207987305304),true⟩,⟨(-2748264655738518137088864),1366965221431397576187074,true⟩⟩
  | 2,5 => ⟨⟨(-5653356655651557352717009),(-998995703537190658962526),true⟩,⟨(-2773663700854523646499705),1563478059487164786818025,true⟩⟩
  | 2,6 => ⟨⟨(-5918254267671150816125049),(-1082913949052822272833661),true⟩,⟨(-2792741175729678476630011),1734561842013987920117018,true⟩⟩
  | 2,7 => ⟨⟨(-6081848402216253113509617),(-1136125498080437845190862),true⟩,⟨(-2803594667052647565802998),1839236782365709360880812,true⟩⟩
  | 3,0 => ⟨⟨(-3465769493206093449723185),(-358237304486827104249461),true⟩,⟨(-2562809739076800539700397),359962271023116082777481,true⟩⟩
  | 3,1 => ⟨⟨(-3245542507076669047435528),(-293664757283591234767342),true⟩,⟨(-2536980515680898977904906),245434780004946583582122,true⟩⟩
  | 3,2 => ⟨⟨(-3078905827227372552865738),(-244051598770164546033681),true⟩,⟨(-2516855030924156428534351),160247341292724816975656,true⟩⟩
  | 3,3 => ⟨⟨(-2981593811495638468271133),(-214713022014773625592686),true⟩,⟨(-2504856194169245608596862),111170967231486482322280,true⟩⟩
  | 3,4 => ⟨⟨(-3714899517025797926349847),(-430290653430723025049360),true⟩,⟨(-2591032293645865393019582),491706484579927817618441,true⟩⟩
  | 3,5 => ⟨⟨(-3959835531179606226255229),(-500513769446975363077085),true⟩,⟨(-2617783333861905143923513),622968296921370516792440,true⟩⟩
  | 3,6 => ⟨⟨(-4162926586259494004683823),(-558561642737436741506276),true⟩,⟨(-2639219334524670467981319),732745145750252762709013,true⟩⟩
  | 3,7 => ⟨⟨(-4289412394269571181323944),(-594735366734857615306791),true⟩,⟨(-2652223944875643603398065),801413359295909417485416,true⟩⟩
  | 4,0 => ⟨⟨(-1015677840485026753371891),545345015647870749027177,true⟩,⟨(-2183260026266458002333336),(-564850662727788198747522),true⟩⟩
  | 4,1 => ⟨⟨(-653186166576091090416737),766845821866721686171541,true⟩,⟨(-2097496567749078771312208),(-604477685036158583444546),true⟩⟩
  | 4,2 => ⟨⟨(-398639179640865171816395),932571026453488936465705,true⟩,⟨(-2028761059545203169884809),(-618507391863336447491565),true⟩⟩
  | 4,3 => ⟨⟨(-256665627827920491287208),1028655928611604949313044,true⟩,⟨(-1986964116202901638997975),(-621000779088786097262918),true⟩⟩
  | 4,4 => ⟨⟨(-1490832569263974696462799),321679552977852149380018,true⟩,⟨(-2278738138402083430030115),(-451146669639468527720720),true⟩⟩
  | 4,5 => ⟨⟨(-2022754059968867940130177),109533159447511306718036,true⟩,⟨(-2369699871003867075468343),(-282009849358088888838355),true⟩⟩
  | 4,6 => ⟨⟨(-2517707823040934260485711),(-67987180505208039539388),true⟩,⟨(-2443954924450618427327588),(-102109206034001772031851),true⟩⟩
  | 4,7 => ⟨⟨(-2866683987623550876850530),(-179671483617359115570230),true⟩,⟨(-2490440208895554399059670),53923153934444011665017,true⟩⟩
  | 5,0 => ⟨⟨1060599787815149831253686,2144494006275059219974796,true⟩,⟨(-1453064035499513785978842),(-413065529479243836568131),true⟩⟩
  | 5,1 => ⟨⟨1304141859760283170034886,2372617593199157892340404,true⟩,⟨(-1317797816862620879453505),(-328394019057590835569994),true⟩⟩
  | 5,2 => ⟨⟨1472653273609645921907578,2529569184615053193122316,true⟩,⟨(-1216935364552063624677589),(-263132890363099374601876),true⟩⟩
  | 5,3 => ⟨⟨1564960829293907331526210,2614855399132606355583442,true⟩,⟨(-1159116081853005545064012),(-225269141186305170006776),true⟩⟩
  | 5,4 => ⟨⟨754761423879849823808032,1859003865250065565204414,true⟩,⟨(-1605400420114542883177173),(-501278877684992668676512),true⟩⟩
  | 5,5 => ⟨⟨419153908927003875603657,1551224575151639970931114,true⟩,⟨(-1749785891633377518578799),(-571866119852622730897972),true⟩⟩
  | 5,6 => ⟨⟨91250127378194618530721,1276560855358585292028396,true⟩,⟨(-1872156021005827388197241),(-610036019555201777642919),true⟩⟩
  | 5,7 => ⟨⟨(-158175184169780795597613),1096821729949205590489596,true⟩,⟨(-1956411141383183486424718),(-620407312646374787190467),true⟩⟩
  | 6,0 => ⟨⟨2352563088937639573955838,3279531917750380518016106,true⟩,⟨(-585469292313832652218462),141473588262377795279113,true⟩⟩
  | 6,1 => ⟨⟨2454024842216024624572413,3345425952636377384569312,true⟩,⟨(-507301136388062561190977),182618120732763989704364,true⟩⟩
  | 6,2 => ⟨⟨2515628862699211026588343,3381963329901043081898371,true⟩,⟨(-468254546182929273289917),198589043409353637431074,true⟩⟩
  | 6,3 => ⟨⟨2547633484182930574553213,3400833373810725494559316,true⟩,⟨(-454197181070900150198626),201633900247861896495545,true⟩⟩
  | 6,4 => ⟨⟨2199463442901934972743840,3166499727334966048212254,true⟩,⟨(-707929665607098780052863),67996667681425496073705,true⟩⟩
  | 6,5 => ⟨⟨1998006461071332570711398,3001356421487132842375638,true⟩,⟨(-861971715468087865457595),(-30663785922920727705218),true⟩⟩
  | 6,6 => ⟨⟨1784867369027995192899670,2814748846501941804304176,true⟩,⟨(-1013760601219403186161230),(-129614219471991736404495),true⟩⟩
  | 6,7 => ⟨⟨1628047446910492475913556,2672744169456738184730999,true⟩,⟨(-1118530477998244325463022),(-198584483406118279447511),true⟩⟩
  | 7,0 => ⟨⟨2703935851545652538802792,3764876608786449101467956,true⟩,⟨(-689788252689104608518682),134170797702295604331925,true⟩⟩
  | 7,1 => ⟨⟨2788978664096934363044354,3978692509816184254875175,true⟩,⟨(-896565616295280466274085),46202853419766026601353,true⟩⟩
  | 7,2 => ⟨⟨2882803684688844914368302,4220059778518984047616000,true⟩,⟨(-1151070320335417603806837),(-64755655562916497656861),true⟩⟩
  | 7,3 => ⟨⟨2952025545823847223057617,4407457997077255726321287,true⟩,⟨(-1364295077179866889672133),(-158586016845521392484708),true⟩⟩
  | 7,4 => ⟨⟨2643220396991613520288547,3610707013234411817127019,true⟩,⟨(-556130395428473835451611),186209949356481114692264,true⟩⟩
  | 7,5 => ⟨⟨2603400900223225106457016,3510266358436336296575896,true⟩,⟨(-485855605410873956617342),207374943986652118941079,true⟩⟩
  | 7,6 => ⟨⟨2576082854196506551051273,3447390728538746812949064,true⟩,⟨(-458330471393324205258797),208827612574300520695122,true⟩⟩
  | 7,7 => ⟨⟨2558944014336818697789803,3412887628517214270267261,true⟩,⟨(-452155664224207837898301),203577897977224156688979,true⟩⟩
  | 8,0 => ⟨⟨3236506818918735026741579,5558061748542112651057488,true⟩,⟨(-3083991883168503818523013),(-937776521284586029699326),true⟩⟩
  | 8,1 => ⟨⟨3226474827734574494645736,5997009404453218110358201,true⟩,⟨(-4046310899167195060679174),(-1377672432309596852232741),true⟩⟩
  | 8,2 => ⟨⟨3104598463424814349806204,6349896554221212689590810,true⟩,⟨(-5097395419983583255383163),(-1855248225810195280205666),true⟩⟩
  | 8,3 => ⟨⟨2942021664416315311078161,6539143251783903053780935,true⟩,⟨(-5893069457196361035567707),(-2213150868418328568059204),true⟩⟩
  | 8,4 => ⟨⟨3170755277445775321222942,5142970020006906506399940,true⟩,⟨(-2363845033582062401507760),(-608925732869636109122037),true⟩⟩
  | 8,5 => ⟨⟨3086748892316764114631762,4818141452601375770335196,true⟩,⟨(-1886441204185436171015841),(-392366872775099315943716),true⟩⟩
  | 8,6 => ⟨⟨3018781637511285542563967,4600817083918858838326801,true⟩,⟨(-1600065697232765272339250),(-263595435772690805093407),true⟩⟩
  | 8,7 => ⟨⟨2979455795646611176042382,4485076863836658635766539,true⟩,⟨(-1456923342820461489087720),(-199709103024050216529078),true⟩⟩
  | 9,0 => ⟨⟨2233352555866352323168501,6737540201874610679249339,true⟩,⟨(-7989432900451822744883929),(-3134318887736206889123453),true⟩⟩
  | 9,1 => ⟨⟨1932576491128513767467662,6710001499405764524304917,true⟩,⟨(-8629343555008739221002852),(-3407498840169879629864267),true⟩⟩
  | 9,2 => ⟨⟨1647486909685487288635237,6652716588543116531185977,true⟩,⟨(-9164516243058729641724281),(-3632426437053726065303398),true⟩⟩
  | 9,3 => ⟨⟨1453123212800045133897419,6600144557102323907281517,true⟩,⟨(-9498092815100329456201412),(-3770812377674833883443088),true⟩⟩
  | 9,4 => ⟨⟨2492989506752029666632464,6723019898679179974757322,true⟩,⟨(-7350508638705790331400890),(-2857478353575997801644700),true⟩⟩
  | 9,5 => ⟨⟨2685641347231881914350855,6678010074743823826335924,true⟩,⟨(-6799953374936916134816521),(-2616015992339524919112176),true⟩⟩
  | 9,6 => ⟨⟨2809657908383757228203852,6625852738944094222642819,true⟩,⟨(-6394240559748271997224705),(-2436523252771765274285880),true⟩⟩
  | 9,7 => ⟨⟨2873811084330382602108404,6588774674193503620111403,true⟩,⟨(-6162165278207123533650935),(-2333303035962820265537243),true⟩⟩
  | 10,0 => ⟨⟨(-1027938856176149708041678),5605382668259055959552227,true⟩,⟨(-12276978832556571815012484),(-4779979250898532992637275),true⟩⟩
  | 10,1 => ⟨⟨(-2082598205080863506758799),5075480632348591021471204,true⟩,⟨(-13050162535729098422911326),(-5008067770108627587604844),true⟩⟩
  | 10,2 => ⟨⟨(-3023735044178476252622817),4558478682775268217820616,true⟩,⟨(-13612222975854092775121824),(-5150281225552121001028906),true⟩⟩
  | 10,3 => ⟨⟨(-3635114563400709382435846),4202721122532173956584557,true⟩,⟨(-13918179230960374528166581),(-5214499891299659610898689),true⟩⟩
  | 10,4 => ⟨⟨(-59626150712051150184594),6036446421516317354136364,true⟩,⟨(-11411719135543183524768851),(-4495623647048698557858637),true⟩⟩
  | 10,5 => ⟨⟨682703742238929868409729,6327454512105108804909055,true⟩,⟨(-10603781706174015680625788),(-4210197837971960343999039),true⟩⟩
  | 10,6 => ⟨⟨1130506265566379421970007,6493228989813130897248264,true⟩,⟨(-10005806590656843209896207),(-3978467877812654176987220),true⟩⟩
  | 10,7 => ⟨⟨1352296794589026293240013,6569186052490470435548414,true⟩,⟨(-9662534612090914553134951),(-3838478134301254848909582),true⟩⟩
  | 11,0 => ⟨⟨(-6249754618872337865263488),2518793023157628225492523,true⟩,⟨(-14728769065364146638510469),(-5255558619306487962804367),true⟩⟩
  | 11,1 => ⟨⟨(-7005255221323268435921749),2020206437509515105432700,true⟩,⟨(-14809791405912487577458543),(-5178574229609807346636955),true⟩⟩
  | 11,2 => ⟨⟨(-7608675117095142886398559),1660106563696393339578987,true⟩,⟨(-14820683311594255272936700),(-5065718067612154224756273),true⟩⟩
  | 11,3 => ⟨⟨(-7972573758935513120335338),1437048443827741330093790,true⟩,⟨(-14802495720263809455659074),(-4985587870645638986222943),true⟩⟩
  | 11,4 => ⟨⟨(-5455750975123802239348323),3057568072656051647624275,true⟩,⟨(-14567759940577939217328529),(-5282662650345781908497007),true⟩⟩
  | 11,5 => ⟨⟨(-4737830748580213576396702),3524127943718303905221017,true⟩,⟨(-14357875553332393607863162),(-5277414972877771240427717),true⟩⟩
  | 11,6 => ⟨⟨(-4187988482878905128030115),3868309088699621742239164,true⟩,⟨(-14156442688310641219783939),(-5254412405447346533610897),true⟩⟩
  | 11,7 => ⟨⟨(-3865370981859549856606714),4064887263849783824250152,true⟩,⟨(-14021790869585840895028757),(-5233187650616814183221483),true⟩⟩
  | 12,0 => ⟨⟨(-10548002711049782505834425),(-299574784011057424535404),true⟩,⟨(-13992762024757389474500580),(-4091154969453836826814086),true⟩⟩
  | 12,1 => ⟨⟨(-11220899748749075795585744),(-774470998971116791535593),true⟩,⟨(-13536604180876121859530189),(-3698203637600262698512307),true⟩⟩
  | 12,2 => ⟨⟨(-11724999559495087444650697),(-1141499905321613226051670),true⟩,⟨(-13101679569314697751306906),(-3338263267548754983985641),true⟩⟩
  | 12,3 => ⟨⟨(-12002974082466475969941740),(-1357265139751484376632875),true⟩,⟨(-12807978017670614525488932),(-3111713647197535526199552),true⟩⟩
  | 12,4 => ⟨⟨(-9819784946670006775377662),222096865563591160614168,true⟩,⟨(-14368216992566478349181012),(-4413937139849830339940336),true⟩⟩
  | 12,5 => ⟨⟨(-9099488928018828898182037),714354219866595470012532,true⟩,⟨(-14613336982697204123361747),(-4673192654901878020576532),true⟩⟩
  | 12,6 => ⟨⟨(-8509716715462153442498836),1098984231324364840394201,true⟩,⟨(-14738855669928793583927031),(-4849471048320617165545360),true⟩⟩
  | 12,7 => ⟨⟨(-8148692868640729923306217),1327400883243519076699778,true⟩,⟨(-14786615643613284433487236),(-4943370340013055788458095),true⟩⟩
  | 13,0 => ⟨⟨(-13282784303722775092089866),(-2745383046732317392045956),true⟩,⟨(-9950892278738140875626788),(-1296911748454751752244817),true⟩⟩
  | 13,1 => ⟨⟨(-13346755906279380508848487),(-3037034075308283600435988),true⟩,⟨(-8988982256977241204201377),(-789836417105257081393328),true⟩⟩
  | 13,2 => ⟨⟨(-13299155874836660379051933),(-3231691567807820385298352),true⟩,⟨(-8196715626142551323674636),(-401590553471145879467916),true⟩⟩
  | 13,3 => ⟨⟨(-13228596485882435552352475),(-3332848866087190454143512),true⟩,⟨(-7710308306190362844990574),(-175469827721195684315149),true⟩⟩
  | 13,4 => ⟨⟨(-13063535135182360496231201),(-2380131617083883436099805),true⟩,⟨(-10916641491452424326531251),(-1850734751478068357826001),true⟩⟩
  | 13,5 => ⟨⟨(-12726167259945794150833506),(-1996573807440856307716915),true⟩,⟨(-11739389994731071432332792),(-2365123232071441298713336),true⟩⟩
  | 13,6 => ⟨⟨(-12374917782486376956596326),(-1667630325660060658879967),true⟩,⟨(-12329629059152595166006498),(-2764395604339378546338132),true⟩⟩
  | 13,7 => ⟨⟨(-12130105115356775890096808),(-1460117355937964634096725),true⟩,⟨(-12657122509808256955333387),(-2999531201058607945894867),true⟩⟩
  | 14,0 => ⟨⟨(-11818768203607201768969220),(-3693668552125170663871624),true⟩,⟨(-4118364289345675716513659),1737058488669441142396908,true⟩⟩
  | 14,1 => ⟨⟨(-11179722733343353403826278),(-3677149549085072014681760),true⟩,⟨(-3201514412353062668734839),2199268689496634818023512,true⟩⟩
  | 14,2 => ⟨⟨(-10621598139715700671101318),(-3621577067608640166983044),true⟩,⟨(-2523071120769051648926728),2505068208108635568341465,true⟩⟩
  | 14,3 => ⟨⟨(-10274615954740627459677075),(-3545880074250697083696433),true⟩,⟨(-2137087889276217737424933),2663460569532522098527233,true⟩⟩
  | 14,4 => ⟨⟨(-12401358796974734729648973),(-3657212961027691964685850),true⟩,⟨(-5161472516666868757327722),1151033865244817188275771,true⟩⟩
  | 14,5 => ⟨⟨(-12828704366900443720724357),(-3568811999991330662130287),true⟩,⟨(-6170913408184502232490124),613548369464614617466935,true⟩⟩
  | 14,6 => ⟨⟨(-13077526724011127514078389),(-3459938509856102445783424),true⟩,⟨(-6982799459183213817499163),205998464524786284850624,true⟩⟩
  | 14,7 => ⟨⟨(-13186524699107441185278549),(-3377439258463941279184286),true⟩,⟨(-7473067683855238247102669),(-52485928789640959782066),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP484Value0_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 0 (0:Fin 8))=sharedDiskP484Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value0_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 0 (1:Fin 8))=sharedDiskP484Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value0_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 0 (2:Fin 8))=sharedDiskP484Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value0_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 0 (3:Fin 8))=sharedDiskP484Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value0_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 0 (4:Fin 8))=sharedDiskP484Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value0_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 0 (5:Fin 8))=sharedDiskP484Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value0_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 0 (6:Fin 8))=sharedDiskP484Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value0_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 0 (7:Fin 8))=sharedDiskP484Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 0 j)=sharedDiskP484Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value0_0
  · exact sharedDiskP484Value0_1
  · exact sharedDiskP484Value0_2
  · exact sharedDiskP484Value0_3
  · exact sharedDiskP484Value0_4
  · exact sharedDiskP484Value0_5
  · exact sharedDiskP484Value0_6
  · exact sharedDiskP484Value0_7
private theorem sharedDiskP484Value1_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 1 (0:Fin 8))=sharedDiskP484Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value1_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 1 (1:Fin 8))=sharedDiskP484Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value1_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 1 (2:Fin 8))=sharedDiskP484Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value1_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 1 (3:Fin 8))=sharedDiskP484Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value1_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 1 (4:Fin 8))=sharedDiskP484Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value1_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 1 (5:Fin 8))=sharedDiskP484Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value1_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 1 (6:Fin 8))=sharedDiskP484Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value1_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 1 (7:Fin 8))=sharedDiskP484Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 1 j)=sharedDiskP484Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value1_0
  · exact sharedDiskP484Value1_1
  · exact sharedDiskP484Value1_2
  · exact sharedDiskP484Value1_3
  · exact sharedDiskP484Value1_4
  · exact sharedDiskP484Value1_5
  · exact sharedDiskP484Value1_6
  · exact sharedDiskP484Value1_7
private theorem sharedDiskP484Value2_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 2 (0:Fin 8))=sharedDiskP484Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value2_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 2 (1:Fin 8))=sharedDiskP484Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value2_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 2 (2:Fin 8))=sharedDiskP484Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value2_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 2 (3:Fin 8))=sharedDiskP484Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value2_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 2 (4:Fin 8))=sharedDiskP484Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value2_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 2 (5:Fin 8))=sharedDiskP484Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value2_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 2 (6:Fin 8))=sharedDiskP484Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value2_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 2 (7:Fin 8))=sharedDiskP484Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 2 j)=sharedDiskP484Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value2_0
  · exact sharedDiskP484Value2_1
  · exact sharedDiskP484Value2_2
  · exact sharedDiskP484Value2_3
  · exact sharedDiskP484Value2_4
  · exact sharedDiskP484Value2_5
  · exact sharedDiskP484Value2_6
  · exact sharedDiskP484Value2_7
private theorem sharedDiskP484Value3_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 3 (0:Fin 8))=sharedDiskP484Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value3_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 3 (1:Fin 8))=sharedDiskP484Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value3_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 3 (2:Fin 8))=sharedDiskP484Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value3_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 3 (3:Fin 8))=sharedDiskP484Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value3_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 3 (4:Fin 8))=sharedDiskP484Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value3_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 3 (5:Fin 8))=sharedDiskP484Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value3_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 3 (6:Fin 8))=sharedDiskP484Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value3_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 3 (7:Fin 8))=sharedDiskP484Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 3 j)=sharedDiskP484Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value3_0
  · exact sharedDiskP484Value3_1
  · exact sharedDiskP484Value3_2
  · exact sharedDiskP484Value3_3
  · exact sharedDiskP484Value3_4
  · exact sharedDiskP484Value3_5
  · exact sharedDiskP484Value3_6
  · exact sharedDiskP484Value3_7
private theorem sharedDiskP484Value4_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 4 (0:Fin 8))=sharedDiskP484Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value4_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 4 (1:Fin 8))=sharedDiskP484Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value4_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 4 (2:Fin 8))=sharedDiskP484Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value4_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 4 (3:Fin 8))=sharedDiskP484Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value4_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 4 (4:Fin 8))=sharedDiskP484Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value4_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 4 (5:Fin 8))=sharedDiskP484Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value4_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 4 (6:Fin 8))=sharedDiskP484Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value4_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 4 (7:Fin 8))=sharedDiskP484Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 4 j)=sharedDiskP484Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value4_0
  · exact sharedDiskP484Value4_1
  · exact sharedDiskP484Value4_2
  · exact sharedDiskP484Value4_3
  · exact sharedDiskP484Value4_4
  · exact sharedDiskP484Value4_5
  · exact sharedDiskP484Value4_6
  · exact sharedDiskP484Value4_7
private theorem sharedDiskP484Value5_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 5 (0:Fin 8))=sharedDiskP484Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value5_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 5 (1:Fin 8))=sharedDiskP484Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value5_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 5 (2:Fin 8))=sharedDiskP484Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value5_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 5 (3:Fin 8))=sharedDiskP484Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value5_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 5 (4:Fin 8))=sharedDiskP484Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value5_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 5 (5:Fin 8))=sharedDiskP484Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value5_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 5 (6:Fin 8))=sharedDiskP484Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value5_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 5 (7:Fin 8))=sharedDiskP484Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 5 j)=sharedDiskP484Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value5_0
  · exact sharedDiskP484Value5_1
  · exact sharedDiskP484Value5_2
  · exact sharedDiskP484Value5_3
  · exact sharedDiskP484Value5_4
  · exact sharedDiskP484Value5_5
  · exact sharedDiskP484Value5_6
  · exact sharedDiskP484Value5_7
private theorem sharedDiskP484Value6_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 6 (0:Fin 8))=sharedDiskP484Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value6_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 6 (1:Fin 8))=sharedDiskP484Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value6_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 6 (2:Fin 8))=sharedDiskP484Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value6_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 6 (3:Fin 8))=sharedDiskP484Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value6_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 6 (4:Fin 8))=sharedDiskP484Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value6_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 6 (5:Fin 8))=sharedDiskP484Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value6_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 6 (6:Fin 8))=sharedDiskP484Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value6_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 6 (7:Fin 8))=sharedDiskP484Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 6 j)=sharedDiskP484Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value6_0
  · exact sharedDiskP484Value6_1
  · exact sharedDiskP484Value6_2
  · exact sharedDiskP484Value6_3
  · exact sharedDiskP484Value6_4
  · exact sharedDiskP484Value6_5
  · exact sharedDiskP484Value6_6
  · exact sharedDiskP484Value6_7
private theorem sharedDiskP484Value7_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 7 (0:Fin 8))=sharedDiskP484Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value7_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 7 (1:Fin 8))=sharedDiskP484Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value7_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 7 (2:Fin 8))=sharedDiskP484Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value7_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 7 (3:Fin 8))=sharedDiskP484Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value7_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 7 (4:Fin 8))=sharedDiskP484Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value7_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 7 (5:Fin 8))=sharedDiskP484Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value7_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 7 (6:Fin 8))=sharedDiskP484Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value7_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 7 (7:Fin 8))=sharedDiskP484Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 7 j)=sharedDiskP484Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value7_0
  · exact sharedDiskP484Value7_1
  · exact sharedDiskP484Value7_2
  · exact sharedDiskP484Value7_3
  · exact sharedDiskP484Value7_4
  · exact sharedDiskP484Value7_5
  · exact sharedDiskP484Value7_6
  · exact sharedDiskP484Value7_7
private theorem sharedDiskP484Value8_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 8 (0:Fin 8))=sharedDiskP484Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value8_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 8 (1:Fin 8))=sharedDiskP484Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value8_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 8 (2:Fin 8))=sharedDiskP484Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value8_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 8 (3:Fin 8))=sharedDiskP484Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value8_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 8 (4:Fin 8))=sharedDiskP484Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value8_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 8 (5:Fin 8))=sharedDiskP484Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value8_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 8 (6:Fin 8))=sharedDiskP484Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value8_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 8 (7:Fin 8))=sharedDiskP484Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 8 j)=sharedDiskP484Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value8_0
  · exact sharedDiskP484Value8_1
  · exact sharedDiskP484Value8_2
  · exact sharedDiskP484Value8_3
  · exact sharedDiskP484Value8_4
  · exact sharedDiskP484Value8_5
  · exact sharedDiskP484Value8_6
  · exact sharedDiskP484Value8_7
private theorem sharedDiskP484Value9_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 9 (0:Fin 8))=sharedDiskP484Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value9_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 9 (1:Fin 8))=sharedDiskP484Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value9_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 9 (2:Fin 8))=sharedDiskP484Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value9_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 9 (3:Fin 8))=sharedDiskP484Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value9_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 9 (4:Fin 8))=sharedDiskP484Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value9_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 9 (5:Fin 8))=sharedDiskP484Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value9_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 9 (6:Fin 8))=sharedDiskP484Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value9_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 9 (7:Fin 8))=sharedDiskP484Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 9 j)=sharedDiskP484Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value9_0
  · exact sharedDiskP484Value9_1
  · exact sharedDiskP484Value9_2
  · exact sharedDiskP484Value9_3
  · exact sharedDiskP484Value9_4
  · exact sharedDiskP484Value9_5
  · exact sharedDiskP484Value9_6
  · exact sharedDiskP484Value9_7
private theorem sharedDiskP484Value10_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 10 (0:Fin 8))=sharedDiskP484Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value10_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 10 (1:Fin 8))=sharedDiskP484Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value10_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 10 (2:Fin 8))=sharedDiskP484Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value10_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 10 (3:Fin 8))=sharedDiskP484Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value10_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 10 (4:Fin 8))=sharedDiskP484Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value10_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 10 (5:Fin 8))=sharedDiskP484Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value10_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 10 (6:Fin 8))=sharedDiskP484Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value10_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 10 (7:Fin 8))=sharedDiskP484Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 10 j)=sharedDiskP484Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value10_0
  · exact sharedDiskP484Value10_1
  · exact sharedDiskP484Value10_2
  · exact sharedDiskP484Value10_3
  · exact sharedDiskP484Value10_4
  · exact sharedDiskP484Value10_5
  · exact sharedDiskP484Value10_6
  · exact sharedDiskP484Value10_7
private theorem sharedDiskP484Value11_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 11 (0:Fin 8))=sharedDiskP484Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value11_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 11 (1:Fin 8))=sharedDiskP484Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value11_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 11 (2:Fin 8))=sharedDiskP484Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value11_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 11 (3:Fin 8))=sharedDiskP484Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value11_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 11 (4:Fin 8))=sharedDiskP484Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value11_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 11 (5:Fin 8))=sharedDiskP484Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value11_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 11 (6:Fin 8))=sharedDiskP484Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value11_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 11 (7:Fin 8))=sharedDiskP484Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 11 j)=sharedDiskP484Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value11_0
  · exact sharedDiskP484Value11_1
  · exact sharedDiskP484Value11_2
  · exact sharedDiskP484Value11_3
  · exact sharedDiskP484Value11_4
  · exact sharedDiskP484Value11_5
  · exact sharedDiskP484Value11_6
  · exact sharedDiskP484Value11_7
private theorem sharedDiskP484Value12_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 12 (0:Fin 8))=sharedDiskP484Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value12_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 12 (1:Fin 8))=sharedDiskP484Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value12_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 12 (2:Fin 8))=sharedDiskP484Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value12_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 12 (3:Fin 8))=sharedDiskP484Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value12_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 12 (4:Fin 8))=sharedDiskP484Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value12_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 12 (5:Fin 8))=sharedDiskP484Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value12_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 12 (6:Fin 8))=sharedDiskP484Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value12_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 12 (7:Fin 8))=sharedDiskP484Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 12 j)=sharedDiskP484Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value12_0
  · exact sharedDiskP484Value12_1
  · exact sharedDiskP484Value12_2
  · exact sharedDiskP484Value12_3
  · exact sharedDiskP484Value12_4
  · exact sharedDiskP484Value12_5
  · exact sharedDiskP484Value12_6
  · exact sharedDiskP484Value12_7
private theorem sharedDiskP484Value13_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 13 (0:Fin 8))=sharedDiskP484Values 13 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value13_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 13 (1:Fin 8))=sharedDiskP484Values 13 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value13_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 13 (2:Fin 8))=sharedDiskP484Values 13 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value13_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 13 (3:Fin 8))=sharedDiskP484Values 13 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value13_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 13 (4:Fin 8))=sharedDiskP484Values 13 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value13_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 13 (5:Fin 8))=sharedDiskP484Values 13 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value13_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 13 (6:Fin 8))=sharedDiskP484Values 13 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value13_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 13 (7:Fin 8))=sharedDiskP484Values 13 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values13_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 13 j)=sharedDiskP484Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value13_0
  · exact sharedDiskP484Value13_1
  · exact sharedDiskP484Value13_2
  · exact sharedDiskP484Value13_3
  · exact sharedDiskP484Value13_4
  · exact sharedDiskP484Value13_5
  · exact sharedDiskP484Value13_6
  · exact sharedDiskP484Value13_7
private theorem sharedDiskP484Value14_0 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 14 (0:Fin 8))=sharedDiskP484Values 14 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value14_1 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 14 (1:Fin 8))=sharedDiskP484Values 14 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value14_2 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 14 (2:Fin 8))=sharedDiskP484Values 14 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value14_3 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 14 (3:Fin 8))=sharedDiskP484Values 14 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value14_4 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 14 (4:Fin 8))=sharedDiskP484Values 14 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value14_5 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 14 (5:Fin 8))=sharedDiskP484Values 14 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value14_6 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 14 (6:Fin 8))=sharedDiskP484Values 14 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP484Value14_7 : truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 14 (7:Fin 8))=sharedDiskP484Values 14 (7:Fin 8) := by decide +kernel
theorem sharedDiskP484Values14_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points 14 j)=sharedDiskP484Values 14 j := by
  intro j
  fin_cases j
  · exact sharedDiskP484Value14_0
  · exact sharedDiskP484Value14_1
  · exact sharedDiskP484Value14_2
  · exact sharedDiskP484Value14_3
  · exact sharedDiskP484Value14_4
  · exact sharedDiskP484Value14_5
  · exact sharedDiskP484Value14_6
  · exact sharedDiskP484Value14_7
theorem sharedDiskP484Values_eq : ∀ (i : Fin 15) (j : Fin 8), truncatedChordCell 1 sharedDiskP484Params (sharedChord469Gauss8Points i j)=sharedDiskP484Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP484Values0_eq
  · exact sharedDiskP484Values1_eq
  · exact sharedDiskP484Values2_eq
  · exact sharedDiskP484Values3_eq
  · exact sharedDiskP484Values4_eq
  · exact sharedDiskP484Values5_eq
  · exact sharedDiskP484Values6_eq
  · exact sharedDiskP484Values7_eq
  · exact sharedDiskP484Values8_eq
  · exact sharedDiskP484Values9_eq
  · exact sharedDiskP484Values10_eq
  · exact sharedDiskP484Values11_eq
  · exact sharedDiskP484Values12_eq
  · exact sharedDiskP484Values13_eq
  · exact sharedDiskP484Values14_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP484Box : HorizontalRectangle := ⟨(3/5),(123/200),(865191350615051/1649267441664000),(880967977455467/1649267441664000),(184286742561416524444815463918593/324518553658426726783156020576256),(1733511388971813648141154959862785/324518553658426726783156020576256),(-389444740642838628818236404557513/81129638414606681695789005144064),(228525353717607634155847095522161/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP484Grid : CGrid := momentChordGrid sharedDiskP484Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984)
theorem sharedDiskP484Columns : containedInReported sharedDiskP484Grid.re sharedDiskP484Box.reLo sharedDiskP484Box.reHi=true ∧ containedInReported sharedDiskP484Grid.im sharedDiskP484Box.imLo sharedDiskP484Box.imHi=true := by
  rw [sharedDiskP484Grid,momentChordGrid_eq_tabulated sharedDiskP484Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984) sharedChord469Gauss8Points sharedChord469Gauss8Weights sharedDiskP484Values sharedChord469Gauss8Points_eq sharedChord469Gauss8Weights_eq sharedDiskP484Values_eq]
  decide +kernel
theorem sharedDiskP484Sound : sharedDiskP484Box.Sound := by
  intro t a tl tu al au
  change (((3/5):ℚ):ℝ)≤t at tl
  change t≤(((123/200):ℚ):ℝ) at tu
  change (((865191350615051/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((880967977455467/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP484Params_ok] at ps
  have band := sharedChord469ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((21/40):ℚ)≤(3/5))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((123/200):ℚ)≤(63/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3408482035145/6597069766656):ℚ)≤(865191350615051/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((880967977455467/1649267441664000):ℚ)≤(885480886574489/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord469Bd (by decide +kernel) (by decide +kernel) sharedChord469M (by decide +kernel) (sharedChord469Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP484Columns.1 sharedDiskP484Columns.2
def sharedDiskP484Rows : List SignRow := [positive_484.toSignRow, positive_485.toSignRow, positive_486.toSignRow]
theorem sharedDiskP484Rows_actual : ∀ r∈sharedDiskP484Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP484Rows.all (sharedDiskP484Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP484Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP487Params : ChordParams := ⟨⟨(-8255110690802907805538),(-7309733048167206818866),true⟩,⟨2791835980130812229077681,2919528848011663100584085,true⟩,⟨77857873007842069549022,87209274043643035520398,true⟩,⟨108040896966035236584339,120077203177636163149250,true⟩,⟨186734728315905385278739,198597250422536859178970,true⟩,⟨1192527573126518129998654,1194394218401241957766546,true⟩,⟨(-3050650489446719329004419),(-2973361795982170076176350),true⟩,⟨⟨1129991727007784410468123,1260136554605913798304844,true⟩,⟨(-160),160,true⟩⟩⟩
theorem sharedDiskP487Params_ok : chordParams (Grid.ofRats (123/200) (63/100)) (Grid.ofRats (869564008542899/1649267441664000) (885480886574489/1649267441664000))=sharedDiskP487Params := by decide +kernel
def sharedDiskP487Values (i : Fin 15) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-9104520813382477412302044),(-2421115001280819527930627),true⟩,⟨(-2777933030792790675243104),3348750722961255462421181,true⟩⟩
  | 0,1 => ⟨⟨(-8743006239142976223287250),(-2233224970436964684580184),true⟩,⟨(-2798537797802517023525078),3252722063961324931735172,true⟩⟩
  | 0,2 => ⟨⟨(-8455710157982407747142386),(-2098428728659550694415257),true⟩,⟨(-2809741365863355089706216),3155764549016873190225024,true⟩⟩
  | 0,3 => ⟨⟨(-8282393888067362155597561),(-2020824973465916616039955),true⟩,⟨(-2814370042300530285119345),3089400592135087038557191,true⟩⟩
  | 0,4 => ⟨⟨(-9489281142370545762564677),(-2646095467955065030216643),true⟩,⟨(-2747753873641719867304448),3414451111251202930863138,true⟩⟩
  | 0,5 => ⟨⟨(-9843775276466299380999102),(-2878780075741960006307278),true⟩,⟨(-2712307225460682342662722),3436763455104968349952737,true⟩⟩
  | 0,6 => ⟨⟨(-10120944066515212379036075),(-3079212224696047356399700),true⟩,⟨(-2679563088247860462874862),3425490786176572347067378,true⟩⟩
  | 0,7 => ⟨⟨(-10286351650199463157256901),(-3207024919078937059136015),true⟩,⟨(-2657999430559258054366962),3405688105546103301381623,true⟩⟩
  | 1,0 => ⟨⟨(-7008375086314993268828587),(-1466000732007085283541958),true⟩,⟨(-2804240009471079591416253),2461028744571949524967301,true⟩⟩
  | 1,1 => ⟨⟨(-6665062588885018468005827),(-1338157493403865550485888),true⟩,⟨(-2789889965543060628546866),2260593404202228404720334,true⟩⟩
  | 1,2 => ⟨⟨(-6398796794913968407734173),(-1244002641187687873939361),true⟩,⟨(-2775878955321390514540496),2099074207831420131182730,true⟩⟩
  | 1,3 => ⟨⟨(-6240867738796834668239715),(-1190014971853402748197591),true⟩,⟨(-2766462713640051269666697),2001220574879880114761078,true⟩⟩
  | 1,4 => ⟨⟨(-7384280716493856115191219),(-1615417502540213888932265),true⟩,⟨(-2814708023454676322897812),2667897525625677083268121,true⟩⟩
  | 1,5 => ⟨⟨(-7740454148770442062434417),(-1767339597711536263907838),true⟩,⟨(-2819090581846565268080602),2848917892031697160581206,true⟩⟩
  | 1,6 => ⟨⟨(-8025523687982942253776192),(-1897077083920695433908233),true⟩,⟨(-2818399455783336818036492),2981238095601061311439642,true⟩⟩
  | 1,7 => ⟨⟨(-8198357766527108765625166),(-1979590485314029288164487),true⟩,⟨(-2816054521976806623330780),3055253911387265636162311,true⟩⟩
  | 2,0 => ⟨⟨(-5136703402957430951526498),(-842718934180162760822224),true⟩,⟨(-2681100801985886667717215),1318083633596798246261995,true⟩⟩
  | 2,1 => ⟨⟨(-4854596510231639083643362),(-759956280163125052426040),true⟩,⟨(-2654835930393646558666347),1165845059150933562768778,true⟩⟩
  | 2,2 => ⟨⟨(-4639345048529684173626999),(-697937530339386590852084),true⟩,⟨(-2633712663759704248860529),1049008436619409594839050,true⟩⟩
  | 2,3 => ⟨⟨(-4513017374007481309905978),(-661891059183770250075192),true⟩,⟨(-2620905741424581885511264),980303617404372920506752,true⟩⟩
  | 2,4 => ⟨⟨(-5452442431036992458681930),(-937746267373426518837002),true⟩,⟨(-2708519701602488046499234),1497219196740631891447851,true⟩⟩
  | 2,5 => ⟨⟨(-5759397842360264386929781),(-1032896439643108827340891),true⟩,⟨(-2733105868339438614214885),1695768145807886735895487,true⟩⟩
  | 2,6 => ⟨⟨(-6010389427109344077530781),(-1113483512445391066613712),true⟩,⟨(-2751334802770391023171553),1856161419393033953925263,true⟩⟩
  | 2,7 => ⟨⟨(-6165001836942503404296341),(-1164538004215981844404320),true⟩,⟨(-2761660505906307138691638),1953744807552629710545281,true⟩⟩
  | 3,0 => ⟨⟨(-3652084101542667972862663),(-418959521934197002135564),true⟩,⟨(-2526270535164676647523718),514816698438072036171362,true⟩⟩
  | 3,1 => ⟨⟨(-3436514272868523646983051),(-357647696733069488715340),true⟩,⟨(-2500667286661897771256658),400576588574647582002435,true⟩⟩
  | 3,2 => ⟨⟨(-3273003655651387639516810),(-310647061749431024074227),true⟩,⟨(-2480732453745032378358286),315007960532753140308733,true⟩⟩
  | 3,3 => ⟨⟨(-3177365183543072603705860),(-282897113666339720409809),true⟩,⟨(-2468859655403764100375693),265469175190729785646210,true⟩⟩
  | 3,4 => ⟨⟨(-3895194104470374185389512),(-487555889444893937049133),true⟩,⟨(-2554238551400409529401529),645164064367494046181211,true⟩⟩
  | 3,5 => ⟨⟨(-4133409704072489986683228),(-554581583850478263023678),true⟩,⟨(-2580708914754213578474835),773968001730614549540792,true⟩⟩
  | 3,6 => ⟨⟨(-4330315668386511972175014),(-610100701746420463193333),true⟩,⟨(-2601872320747380050856680),880915305139891897303364,true⟩⟩
  | 3,7 => ⟨⟨(-4452667116733162831923407),(-644744454070197081033784),true⟩,⟨(-2614684409939601076191233),947469457144867367394503,true⟩⟩
  | 4,0 => ⟨⟨(-1213531836779720619942534),417497692336812333469108,true⟩,⟨(-2159264381314682075441154),(-492831173130895354032043),true⟩⟩
  | 4,1 => ⟨⟨(-847347583615669219772378),614167133811907099488914,true⟩,⟨(-2078647850425211170389248),(-557923707513113904644933),true⟩⟩
  | 4,2 => ⟨⟨(-596413268742202716914339),769810402360165625837120,true⟩,⟨(-2015914404891202513527967),(-581542667438009263044027),true⟩⟩
  | 4,3 => ⟨⟨(-456697543174160234808867),860197373994406414237885,true⟩,⟨(-1977888206053466691978814),(-589603753142507948786764),true⟩⟩
  | 4,4 => ⟨⟨(-1689821734820399146176557),217860497112541305226242,true⟩,⟨(-2249791837586880244164463),(-354591990481110640574123),true⟩⟩
  | 4,5 => ⟨⟨(-2215685585249013352706387),19752787481241883228591,true⟩,⟨(-2336585993186811754991355),(-173916608612153667717865),true⟩⟩
  | 4,6 => ⟨⟨(-2713564725434698708156498),(-144580156902413328359602),true⟩,⟨(-2408851792395143919100111),31916678729682325623273,true⟩⟩
  | 4,7 => ⟨⟨(-3064293017971221235156518),(-249794892366535996853250),true⟩,⟨(-2454612236598685586515469),207447390172526645954328,true⟩⟩
  | 5,0 => ⟨⟨867179186594800991202838,1926335129317097596744547,true⟩,⟨(-1478466804549445892072330),(-439245449330163479237389),true⟩⟩
  | 5,1 => ⟨⟨1108031729504045546722337,2150775268165484530004669,true⟩,⟨(-1353250258556956433409909),(-363549672674376340109260),true⟩⟩
  | 5,2 => ⟨⟨1276075470937014899050218,2307451244250355974959290,true⟩,⟨(-1258980867982453567390581),(-303678257808939609133475),true⟩⟩
  | 5,3 => ⟨⟨1368769744821047935382783,2393575427224571819836555,true⟩,⟨(-1204613395872737177792410),(-268435503085944268006678),true⟩⟩
  | 5,4 => ⟨⟨566912826826987261075074,1649516359884661544805233,true⟩,⟨(-1617663868338525908888894),(-514603055630518165290384),true⟩⟩
  | 5,5 => ⟨⟨238872403547526766325226,1354766684924454290506872,true⟩,⟨(-1747560472873461456836922),(-569652310155104205720733),true⟩⟩
  | 5,6 => ⟨⟨(-112605532375016062624070),1094088479320425727107596,true⟩,⟨(-1873553390717818532010157),(-592806469564885785894320),true⟩⟩
  | 5,7 => ⟨⟨(-359871436945651335524456),924402536873923082803309,true⟩,⟨(-1950119235740239286649689),(-592943452827288560367582),true⟩⟩
  | 6,0 => ⟨⟨2201779265265981979941752,3124555626425447047685787,true⟩,⟨(-653794668407546098760756),89364432680573973739752,true⟩⟩
  | 6,1 => ⟨⟨2323404736651793283740713,3218409308290012562172798,true⟩,⟨(-577980639770648792914374),132832981633470839832106,true⟩⟩
  | 6,2 => ⟨⟨2401682950245851933588570,3277963409550580344197945,true⟩,⟨(-540939053038873649767169),150657816710547295018832,true⟩⟩
  | 6,3 => ⟨⟨2443870593003498954994263,3310919174096401960659842,true⟩,⟨(-528375769375445828929970),154646251088576896495297,true⟩⟩
  | 6,4 => ⟨⟨2029237388239139318861007,2984138317512920132391827,true⟩,⟨(-772862922988362027501316),14392493621470678887309,true⟩⟩
  | 6,5 => ⟨⟨1813160643880461421851702,2797795230405291153746483,true⟩,⟨(-921682537232376026238686),(-82126058384010213208802),true⟩⟩
  | 6,6 => ⟨⟨1592048131275580620778917,2599074156200138596706373,true⟩,⟨(-1066928960600497934764688),(-177918091150759799638794),true⟩⟩
  | 6,7 => ⟨⟨1432436429866796659628454,2452508301575891374532256,true⟩,⟨(-1166312645764080376443327),(-243392703408425407130448),true⟩⟩
  | 7,0 => ⟨⟨2677238364307159065150867,3779290726671992080376696,true⟩,⟨(-797399040226110843169675),80377940716998059423974,true⟩⟩
  | 7,1 => ⟨⟨2779761904197217980512256,4024892051643470191791542,true⟩,⟨(-1030034420349469574853676),(-17841282744162500618297),true⟩⟩
  | 7,2 => ⟨⟨2883891801100403508366755,4292160306146268420810149,true⟩,⟨(-1316274823034835756847202),(-141852386979831421487372),true⟩⟩
  | 7,3 => ⟨⟨2956474289357080622922412,4494929543777760071501489,true⟩,⟨(-1555763365436151980207566),(-248025251159867043304227),true⟩⟩
  | 7,4 => ⟨⟨2594974163296615061646967,3592566576179767712806240,true⟩,⟨(-646952638178986196979350),138013757225446444025721,true⟩⟩
  | 7,5 => ⟨⟨2533552994755157101425311,3462911974656416643428032,true⟩,⟨(-567333774873890356782289),161041089311781449726274,true⟩⟩
  | 7,6 => ⟨⟨2488419262359864891550772,3377481633459078578850403,true⟩,⟨(-535214461660816201095111),162537175833685185866831,true⟩⟩
  | 7,7 => ⟨⟨2460322328867472772749506,3329601935626584954978551,true⟩,⟨(-527115132834742358490844),156916981503467639703471,true⟩⟩
  | 8,0 => ⟨⟨3192506415142976052287016,5672717437697303537807180,true⟩,⟨(-3463784755293272617051140),(-1119804495246918497472517),true⟩⟩
  | 8,1 => ⟨⟨3126606288081294925047429,6085293204367294392616865,true⟩,⟨(-4508321800990809366037033),(-1600153200772073059061375),true⟩⟩
  | 8,2 => ⟨⟨2932234663477866179992739,6388491857187096191677462,true⟩,⟨(-5628038184645602175844201),(-2110778326151227003745490),true⟩⟩
  | 8,3 => ⟨⟨2709974500693101906174681,6528880973504473896724903,true⟩,⟨(-6460242420142711773688260),(-2485662157295540879764957),true⟩⟩
  | 8,4 => ⟨⟨3158086344433365937745272,5261197261442621278935866,true⟩,⟨(-2670711769151145671689730),(-754802435567795087641148),true⟩⟩
  | 8,5 => ⟨⟨3087348300757057004081739,4928282431812507626804955,true⟩,⟨(-2140032011897852431894005),(-511937232371848585621385),true⟩⟩
  | 8,6 => ⟨⟨3023232122867537974307216,4700720730479558953895363,true⟩,⟨(-1820025011116473648223495),(-366738649609355308435006),true⟩⟩
  | 8,7 => ⟨⟨2984305893602151755132666,4577930826038953343648218,true⟩,⟨(-1659662537932710666928599),(-294538873319613333439575),true⟩⟩
  | 9,0 => ⟨⟨1837167989934100640812502,6564248176265214503859057,true⟩,⟨(-8584285575721244302644728),(-3417007684615417983902779),true⟩⟩
  | 9,1 => ⟨⟨1487182970512926622611888,6479367333343818343962646,true⟩,⟨(-9211044620513857827805059),(-3682804760252629851385318),true⟩⟩
  | 9,2 => ⟨⟨1162229918882571417710474,6372059903484993782574138,true⟩,⟨(-9726587858611066170766454),(-3897523416832370744024786),true⟩⟩
  | 9,3 => ⟨⟨943846870515839753463855,6287486487990471539919585,true⟩,⟨(-10043683684620068343318902),(-4027599039626418289845232),true⟩⟩
  | 9,4 => ⟨⟨2146898152495107570587283,6603846028362566169925419,true⟩,⟨(-7947995795490955807018630),(-3142521690326830417405085),true⟩⟩
  | 9,5 => ⟨⟨2382937146519795044119293,6602568561682308693930323,true⟩,⟨(-7391750884352133103541438),(-2899202173889996963174616),true⟩⟩
  | 9,6 => ⟨⟨2538778581847422834820238,6580701560708111983406197,true⟩,⟨(-6977318686299612455595622),(-2716092003661297144511192),true⟩⟩
  | 9,7 => ⟨⟨2620998693346508377249737,6560143451092861290899583,true⟩,⟨(-6738574524413335052417705),(-2609956991347103612368151),true⟩⟩
  | 10,0 => ⟨⟨(-1858883045940965058482157),5031186243917358720548494,true⟩,⟨(-12639242562049588330567637),(-4910576217037934681891426),true⟩⟩
  | 10,1 => ⟨⟨(-2934665590446727201476379),4434153874408080626138196,true⟩,⟨(-13287344723120993899441913),(-5081113313943797660519984),true⟩⟩
  | 10,2 => ⟨⟨(-3873240664472679897051954),3872512553854851718562715,true⟩,⟨(-13731494594088527822359125),(-5171603174261927310117008),true⟩⟩
  | 10,3 => ⟨⟨(-4472954515445958729098388),3495101993516153502592595,true⟩,⟨(-13958902999547028559930402),(-5202558846836372464617058),true⟩⟩
  | 10,4 => ⟨⟨(-846006146728178513037333),5541167123810375480364876,true⟩,⟨(-11878477701345859842002214),(-4677048591634049996188623),true⟩⟩
  | 10,5 => ⟨⟨(-30910761891781923134389),5907118412889023191078810,true⟩,⟨(-11142183548645999818685361),(-4428669022993966429119684),true⟩⟩
  | 10,6 => ⟨⟨517673718584057711628633,6130828998334631766175409,true⟩,⟨(-10557002269427744569228646),(-4219579662937496369459813),true⟩⟩
  | 10,7 => ⟨⟨815433086003747189170207,6240545381683319521109837,true⟩,⟨(-10207512378218037067417341),(-4090596517750591133787460),true⟩⟩
  | 11,0 => ⟨⟨(-6955486992544483831619255),1854848619155140782170202,true⟩,⟨(-14430107911858568835080530),(-5073910201099558489751931),true⟩⟩
  | 11,1 => ⟨⟨(-7648896490198637626173991),1428457708361616435331760,true⟩,⟨(-14415714174076502525460658),(-4931992094070670156587137),true⟩⟩
  | 11,2 => ⟨⟨(-8195016299143037651355628),1080205171010176993960501,true⟩,⟨(-14352500418920101296549815),(-4794783437699856016319336),true⟩⟩
  | 11,3 => ⟨⟨(-8520989292041442693361985),866547619930881195500855,true⟩,⟨(-14290797770814568460729133),(-4701203924031791528031859),true⟩⟩
  | 11,4 => ⟨⟨(-6215276228053981102738896),2318623489675733764605076,true⟩,⟨(-14371474615385836503773262),(-5175783171312326660951795),true⟩⟩
  | 11,5 => ⟨⟨(-5535828357240380521330238),2791656220103616393239411,true⟩,⟨(-14255100305518954375635574),(-5207022976883444157253967),true⟩⟩
  | 11,6 => ⟨⟨(-5008815157322922500541432),3145964333282193006932485,true⟩,⟨(-14125378905270378273731723),(-5212860318211115985557065),true⟩⟩
  | 11,7 => ⟨⟨(-4696859391181955539812213),3350579112723618124385988,true⟩,⟨(-14032680100108160290350988),(-5208850042249565670389693),true⟩⟩
  | 12,0 => ⟨⟨(-10769665071339213675120872),(-736489636350264376412259),true⟩,⟨(-13216490390358584532823869),(-3725075347264369842589326),true⟩⟩
  | 12,1 => ⟨⟨(-11352300569661176363836585),(-1164244072124262978830461),true⟩,⟨(-12715935565188879746719970),(-3308480045367934749363613),true⟩⟩
  | 12,2 => ⟨⟨(-11760897671566515024273809),(-1491031287813224689320479),true⟩,⟨(-12257053477634741326924472),(-2959724811660015257989160),true⟩⟩
  | 12,3 => ⟨⟨(-11981772779409648091246742),(-1681552383786500238603547),true⟩,⟨(-11954455492228152882983539),(-2742772880955573904824868),true⟩⟩
  | 12,4 => ⟨⟨(-10133863704787985479682321),(-265009668636543580272228),true⟩,⟨(-13656041005763607670242369),(-4079251185793464421426384),true⟩⟩
  | 12,5 => ⟨⟨(-9513672881726964796299646),184421874983864815903580,true⟩,⟨(-13974413743346489327894449),(-4354079196124569202634645),true⟩⟩
  | 12,6 => ⟨⟨(-8997390922346239691631461),545588889864071954973929,true⟩,⟨(-14164919506586675749256996),(-4547133717525872233738911),true⟩⟩
  | 12,7 => ⟨⟨(-8677825256166850060566339),762077118463593602625947,true⟩,⟨(-14254229673475343363976034),(-4652840040768894872165334),true⟩⟩
  | 13,0 => ⟨⟨(-12896574837187655260718325),(-2877594726910737638167074),true⟩,⟨(-9170813420252948413202021),(-1056511803032082299145266),true⟩⟩
  | 13,1 => ⟨⟨(-12892914928384745129039097),(-3121143802335527418874092),true⟩,⟨(-8270898504395113824649942),(-597193281167619398900407),true⟩⟩
  | 13,2 => ⟨⟨(-12806205035381131262762936),(-3281445679599252710190954),true⟩,⟨(-7537979051860129232556752),(-247853532107463174519136),true⟩⟩
  | 13,3 => ⟨⟨(-12722582309117676824420207),(-3363769666399081641503197),true⟩,⟨(-7091290223803775618997709),(-26049260230213698015082),true⟩⟩
  | 13,4 => ⟨⟨(-12769879403638662880851982),(-2568242286193039501190204),true⟩,⟨(-10088894955972620869332506),(-1563115168208577750322200),true⟩⟩
  | 13,5 => ⟨⟨(-12533950201139557431552371),(-2239049025578219337089525),true⟩,⟨(-10886638363302447932948150),(-2039327537023186553175494),true⟩⟩
  | 13,6 => ⟨⟨(-12270811884957984090404467),(-1953527357340546932892923),true⟩,⟨(-11470963217385565174511609),(-2413499299191685695745424),true⟩⟩
  | 13,7 => ⟨⟨(-12081505772254436104722433),(-1771955500751182972239228),true⟩,⟨(-11800845631547035259893431),(-2635999196805761203661644),true⟩⟩
  | 14,0 => ⟨⟨(-11333415337845956428721448),(-3637158007001082703817175),true⟩,⟨(-3831985804912769676344001),1705407563065422749036792,true⟩⟩
  | 14,1 => ⟨⟨(-10743200423767326380325343),(-3613347105037841949660410),true⟩,⟨(-3004218805182411345419069),2117889710122811790770397,true⟩⟩
  | 14,2 => ⟨⟨(-10232968025257822400852705),(-3555793825186141407468158),true⟩,⟨(-2390615375436699986650655),2392884507080882067190585,true⟩⟩
  | 14,3 => ⟨⟨(-9916474061915706235518537),(-3484934623973381033831242),true⟩,⟨(-2040676256452473407284121),2536484716320411591327956,true⟩⟩
  | 14,4 => ⟨⟨(-11881858916935918933310738),(-3616656307639735993074763),true⟩,⟨(-4773741110295712835766812),1184828045628396713303659,true⟩⟩
  | 14,5 => ⟨⟨(-12298064042703789916821513),(-3551102494162931836325353),true⟩,⟨(-5687686106785156269375698),682755736650580104540499,true⟩⟩
  | 14,6 => ⟨⟨(-12553758733832543177347222),(-3465798572238070184996248),true⟩,⟨(-6426106269190315308693154),320334801240066500644257,true⟩⟩
  | 14,7 => ⟨⟨(-12673893079596618544081435),(-3399776764208939475477533),true⟩,⟨(-6873980821259261596738238),88809180927531582764517,true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP487Value0_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 0 (0:Fin 8))=sharedDiskP487Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value0_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 0 (1:Fin 8))=sharedDiskP487Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value0_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 0 (2:Fin 8))=sharedDiskP487Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value0_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 0 (3:Fin 8))=sharedDiskP487Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value0_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 0 (4:Fin 8))=sharedDiskP487Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value0_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 0 (5:Fin 8))=sharedDiskP487Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value0_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 0 (6:Fin 8))=sharedDiskP487Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value0_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 0 (7:Fin 8))=sharedDiskP487Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 0 j)=sharedDiskP487Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value0_0
  · exact sharedDiskP487Value0_1
  · exact sharedDiskP487Value0_2
  · exact sharedDiskP487Value0_3
  · exact sharedDiskP487Value0_4
  · exact sharedDiskP487Value0_5
  · exact sharedDiskP487Value0_6
  · exact sharedDiskP487Value0_7
private theorem sharedDiskP487Value1_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 1 (0:Fin 8))=sharedDiskP487Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value1_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 1 (1:Fin 8))=sharedDiskP487Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value1_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 1 (2:Fin 8))=sharedDiskP487Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value1_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 1 (3:Fin 8))=sharedDiskP487Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value1_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 1 (4:Fin 8))=sharedDiskP487Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value1_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 1 (5:Fin 8))=sharedDiskP487Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value1_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 1 (6:Fin 8))=sharedDiskP487Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value1_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 1 (7:Fin 8))=sharedDiskP487Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 1 j)=sharedDiskP487Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value1_0
  · exact sharedDiskP487Value1_1
  · exact sharedDiskP487Value1_2
  · exact sharedDiskP487Value1_3
  · exact sharedDiskP487Value1_4
  · exact sharedDiskP487Value1_5
  · exact sharedDiskP487Value1_6
  · exact sharedDiskP487Value1_7
private theorem sharedDiskP487Value2_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 2 (0:Fin 8))=sharedDiskP487Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value2_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 2 (1:Fin 8))=sharedDiskP487Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value2_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 2 (2:Fin 8))=sharedDiskP487Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value2_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 2 (3:Fin 8))=sharedDiskP487Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value2_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 2 (4:Fin 8))=sharedDiskP487Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value2_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 2 (5:Fin 8))=sharedDiskP487Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value2_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 2 (6:Fin 8))=sharedDiskP487Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value2_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 2 (7:Fin 8))=sharedDiskP487Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 2 j)=sharedDiskP487Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value2_0
  · exact sharedDiskP487Value2_1
  · exact sharedDiskP487Value2_2
  · exact sharedDiskP487Value2_3
  · exact sharedDiskP487Value2_4
  · exact sharedDiskP487Value2_5
  · exact sharedDiskP487Value2_6
  · exact sharedDiskP487Value2_7
private theorem sharedDiskP487Value3_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 3 (0:Fin 8))=sharedDiskP487Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value3_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 3 (1:Fin 8))=sharedDiskP487Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value3_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 3 (2:Fin 8))=sharedDiskP487Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value3_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 3 (3:Fin 8))=sharedDiskP487Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value3_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 3 (4:Fin 8))=sharedDiskP487Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value3_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 3 (5:Fin 8))=sharedDiskP487Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value3_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 3 (6:Fin 8))=sharedDiskP487Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value3_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 3 (7:Fin 8))=sharedDiskP487Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 3 j)=sharedDiskP487Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value3_0
  · exact sharedDiskP487Value3_1
  · exact sharedDiskP487Value3_2
  · exact sharedDiskP487Value3_3
  · exact sharedDiskP487Value3_4
  · exact sharedDiskP487Value3_5
  · exact sharedDiskP487Value3_6
  · exact sharedDiskP487Value3_7
private theorem sharedDiskP487Value4_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 4 (0:Fin 8))=sharedDiskP487Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value4_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 4 (1:Fin 8))=sharedDiskP487Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value4_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 4 (2:Fin 8))=sharedDiskP487Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value4_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 4 (3:Fin 8))=sharedDiskP487Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value4_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 4 (4:Fin 8))=sharedDiskP487Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value4_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 4 (5:Fin 8))=sharedDiskP487Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value4_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 4 (6:Fin 8))=sharedDiskP487Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value4_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 4 (7:Fin 8))=sharedDiskP487Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 4 j)=sharedDiskP487Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value4_0
  · exact sharedDiskP487Value4_1
  · exact sharedDiskP487Value4_2
  · exact sharedDiskP487Value4_3
  · exact sharedDiskP487Value4_4
  · exact sharedDiskP487Value4_5
  · exact sharedDiskP487Value4_6
  · exact sharedDiskP487Value4_7
private theorem sharedDiskP487Value5_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 5 (0:Fin 8))=sharedDiskP487Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value5_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 5 (1:Fin 8))=sharedDiskP487Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value5_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 5 (2:Fin 8))=sharedDiskP487Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value5_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 5 (3:Fin 8))=sharedDiskP487Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value5_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 5 (4:Fin 8))=sharedDiskP487Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value5_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 5 (5:Fin 8))=sharedDiskP487Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value5_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 5 (6:Fin 8))=sharedDiskP487Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value5_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 5 (7:Fin 8))=sharedDiskP487Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 5 j)=sharedDiskP487Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value5_0
  · exact sharedDiskP487Value5_1
  · exact sharedDiskP487Value5_2
  · exact sharedDiskP487Value5_3
  · exact sharedDiskP487Value5_4
  · exact sharedDiskP487Value5_5
  · exact sharedDiskP487Value5_6
  · exact sharedDiskP487Value5_7
private theorem sharedDiskP487Value6_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 6 (0:Fin 8))=sharedDiskP487Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value6_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 6 (1:Fin 8))=sharedDiskP487Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value6_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 6 (2:Fin 8))=sharedDiskP487Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value6_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 6 (3:Fin 8))=sharedDiskP487Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value6_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 6 (4:Fin 8))=sharedDiskP487Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value6_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 6 (5:Fin 8))=sharedDiskP487Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value6_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 6 (6:Fin 8))=sharedDiskP487Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value6_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 6 (7:Fin 8))=sharedDiskP487Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 6 j)=sharedDiskP487Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value6_0
  · exact sharedDiskP487Value6_1
  · exact sharedDiskP487Value6_2
  · exact sharedDiskP487Value6_3
  · exact sharedDiskP487Value6_4
  · exact sharedDiskP487Value6_5
  · exact sharedDiskP487Value6_6
  · exact sharedDiskP487Value6_7
private theorem sharedDiskP487Value7_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 7 (0:Fin 8))=sharedDiskP487Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value7_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 7 (1:Fin 8))=sharedDiskP487Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value7_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 7 (2:Fin 8))=sharedDiskP487Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value7_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 7 (3:Fin 8))=sharedDiskP487Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value7_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 7 (4:Fin 8))=sharedDiskP487Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value7_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 7 (5:Fin 8))=sharedDiskP487Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value7_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 7 (6:Fin 8))=sharedDiskP487Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value7_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 7 (7:Fin 8))=sharedDiskP487Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 7 j)=sharedDiskP487Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value7_0
  · exact sharedDiskP487Value7_1
  · exact sharedDiskP487Value7_2
  · exact sharedDiskP487Value7_3
  · exact sharedDiskP487Value7_4
  · exact sharedDiskP487Value7_5
  · exact sharedDiskP487Value7_6
  · exact sharedDiskP487Value7_7
private theorem sharedDiskP487Value8_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 8 (0:Fin 8))=sharedDiskP487Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value8_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 8 (1:Fin 8))=sharedDiskP487Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value8_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 8 (2:Fin 8))=sharedDiskP487Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value8_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 8 (3:Fin 8))=sharedDiskP487Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value8_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 8 (4:Fin 8))=sharedDiskP487Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value8_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 8 (5:Fin 8))=sharedDiskP487Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value8_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 8 (6:Fin 8))=sharedDiskP487Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value8_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 8 (7:Fin 8))=sharedDiskP487Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 8 j)=sharedDiskP487Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value8_0
  · exact sharedDiskP487Value8_1
  · exact sharedDiskP487Value8_2
  · exact sharedDiskP487Value8_3
  · exact sharedDiskP487Value8_4
  · exact sharedDiskP487Value8_5
  · exact sharedDiskP487Value8_6
  · exact sharedDiskP487Value8_7
private theorem sharedDiskP487Value9_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 9 (0:Fin 8))=sharedDiskP487Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value9_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 9 (1:Fin 8))=sharedDiskP487Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value9_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 9 (2:Fin 8))=sharedDiskP487Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value9_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 9 (3:Fin 8))=sharedDiskP487Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value9_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 9 (4:Fin 8))=sharedDiskP487Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value9_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 9 (5:Fin 8))=sharedDiskP487Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value9_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 9 (6:Fin 8))=sharedDiskP487Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value9_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 9 (7:Fin 8))=sharedDiskP487Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 9 j)=sharedDiskP487Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value9_0
  · exact sharedDiskP487Value9_1
  · exact sharedDiskP487Value9_2
  · exact sharedDiskP487Value9_3
  · exact sharedDiskP487Value9_4
  · exact sharedDiskP487Value9_5
  · exact sharedDiskP487Value9_6
  · exact sharedDiskP487Value9_7
private theorem sharedDiskP487Value10_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 10 (0:Fin 8))=sharedDiskP487Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value10_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 10 (1:Fin 8))=sharedDiskP487Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value10_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 10 (2:Fin 8))=sharedDiskP487Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value10_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 10 (3:Fin 8))=sharedDiskP487Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value10_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 10 (4:Fin 8))=sharedDiskP487Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value10_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 10 (5:Fin 8))=sharedDiskP487Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value10_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 10 (6:Fin 8))=sharedDiskP487Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value10_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 10 (7:Fin 8))=sharedDiskP487Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 10 j)=sharedDiskP487Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value10_0
  · exact sharedDiskP487Value10_1
  · exact sharedDiskP487Value10_2
  · exact sharedDiskP487Value10_3
  · exact sharedDiskP487Value10_4
  · exact sharedDiskP487Value10_5
  · exact sharedDiskP487Value10_6
  · exact sharedDiskP487Value10_7
private theorem sharedDiskP487Value11_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 11 (0:Fin 8))=sharedDiskP487Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value11_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 11 (1:Fin 8))=sharedDiskP487Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value11_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 11 (2:Fin 8))=sharedDiskP487Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value11_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 11 (3:Fin 8))=sharedDiskP487Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value11_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 11 (4:Fin 8))=sharedDiskP487Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value11_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 11 (5:Fin 8))=sharedDiskP487Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value11_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 11 (6:Fin 8))=sharedDiskP487Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value11_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 11 (7:Fin 8))=sharedDiskP487Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 11 j)=sharedDiskP487Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value11_0
  · exact sharedDiskP487Value11_1
  · exact sharedDiskP487Value11_2
  · exact sharedDiskP487Value11_3
  · exact sharedDiskP487Value11_4
  · exact sharedDiskP487Value11_5
  · exact sharedDiskP487Value11_6
  · exact sharedDiskP487Value11_7
private theorem sharedDiskP487Value12_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 12 (0:Fin 8))=sharedDiskP487Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value12_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 12 (1:Fin 8))=sharedDiskP487Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value12_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 12 (2:Fin 8))=sharedDiskP487Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value12_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 12 (3:Fin 8))=sharedDiskP487Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value12_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 12 (4:Fin 8))=sharedDiskP487Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value12_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 12 (5:Fin 8))=sharedDiskP487Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value12_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 12 (6:Fin 8))=sharedDiskP487Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value12_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 12 (7:Fin 8))=sharedDiskP487Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 12 j)=sharedDiskP487Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value12_0
  · exact sharedDiskP487Value12_1
  · exact sharedDiskP487Value12_2
  · exact sharedDiskP487Value12_3
  · exact sharedDiskP487Value12_4
  · exact sharedDiskP487Value12_5
  · exact sharedDiskP487Value12_6
  · exact sharedDiskP487Value12_7
private theorem sharedDiskP487Value13_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 13 (0:Fin 8))=sharedDiskP487Values 13 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value13_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 13 (1:Fin 8))=sharedDiskP487Values 13 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value13_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 13 (2:Fin 8))=sharedDiskP487Values 13 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value13_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 13 (3:Fin 8))=sharedDiskP487Values 13 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value13_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 13 (4:Fin 8))=sharedDiskP487Values 13 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value13_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 13 (5:Fin 8))=sharedDiskP487Values 13 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value13_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 13 (6:Fin 8))=sharedDiskP487Values 13 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value13_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 13 (7:Fin 8))=sharedDiskP487Values 13 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values13_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 13 j)=sharedDiskP487Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value13_0
  · exact sharedDiskP487Value13_1
  · exact sharedDiskP487Value13_2
  · exact sharedDiskP487Value13_3
  · exact sharedDiskP487Value13_4
  · exact sharedDiskP487Value13_5
  · exact sharedDiskP487Value13_6
  · exact sharedDiskP487Value13_7
private theorem sharedDiskP487Value14_0 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 14 (0:Fin 8))=sharedDiskP487Values 14 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value14_1 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 14 (1:Fin 8))=sharedDiskP487Values 14 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value14_2 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 14 (2:Fin 8))=sharedDiskP487Values 14 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value14_3 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 14 (3:Fin 8))=sharedDiskP487Values 14 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value14_4 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 14 (4:Fin 8))=sharedDiskP487Values 14 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value14_5 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 14 (5:Fin 8))=sharedDiskP487Values 14 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value14_6 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 14 (6:Fin 8))=sharedDiskP487Values 14 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP487Value14_7 : truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 14 (7:Fin 8))=sharedDiskP487Values 14 (7:Fin 8) := by decide +kernel
theorem sharedDiskP487Values14_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points 14 j)=sharedDiskP487Values 14 j := by
  intro j
  fin_cases j
  · exact sharedDiskP487Value14_0
  · exact sharedDiskP487Value14_1
  · exact sharedDiskP487Value14_2
  · exact sharedDiskP487Value14_3
  · exact sharedDiskP487Value14_4
  · exact sharedDiskP487Value14_5
  · exact sharedDiskP487Value14_6
  · exact sharedDiskP487Value14_7
theorem sharedDiskP487Values_eq : ∀ (i : Fin 15) (j : Fin 8), truncatedChordCell 1 sharedDiskP487Params (sharedChord469Gauss8Points i j)=sharedDiskP487Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP487Values0_eq
  · exact sharedDiskP487Values1_eq
  · exact sharedDiskP487Values2_eq
  · exact sharedDiskP487Values3_eq
  · exact sharedDiskP487Values4_eq
  · exact sharedDiskP487Values5_eq
  · exact sharedDiskP487Values6_eq
  · exact sharedDiskP487Values7_eq
  · exact sharedDiskP487Values8_eq
  · exact sharedDiskP487Values9_eq
  · exact sharedDiskP487Values10_eq
  · exact sharedDiskP487Values11_eq
  · exact sharedDiskP487Values12_eq
  · exact sharedDiskP487Values13_eq
  · exact sharedDiskP487Values14_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP487Box : HorizontalRectangle := ⟨(123/200),(63/100),(869564008542899/1649267441664000),(885480886574489/1649267441664000),(367636760670855085152590140359829/649037107316853453566312041152512),(1612833100114794770881595604708635/324518553658426726783156020576256),(-1527267448740130172549988406609217/324518553658426726783156020576256),(-148411388349328332261689326376195/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP487Grid : CGrid := momentChordGrid sharedDiskP487Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984)
theorem sharedDiskP487Columns : containedInReported sharedDiskP487Grid.re sharedDiskP487Box.reLo sharedDiskP487Box.reHi=true ∧ containedInReported sharedDiskP487Grid.im sharedDiskP487Box.imLo sharedDiskP487Box.imHi=true := by
  rw [sharedDiskP487Grid,momentChordGrid_eq_tabulated sharedDiskP487Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984) sharedChord469Gauss8Points sharedChord469Gauss8Weights sharedDiskP487Values sharedChord469Gauss8Points_eq sharedChord469Gauss8Weights_eq sharedDiskP487Values_eq]
  decide +kernel
theorem sharedDiskP487Sound : sharedDiskP487Box.Sound := by
  intro t a tl tu al au
  change (((123/200):ℚ):ℝ)≤t at tl
  change t≤(((63/100):ℚ):ℝ) at tu
  change (((869564008542899/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((885480886574489/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP487Params_ok] at ps
  have band := sharedChord469ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((21/40):ℚ)≤(123/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((63/100):ℚ)≤(63/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3408482035145/6597069766656):ℚ)≤(869564008542899/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((885480886574489/1649267441664000):ℚ)≤(885480886574489/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord469Bd (by decide +kernel) (by decide +kernel) sharedChord469M (by decide +kernel) (sharedChord469Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP487Columns.1 sharedDiskP487Columns.2
def sharedDiskP487Rows : List SignRow := [positive_487.toSignRow, positive_488.toSignRow, positive_489.toSignRow]
theorem sharedDiskP487Rows_actual : ∀ r∈sharedDiskP487Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP487Rows.all (sharedDiskP487Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP487Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP482Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP484Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP487Rows_actual
