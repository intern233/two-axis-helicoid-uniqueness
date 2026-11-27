import TwoAxisHelicoid.PdfSharedChord521Rule12

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP522Params : ChordParams := ⟨⟨(-21537693856656346369431),(-20985244582004240566651),true⟩,⟨2097167693242890773234896,2129840713005931291238285,true⟩,⟨120271039343652971262986,123999086186238386490123,true⟩,⟨207623126890980559532081,213310965889889077826578,true⟩,⟨312980840667831907344462,317216206101915281371267,true⟩,⟨1166604411603411691782254,1167671448067554550193590,true⟩,⟨(-2366676156810054933799757),(-2349356313550462509332515),true⟩,⟨⟨1137413153369668384770797,1193469249404051446596106,true⟩,⟨(-3348867),3348867,true⟩⟩⟩
theorem sharedDiskP522Params_ok : chordParams (Grid.ofRats (31/40) (39/50)) (Grid.ofRats (932480001480701/1649267441664000) (938922452424701/1649267441664000))=sharedDiskP522Params := by decide +kernel
def sharedDiskP522Values (i : Fin 9) (j : Fin 12) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-2516200145549107370003219),(-1724125387721755460028589),true⟩,⟨(-730185636624428414666364),(-50793071152914968912786),true⟩⟩
  | 0,1 => ⟨⟨(-2586073580213140572283298),(-1776626808104158209792808),true⟩,⟨(-717594462291068043383798),(-25844928243561301980920),true⟩⟩
  | 0,2 => ⟨⟨(-2726502554231650688842520),(-1882706364293012068909845),true⟩,⟨(-692734523828180488674553),22931659001295320847895,true⟩⟩
  | 0,3 => ⟨⟨(-2935550598261713543708028),(-2042162116336562473238817),true⟩,⟨(-657004026623837234561823),91590590751897249417020,true⟩⟩
  | 0,4 => ⟨⟨(-3209187829305229108393408),(-2253999046087565656821434),true⟩,⟨(-612948072359678971780785),172832380296495260866799,true⟩⟩
  | 0,5 => ⟨⟨(-3539136660870677927939995),(-2514618759656165170476955),true⟩,⟨(-564587409823417874979103),256217436074125026973184,true⟩⟩
  | 0,6 => ⟨⟨(-3909433136414612331706854),(-2814246700983141837023762),true⟩,⟨(-517419416962221583836674),331984671204659280700595,true⟩⟩
  | 0,7 => ⟨⟨(-4291955139358366262817573),(-3131938750201176167047271),true⟩,⟨(-477564723073101826749259),390979987529613798681227,true⟩⟩
  | 0,8 => ⟨⟨(-4654641048528333780033389),(-3441337959651739198498968),true⟩,⟨(-448948316777190299936448),419941017986795104048527,true⟩⟩
  | 0,9 => ⟨⟨(-4964260456712736869515397),(-3711390386498266185772885),true⟩,⟨(-439160508105075655494763),423042161901142272297586,true⟩⟩
  | 0,10 => ⟨⟨(-5190599373139713710055335),(-3912075252114432072934760),true⟩,⟨(-440285404553916402981371),412468696852968827739770,true⟩⟩
  | 0,11 => ⟨⟨(-5308967179415313483729061),(-4018355945140010529480132),true⟩,⟨(-442911290764846963359665),402583656889805368286447,true⟩⟩
  | 1,0 => ⟨⟨(-1040831321354113411306624),(-619415142895761395569056),true⟩,⟨(-994144245097369259867631),(-595398933310504340190778),true⟩⟩
  | 1,1 => ⟨⟨(-1076940700179222072914812),(-646882507366879392630071),true⟩,⟨(-989059689657628124525467),(-583399508990293727123006),true⟩⟩
  | 1,2 => ⟨⟨(-1149036740675572742241154),(-701553678589702721339223),true⟩,⟨(-978457941563564309421790),(-558889716491897646148893),true⟩⟩
  | 1,3 => ⟨⟨(-1255435009834895285374384),(-781865563530341607482964),true⟩,⟨(-961832267269558245006947),(-521534129421732909354776),true⟩⟩
  | 1,4 => ⟨⟨(-1393660394519316645293421),(-885657708721561491773288),true⟩,⟨(-938777743487083984837576),(-471304308652211465557777),true⟩⟩
  | 1,5 => ⟨⟨(-1559896406547020481460591),(-1009898783025326964365433),true⟩,⟨(-909387832818400370495604),(-409110594427461294748741),true⟩⟩
  | 1,6 => ⟨⟨(-1747486035640709078986351),(-1149686671449288909329185),true⟩,⟨(-874754062797555928590806),(-337692708986127442386710),true⟩⟩
  | 1,7 => ⟨⟨(-1944240392672144877722346),(-1296258273440882963068021),true⟩,⟨(-837523507524203555614933),(-262642207190932263317674),true⟩⟩
  | 1,8 => ⟨⟨(-2135413767428585384742604),(-1439021073208996536266194),true⟩,⟨(-801107509820075450368255),(-190709076825017172950761),true⟩⟩
  | 1,9 => ⟨⟨(-2303392307875507502148184),(-1565018063336931675729009),true⟩,⟨(-769324523716798623498956),(-129069600245773166282131),true⟩⟩
  | 1,10 => ⟨⟨(-2430395934762838119854424),(-1659887770492456453486859),true⟩,⟨(-745823414762701677984688),(-82061815237447651783257),true⟩⟩
  | 1,11 => ⟨⟨(-2498239158092229015520076),(-1710658109973918495904152),true⟩,⟨(-733443705464291294969385),(-57282408163331202360477),true⟩⟩
  | 2,0 => ⟨⟨354465553238847672170985,588996024543341292356134,true⟩,⟨(-1033593543777966336670113),(-786234490952988256724918),true⟩⟩
  | 2,1 => ⟨⟨321915938414925687556253,556509227623274122766428,true⟩,⟨(-1037126127143989865635386),(-788880338580558223642499),true⟩⟩
  | 2,2 => ⟨⟨256159781087980729338719,492112168007422332495532,true⟩,⟨(-1044174663589482823375713),(-793309051788778266081471),true⟩⟩
  | 2,3 => ⟨⟨158029687940184313861340,398145529696026265887203,true⟩,⟨(-1053846746930529808371611),(-797660421592382617907344),true⟩⟩
  | 2,4 => ⟨⟨31147615785469241627346,279797795927117939557299,true⟩,⟨(-1063020725439058928589796),(-797904415376652561937670),true⟩⟩
  | 2,5 => ⟨⟨(-121954453881993646356634),142285004647333188919727,true⟩,⟨(-1068724168678183247849775),(-790109984429239847597957),true⟩⟩
  | 2,6 => ⟨⟨(-295414095441361481371237),(-10328863850277927456743),true⟩,⟨(-1068008333028761958810458),(-772468931801660006586135),true⟩⟩
  | 2,7 => ⟨⟨(-479185369224503105129073),(-167537385517505794405149),true⟩,⟨(-1059167326425534684772759),(-743783825149135348398060),true⟩⟩
  | 2,8 => ⟨⟨(-661047496009219507352783),(-319717000546675905872309),true⟩,⟨(-1042920266124879924621237),(-706022788004105050870474),true⟩⟩
  | 2,9 => ⟨⟨(-828473961704354491463408),(-453949531197473560917720),true⟩,⟨(-1023439538690674804757030),(-661152976880530178066534),true⟩⟩
  | 2,10 => ⟨⟨(-957120005832769877365475),(-555392784440593301326170),true⟩,⟨(-1005423924924232652238229),(-622415878839180214180982),true⟩⟩
  | 2,11 => ⟨⟨(-1026882515390482075659606),(-608788570569681295054403),true⟩,⟨(-996065623720868064598238),(-599981502275850888776444),true⟩⟩
  | 3,0 => ⟨⟨1774298147176385129969651,2062976026542605821170183,true⟩,⟨(-947873582178135072598629),(-680771057699650014121440),true⟩⟩
  | 3,1 => ⟨⟨1734224042494637017183099,2019365946440093856954614,true⟩,⟨(-937526609515901371616589),(-673336563675725981771385),true⟩⟩
  | 3,2 => ⟨⟨1656025509588491457481677,1934821533383391221736619,true⟩,⟨(-921721111010565164714718),(-662561676449470987040858),true⟩⟩
  | 3,3 => ⟨⟨1544462866247134646290545,1815239773470677660543626,true⟩,⟨(-908033963787279671223409),(-654805693930285104400171),true⟩⟩
  | 3,4 => ⟨⟨1404882717937065053193592,1667115668218489973348796,true⟩,⟨(-903167956117973566094570),(-655551845941261999748861),true⟩⟩
  | 3,5 => ⟨⟨1242772921112926145477111,1496837989782586081937253,true⟩,⟨(-910652827594547851878706),(-667418172664362861909051),true⟩⟩
  | 3,6 => ⟨⟨1064759968825168267957517,1311685644158355105834428,true⟩,⟨(-929991043604791693664979),(-689372065358749885056143),true⟩⟩
  | 3,7 => ⟨⟨881211977318478846733412,1122525620691533162094316,true⟩,⟨(-956799555279391945251440),(-716866306548022442785235),true⟩⟩
  | 3,8 => ⟨⟨704052080563115742605402,941522432436695377333301,true⟩,⟨(-984883507291264680259542),(-743930897624018471790695),true⟩⟩
  | 3,9 => ⟨⟨548060205661780666581814,783429840281611323025822,true⟩,⟨(-1008574941256829746494835),(-765468699758263926990981),true⟩⟩
  | 3,10 => ⟨⟨430319514844781270531646,664935870825605586228411,true⟩,⟨(-1024547570847113833142587),(-779062659760304346278472),true⟩⟩
  | 3,11 => ⟨⟨367066019787714269119072,601588419188002270943017,true⟩,⟨(-1032167645652441624548817),(-785138526238230982478632),true⟩⟩
  | 4,0 => ⟨⟨2828232635808901143716405,3533040422652860252815204,true⟩,⟨(-2924496079716225302853300),(-2217940906350909468412351),true⟩⟩
  | 4,1 => ⟨⟨2819579230988237594383650,3494316230434183180400426,true⟩,⟨(-2751161479554522162866748),(-2079249629509648737522163),true⟩⟩
  | 4,2 => ⟨⟨2784488102866399408489876,3406344409221137273259072,true⟩,⟨(-2452379545433335875024417),(-1840527805513834420919830),true⟩⟩
  | 4,3 => ⟨⟨2707202682025000754630416,3265318048673139543256749,true⟩,⟨(-2104569056587046106785568),(-1563571505422899023326598),true⟩⟩
  | 4,4 => ⟨⟨2588452862978568945118931,3082789609024134036706952,true⟩,⟨(-1773935734102727971718917),(-1301989251310507432094800),true⟩⟩
  | 4,5 => ⟨⟨2442408623423120279190207,2879806127208037877763981,true⟩,⟨(-1498579757541027951684008),(-1086501807017824545672776),true⟩⟩
  | 4,6 => ⟨⟨2286909900967654008217157,2677234435127557238512659,true⟩,⟨(-1290531448591869909758005),(-926446369996319766609082),true⟩⟩
  | 4,7 => ⟨⟨2138075693159237823894865,2491847663180313743700791,true⟩,⟨(-1146090655346131455050991),(-818126193034725861718973),true⟩⟩
  | 4,8 => ⟨⟨2006378996565647209420703,2333042603966340292523831,true⟩,⟨(-1052280804214397472271813),(-750302335736143781746897),true⟩⟩
  | 4,9 => ⟨⟨1899399654422562122158613,2207047704655163841260583,true⟩,⟨(-995458397229862680159870),(-711206998269076203393882),true⟩⟩
  | 4,10 => ⟨⟨1823647253782780005417208,2119267622485529312255185,true⟩,⟨(-964321921069560648483974),(-691028390658946015132077),true⟩⟩
  | 4,11 => ⟨⟨1784571468929151908518636,2074445185804980531252467,true⟩,⟨(-950935196572518208055859),(-682794310298077587699876),true⟩⟩
  | 5,0 => ⟨⟨2465561866569392028295708,3471057417931294146901458,true⟩,⟨(-4747706712911259173325837),(-3676460414629199781168475),true⟩⟩
  | 5,1 => ⟨⟨2497218854909578711251747,3490453423093047085297593,true⟩,⟨(-4671200956252365459593559),(-3615466443233511449566780),true⟩⟩
  | 5,2 => ⟨⟨2553275466309686605246178,3523130081057083735456961,true⟩,⟨(-4525650786287046863127287),(-3499341862333360045890348),true⟩⟩
  | 5,3 => ⟨⟨2621058984599142250613950,3558932620508352213353679,true⟩,⟨(-4327355856631539695880028),(-3340975016826936114793949),true⟩⟩
  | 5,4 => ⟨⟨2687840508443529205974071,3588246003111347781519961,true⟩,⟨(-4096393706826661473155639),(-3156321664142901421534232),true⟩⟩
  | 5,5 => ⟨⟨2744238586813530439564810,3604923205782701519407701,true⟩,⟨(-3853399377058053622444704),(-2961869706172562913988816),true⟩⟩
  | 5,6 => ⟨⟨2785495282769308025207250,3607276219463050170923244,true⟩,⟨(-3617543754846893672891202),(-2773008591564790805417327),true⟩⟩
  | 5,7 => ⟨⟨2811143029057107251524791,3597686240773554995921014,true⟩,⟨(-3406003957003243796865390),(-2603563460167306862890066),true⟩⟩
  | 5,8 => ⟨⟨2824216772788641670172116,3580989644552773467088335,true⟩,⟨(-3229030789142043347190299),(-2461801082976971290687595),true⟩⟩
  | 5,9 => ⟨⟨2828962095066514160299192,3562580452518939237139307,true⟩,⟨(-3092607093366457156419011),(-2352537408570257926530677),true⟩⟩
  | 5,10 => ⟨⟨2829475305975859724681310,3547310043793368634284138,true⟩,⟨(-3000273873053946742944318),(-2278603579089837838470997),true⟩⟩
  | 5,11 => ⟨⟨2828898804273799622172602,3538805424616709484934169,true⟩,⟨(-2954108509655010640532158),(-2241644839424410656315140),true⟩⟩
  | 6,0 => ⟨⟨193013567983887083296022,1639973067088293162004190,true⟩,⟨(-7217712761955287585520308),(-5587566752489585765295953),true⟩⟩
  | 6,1 => ⟨⟨326568220660339620846060,1754980537423603811156685,true⟩,⟨(-7143819005020761308375112),(-5534775198393968223483936),true⟩⟩
  | 6,2 => ⟨⟨573263089697294102341353,1965562304923185714495125,true⟩,⟨(-6993397565355718548638903),(-5425895336008475588342092),true⟩⟩
  | 6,3 => ⟨⟨893107970339011143594607,2234593555455980505756221,true⟩,⟨(-6768857179361227253287504),(-5260647758159022172123634),true⟩⟩
  | 6,4 => ⟨⟨1239409217668186191317496,2520938667429611411003403,true⟩,⟨(-6481826208560610028722285),(-5045339739836122195189541),true⟩⟩
  | 6,5 => ⟨⟨1559193515496458017186422,2789442687258506837833122,true⟩,⟨(-6160678057785163840627355),(-4794613765190548980768882),true⟩⟩
  | 6,6 => ⟨⟨1839790016093961743170715,3016511041908791919753697,true⟩,⟨(-5823820126064250669081359),(-4529894753606822841017606),true⟩⟩
  | 6,7 => ⟨⟨2065089407058830692839050,3190893180159991319273392,true⟩,⟨(-5502970223754056054272928),(-4276490896534730765117965),true⟩⟩
  | 6,8 => ⟨⟨2233490449024598322901819,3314731133555032256437035,true⟩,⟨(-5222475951081202380027287),(-4054150964649261762562003),true⟩⟩
  | 6,9 => ⟨⟨2350323123143958319702497,3396060097015768969552397,true⟩,⟨(-4999537220597354676656006),(-3876986681920222210544622),true⟩⟩
  | 6,10 => ⟨⟨2422788226134301898638173,3443952369086794819968576,true⟩,⟨(-4845634940340851042049164),(-3754484661223433254445459),true⟩⟩
  | 6,11 => ⟨⟨2456978005537481399845615,3465696388029551630578275,true⟩,⟨(-4767835121631375981073029),(-3692502281157204975581888),true⟩⟩
  | 7,0 => ⟨⟨(-5088191424866429230081673),(-3006195531243941412448445),true⟩,⟨(-6690578698509379422652890),(-4738036329653966584671996),true⟩⟩
  | 7,1 => ⟨⟨(-4921098334145844572383499),(-2846611843530951173183317),true⟩,⟨(-6835773724097746248584969),(-4868908201683252138011416),true⟩⟩
  | 7,2 => ⟨⟨(-4580318245736270388540109),(-2525825318795320154867212),true⟩,⟨(-7088408155979009160686073),(-5100989899740270951945373),true⟩⟩
  | 7,3 => ⟨⟨(-4071469224035783896418526),(-2056024271850282813269945),true⟩,⟨(-7378103653479386654988194),(-5377241382671195871686749),true⟩⟩
  | 7,4 => ⟨⟨(-3422710491984277970731907),(-1469269241820928969173281),true⟩,⟨(-7627677380998868360051981),(-5632895174460265939182922),true⟩⟩
  | 7,5 => ⟨⟨(-2689113672331120398613377),(-818895463876601664065066),true⟩,⟨(-7778184099017280141778835),(-5815302848960425944697507),true⟩⟩
  | 7,6 => ⟨⟨(-1943997002611772875225403),(-170589548964703957870864),true⟩,⟨(-7806450229704032830664583),(-5899151340739865268696860),true⟩⟩
  | 7,7 => ⟨⟨(-1263509678152751729621555),414251555192336450275692,true⟩,⟨(-7729071434472725952481353),(-5891375519388158615519234),true⟩⟩
  | 7,8 => ⟨⟨(-696372280341275851244340),894939304460369286052205,true⟩,⟨(-7588813053835806029468075),(-5822773343708427947663965),true⟩⟩
  | 7,9 => ⟨⟨(-266531915921305705392495),1254126164299580341400769,true⟩,⟨(-7434130139123265842472876),(-5731044048342777192445680),true⟩⟩
  | 7,10 => ⟨⟨18284923913656019546776,1489536055264092018562407,true⟩,⟨(-7306870345211868094851986),(-5649918478862079182575839),true⟩⟩
  | 7,11 => ⟨⟨157442101156906919899322,1609229225616632716251856,true⟩,⟨(-7236542339154387736753994),(-5600932583031972843007159),true⟩⟩
  | 8,0 => ⟨⟨(-5330848650227460043624480),(-4048772502607721345463672),true⟩,⟨(-344652182450390105488144),370264908887508005373140,true⟩⟩
  | 8,1 => ⟨⟨(-5468962421084717407162566),(-4135725970433332608165042),true⟩,⟨(-516387022630698686275144),232621485039842940754658,true⟩⟩
  | 8,2 => ⟨⟨(-5720094652393569943270875),(-4287578214917233350314729),true⟩,⟨(-875618975694795525396691),(-47977755210522928475994),true⟩⟩
  | 8,3 => ⟨⟨(-6025399542882371514134579),(-4458795192874391356760270),true⟩,⟨(-1434931755798785917672343),(-464006958179553027011347),true⟩⟩
  | 8,4 => ⟨⟨(-6300880087487379949300820),(-4585568420353272273616950),true⟩,⟨(-2186549497457596286284363),(-1035800760077425543823877),true⟩⟩
  | 8,5 => ⟨⟨(-6455421025823567577443622),(-4602471494493895126098609),true⟩,⟨(-3082295115307166578312866),(-1740525223370490420596683),true⟩⟩
  | 8,6 => ⟨⟨(-6435595631141728442994713),(-4468779314144842440462823),true⟩,⟨(-4028956978154698559665856),(-2497057478637350849935578),true⟩⟩
  | 8,7 => ⟨⟨(-6239031733980158302007517),(-4195318421659873438306628),true⟩,⟨(-4907373284353626425874963),(-3212808413465098524150910),true⟩⟩
  | 8,8 => ⟨⟨(-5922031882408182845674586),(-3840320146643194657758274),true⟩,⟨(-5630523271716560946634573),(-3817316930279499812318962),true⟩⟩
  | 8,9 => ⟨⟨(-5575529066411616675746095),(-3483599969833387005557990),true⟩,⟨(-6159097277622920149741312),(-4270071466200203930253457),true⟩⟩
  | 8,10 => ⟨⟨(-5289370226869683638372659),(-3200808369182492801062862),true⟩,⟨(-6493198447529221149009783),(-4562427987807752752189580),true⟩⟩
  | 8,11 => ⟨⟨(-5130722085559290081363324),(-3047096706660587389382257),true⟩,⟨(-6651039077079068340601222),(-4702659608278535530602575),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP522Value0_0 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (0:Fin 12))=sharedDiskP522Values 0 (0:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_1 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (1:Fin 12))=sharedDiskP522Values 0 (1:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_2 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (2:Fin 12))=sharedDiskP522Values 0 (2:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_3 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (3:Fin 12))=sharedDiskP522Values 0 (3:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_4 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (4:Fin 12))=sharedDiskP522Values 0 (4:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_5 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (5:Fin 12))=sharedDiskP522Values 0 (5:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_6 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (6:Fin 12))=sharedDiskP522Values 0 (6:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_7 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (7:Fin 12))=sharedDiskP522Values 0 (7:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_8 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (8:Fin 12))=sharedDiskP522Values 0 (8:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_9 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (9:Fin 12))=sharedDiskP522Values 0 (9:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_10 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (10:Fin 12))=sharedDiskP522Values 0 (10:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value0_11 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 (11:Fin 12))=sharedDiskP522Values 0 (11:Fin 12) := by decide +kernel
theorem sharedDiskP522Values0_eq : ∀ j : Fin 12, truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 0 j)=sharedDiskP522Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP522Value0_0
  · exact sharedDiskP522Value0_1
  · exact sharedDiskP522Value0_2
  · exact sharedDiskP522Value0_3
  · exact sharedDiskP522Value0_4
  · exact sharedDiskP522Value0_5
  · exact sharedDiskP522Value0_6
  · exact sharedDiskP522Value0_7
  · exact sharedDiskP522Value0_8
  · exact sharedDiskP522Value0_9
  · exact sharedDiskP522Value0_10
  · exact sharedDiskP522Value0_11
private theorem sharedDiskP522Value1_0 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (0:Fin 12))=sharedDiskP522Values 1 (0:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_1 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (1:Fin 12))=sharedDiskP522Values 1 (1:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_2 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (2:Fin 12))=sharedDiskP522Values 1 (2:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_3 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (3:Fin 12))=sharedDiskP522Values 1 (3:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_4 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (4:Fin 12))=sharedDiskP522Values 1 (4:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_5 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (5:Fin 12))=sharedDiskP522Values 1 (5:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_6 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (6:Fin 12))=sharedDiskP522Values 1 (6:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_7 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (7:Fin 12))=sharedDiskP522Values 1 (7:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_8 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (8:Fin 12))=sharedDiskP522Values 1 (8:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_9 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (9:Fin 12))=sharedDiskP522Values 1 (9:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_10 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (10:Fin 12))=sharedDiskP522Values 1 (10:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value1_11 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 (11:Fin 12))=sharedDiskP522Values 1 (11:Fin 12) := by decide +kernel
theorem sharedDiskP522Values1_eq : ∀ j : Fin 12, truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 1 j)=sharedDiskP522Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP522Value1_0
  · exact sharedDiskP522Value1_1
  · exact sharedDiskP522Value1_2
  · exact sharedDiskP522Value1_3
  · exact sharedDiskP522Value1_4
  · exact sharedDiskP522Value1_5
  · exact sharedDiskP522Value1_6
  · exact sharedDiskP522Value1_7
  · exact sharedDiskP522Value1_8
  · exact sharedDiskP522Value1_9
  · exact sharedDiskP522Value1_10
  · exact sharedDiskP522Value1_11
private theorem sharedDiskP522Value2_0 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (0:Fin 12))=sharedDiskP522Values 2 (0:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_1 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (1:Fin 12))=sharedDiskP522Values 2 (1:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_2 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (2:Fin 12))=sharedDiskP522Values 2 (2:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_3 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (3:Fin 12))=sharedDiskP522Values 2 (3:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_4 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (4:Fin 12))=sharedDiskP522Values 2 (4:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_5 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (5:Fin 12))=sharedDiskP522Values 2 (5:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_6 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (6:Fin 12))=sharedDiskP522Values 2 (6:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_7 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (7:Fin 12))=sharedDiskP522Values 2 (7:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_8 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (8:Fin 12))=sharedDiskP522Values 2 (8:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_9 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (9:Fin 12))=sharedDiskP522Values 2 (9:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_10 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (10:Fin 12))=sharedDiskP522Values 2 (10:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value2_11 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 (11:Fin 12))=sharedDiskP522Values 2 (11:Fin 12) := by decide +kernel
theorem sharedDiskP522Values2_eq : ∀ j : Fin 12, truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 2 j)=sharedDiskP522Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP522Value2_0
  · exact sharedDiskP522Value2_1
  · exact sharedDiskP522Value2_2
  · exact sharedDiskP522Value2_3
  · exact sharedDiskP522Value2_4
  · exact sharedDiskP522Value2_5
  · exact sharedDiskP522Value2_6
  · exact sharedDiskP522Value2_7
  · exact sharedDiskP522Value2_8
  · exact sharedDiskP522Value2_9
  · exact sharedDiskP522Value2_10
  · exact sharedDiskP522Value2_11
private theorem sharedDiskP522Value3_0 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (0:Fin 12))=sharedDiskP522Values 3 (0:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_1 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (1:Fin 12))=sharedDiskP522Values 3 (1:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_2 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (2:Fin 12))=sharedDiskP522Values 3 (2:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_3 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (3:Fin 12))=sharedDiskP522Values 3 (3:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_4 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (4:Fin 12))=sharedDiskP522Values 3 (4:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_5 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (5:Fin 12))=sharedDiskP522Values 3 (5:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_6 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (6:Fin 12))=sharedDiskP522Values 3 (6:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_7 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (7:Fin 12))=sharedDiskP522Values 3 (7:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_8 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (8:Fin 12))=sharedDiskP522Values 3 (8:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_9 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (9:Fin 12))=sharedDiskP522Values 3 (9:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_10 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (10:Fin 12))=sharedDiskP522Values 3 (10:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value3_11 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 (11:Fin 12))=sharedDiskP522Values 3 (11:Fin 12) := by decide +kernel
theorem sharedDiskP522Values3_eq : ∀ j : Fin 12, truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 3 j)=sharedDiskP522Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP522Value3_0
  · exact sharedDiskP522Value3_1
  · exact sharedDiskP522Value3_2
  · exact sharedDiskP522Value3_3
  · exact sharedDiskP522Value3_4
  · exact sharedDiskP522Value3_5
  · exact sharedDiskP522Value3_6
  · exact sharedDiskP522Value3_7
  · exact sharedDiskP522Value3_8
  · exact sharedDiskP522Value3_9
  · exact sharedDiskP522Value3_10
  · exact sharedDiskP522Value3_11
private theorem sharedDiskP522Value4_0 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (0:Fin 12))=sharedDiskP522Values 4 (0:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_1 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (1:Fin 12))=sharedDiskP522Values 4 (1:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_2 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (2:Fin 12))=sharedDiskP522Values 4 (2:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_3 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (3:Fin 12))=sharedDiskP522Values 4 (3:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_4 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (4:Fin 12))=sharedDiskP522Values 4 (4:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_5 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (5:Fin 12))=sharedDiskP522Values 4 (5:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_6 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (6:Fin 12))=sharedDiskP522Values 4 (6:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_7 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (7:Fin 12))=sharedDiskP522Values 4 (7:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_8 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (8:Fin 12))=sharedDiskP522Values 4 (8:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_9 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (9:Fin 12))=sharedDiskP522Values 4 (9:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_10 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (10:Fin 12))=sharedDiskP522Values 4 (10:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value4_11 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 (11:Fin 12))=sharedDiskP522Values 4 (11:Fin 12) := by decide +kernel
theorem sharedDiskP522Values4_eq : ∀ j : Fin 12, truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 4 j)=sharedDiskP522Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP522Value4_0
  · exact sharedDiskP522Value4_1
  · exact sharedDiskP522Value4_2
  · exact sharedDiskP522Value4_3
  · exact sharedDiskP522Value4_4
  · exact sharedDiskP522Value4_5
  · exact sharedDiskP522Value4_6
  · exact sharedDiskP522Value4_7
  · exact sharedDiskP522Value4_8
  · exact sharedDiskP522Value4_9
  · exact sharedDiskP522Value4_10
  · exact sharedDiskP522Value4_11
private theorem sharedDiskP522Value5_0 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (0:Fin 12))=sharedDiskP522Values 5 (0:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_1 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (1:Fin 12))=sharedDiskP522Values 5 (1:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_2 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (2:Fin 12))=sharedDiskP522Values 5 (2:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_3 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (3:Fin 12))=sharedDiskP522Values 5 (3:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_4 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (4:Fin 12))=sharedDiskP522Values 5 (4:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_5 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (5:Fin 12))=sharedDiskP522Values 5 (5:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_6 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (6:Fin 12))=sharedDiskP522Values 5 (6:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_7 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (7:Fin 12))=sharedDiskP522Values 5 (7:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_8 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (8:Fin 12))=sharedDiskP522Values 5 (8:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_9 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (9:Fin 12))=sharedDiskP522Values 5 (9:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_10 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (10:Fin 12))=sharedDiskP522Values 5 (10:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value5_11 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 (11:Fin 12))=sharedDiskP522Values 5 (11:Fin 12) := by decide +kernel
theorem sharedDiskP522Values5_eq : ∀ j : Fin 12, truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 5 j)=sharedDiskP522Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP522Value5_0
  · exact sharedDiskP522Value5_1
  · exact sharedDiskP522Value5_2
  · exact sharedDiskP522Value5_3
  · exact sharedDiskP522Value5_4
  · exact sharedDiskP522Value5_5
  · exact sharedDiskP522Value5_6
  · exact sharedDiskP522Value5_7
  · exact sharedDiskP522Value5_8
  · exact sharedDiskP522Value5_9
  · exact sharedDiskP522Value5_10
  · exact sharedDiskP522Value5_11
private theorem sharedDiskP522Value6_0 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (0:Fin 12))=sharedDiskP522Values 6 (0:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_1 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (1:Fin 12))=sharedDiskP522Values 6 (1:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_2 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (2:Fin 12))=sharedDiskP522Values 6 (2:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_3 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (3:Fin 12))=sharedDiskP522Values 6 (3:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_4 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (4:Fin 12))=sharedDiskP522Values 6 (4:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_5 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (5:Fin 12))=sharedDiskP522Values 6 (5:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_6 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (6:Fin 12))=sharedDiskP522Values 6 (6:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_7 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (7:Fin 12))=sharedDiskP522Values 6 (7:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_8 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (8:Fin 12))=sharedDiskP522Values 6 (8:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_9 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (9:Fin 12))=sharedDiskP522Values 6 (9:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_10 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (10:Fin 12))=sharedDiskP522Values 6 (10:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value6_11 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 (11:Fin 12))=sharedDiskP522Values 6 (11:Fin 12) := by decide +kernel
theorem sharedDiskP522Values6_eq : ∀ j : Fin 12, truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 6 j)=sharedDiskP522Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP522Value6_0
  · exact sharedDiskP522Value6_1
  · exact sharedDiskP522Value6_2
  · exact sharedDiskP522Value6_3
  · exact sharedDiskP522Value6_4
  · exact sharedDiskP522Value6_5
  · exact sharedDiskP522Value6_6
  · exact sharedDiskP522Value6_7
  · exact sharedDiskP522Value6_8
  · exact sharedDiskP522Value6_9
  · exact sharedDiskP522Value6_10
  · exact sharedDiskP522Value6_11
private theorem sharedDiskP522Value7_0 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (0:Fin 12))=sharedDiskP522Values 7 (0:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_1 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (1:Fin 12))=sharedDiskP522Values 7 (1:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_2 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (2:Fin 12))=sharedDiskP522Values 7 (2:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_3 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (3:Fin 12))=sharedDiskP522Values 7 (3:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_4 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (4:Fin 12))=sharedDiskP522Values 7 (4:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_5 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (5:Fin 12))=sharedDiskP522Values 7 (5:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_6 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (6:Fin 12))=sharedDiskP522Values 7 (6:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_7 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (7:Fin 12))=sharedDiskP522Values 7 (7:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_8 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (8:Fin 12))=sharedDiskP522Values 7 (8:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_9 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (9:Fin 12))=sharedDiskP522Values 7 (9:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_10 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (10:Fin 12))=sharedDiskP522Values 7 (10:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value7_11 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 (11:Fin 12))=sharedDiskP522Values 7 (11:Fin 12) := by decide +kernel
theorem sharedDiskP522Values7_eq : ∀ j : Fin 12, truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 7 j)=sharedDiskP522Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP522Value7_0
  · exact sharedDiskP522Value7_1
  · exact sharedDiskP522Value7_2
  · exact sharedDiskP522Value7_3
  · exact sharedDiskP522Value7_4
  · exact sharedDiskP522Value7_5
  · exact sharedDiskP522Value7_6
  · exact sharedDiskP522Value7_7
  · exact sharedDiskP522Value7_8
  · exact sharedDiskP522Value7_9
  · exact sharedDiskP522Value7_10
  · exact sharedDiskP522Value7_11
private theorem sharedDiskP522Value8_0 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (0:Fin 12))=sharedDiskP522Values 8 (0:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_1 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (1:Fin 12))=sharedDiskP522Values 8 (1:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_2 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (2:Fin 12))=sharedDiskP522Values 8 (2:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_3 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (3:Fin 12))=sharedDiskP522Values 8 (3:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_4 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (4:Fin 12))=sharedDiskP522Values 8 (4:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_5 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (5:Fin 12))=sharedDiskP522Values 8 (5:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_6 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (6:Fin 12))=sharedDiskP522Values 8 (6:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_7 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (7:Fin 12))=sharedDiskP522Values 8 (7:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_8 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (8:Fin 12))=sharedDiskP522Values 8 (8:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_9 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (9:Fin 12))=sharedDiskP522Values 8 (9:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_10 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (10:Fin 12))=sharedDiskP522Values 8 (10:Fin 12) := by decide +kernel
private theorem sharedDiskP522Value8_11 : truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 (11:Fin 12))=sharedDiskP522Values 8 (11:Fin 12) := by decide +kernel
theorem sharedDiskP522Values8_eq : ∀ j : Fin 12, truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points 8 j)=sharedDiskP522Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP522Value8_0
  · exact sharedDiskP522Value8_1
  · exact sharedDiskP522Value8_2
  · exact sharedDiskP522Value8_3
  · exact sharedDiskP522Value8_4
  · exact sharedDiskP522Value8_5
  · exact sharedDiskP522Value8_6
  · exact sharedDiskP522Value8_7
  · exact sharedDiskP522Value8_8
  · exact sharedDiskP522Value8_9
  · exact sharedDiskP522Value8_10
  · exact sharedDiskP522Value8_11
theorem sharedDiskP522Values_eq : ∀ (i : Fin 9) (j : Fin 12), truncatedChordCell 2 sharedDiskP522Params (sharedChord521Rule12Points i j)=sharedDiskP522Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP522Values0_eq
  · exact sharedDiskP522Values1_eq
  · exact sharedDiskP522Values2_eq
  · exact sharedDiskP522Values3_eq
  · exact sharedDiskP522Values4_eq
  · exact sharedDiskP522Values5_eq
  · exact sharedDiskP522Values6_eq
  · exact sharedDiskP522Values7_eq
  · exact sharedDiskP522Values8_eq

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP522Values_eq
