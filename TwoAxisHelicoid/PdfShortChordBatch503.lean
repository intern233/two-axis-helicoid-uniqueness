import TwoAxisHelicoid.PdfSharedChord493Gauss8
import TwoAxisHelicoid.PdfSharedChord493Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP503Params : ChordParams := ⟨⟨(-14031821289093377397294),(-13160373309931296876964),true⟩,⟨2410842609718200290747352,2494443586278576077330903,true⟩,⟨99494873177266436207917,107277144479270645163995,true⟩,⟨153566257407441428728840,164561642300592123110216,true⟩,⟨249374570418667534524873,257682342750395931059760,true⟩,⟨1181184170214462155547114,1182888515237481524076016,true⟩,⟨(-2673491992435834643461398),(-2631772703320787361121861),true⟩,⟨⟨1126256146616936314772386,1238994220792959820204042,true⟩,⟨(-35707),35707,true⟩⟩⟩
theorem sharedDiskP503Params_ok : chordParams (Grid.ofRats (139/200) (141/200)) (Grid.ofRats (896432009617469/1649267441664000) (182238814541941/329853488332800))=sharedDiskP503Params := by decide +kernel
def sharedDiskP503Values (i : Fin 13) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-5546216654268543343452474),(-2751071238027912902632169),true⟩,⟨(-1152391978464411590597555),1087560286503994006312936,true⟩⟩
  | 0,1 => ⟨⟨(-5141391055250084813016638),(-2481934885913111342850244),true⟩,⟨(-1195430536369927346013323),987537894533041538283206,true⟩⟩
  | 0,2 => ⟨⟨(-4833710863985871791242183),(-2285806853119247439472537),true⟩,⟨(-1227359946231285348098960),891873984535168234470800,true⟩⟩
  | 0,3 => ⟨⟨(-4653967764897489533897539),(-2174473915689876797408672),true⟩,⟨(-1245360765814773234458226),828912627056048576876242,true⟩⟩
  | 0,4 => ⟨⟨(-5999141224001157628447030),(-3065467371257587980492541),true⟩,⟨(-1124176870078786384536830),1160661428599660354535921,true⟩⟩
  | 0,5 => ⟨⟨(-6436757555104057040304631),(-3383509188040519290970217),true⟩,⟨(-1101772840226495307942105),1188612336394795245315670,true⟩⟩
  | 0,6 => ⟨⟨(-6792411884307582878556964),(-3655563655085931961749513),true⟩,⟨(-1088096729350962847520460),1178361027292111056984119,true⟩⟩
  | 0,7 => ⟨⟨(-7010210328347412140315104),(-3829437075306691584844840),true⟩,⟨(-1082144921021401749598408),1156931733841122160766626,true⟩⟩
  | 1,0 => ⟨⟨(-3461008102071771930122134),(-1486186240490910310325491),true⟩,⟨(-1350626231126086896046335),368665180928332167713172,true⟩⟩
  | 1,1 => ⟨⟨(-3174199341133131413698445),(-1331593899455527355329385),true⟩,⟨(-1371590207513647253449455),245807051203069223748304,true⟩⟩
  | 1,2 => ⟨⟨(-2960623687001162605983273),(-1218417583859155345531909),true⟩,⟨(-1385911024064217104839074),151613816776961864725208,true⟩⟩
  | 1,3 => ⟨⟨(-2837394045152579870695600),(-1153717357514138073021174),true⟩,⟨(-1393632640728094642563223),96535378524550346192490,true⟩⟩
  | 1,4 => ⟨⟨(-3790886149552193941200748),(-1668583409056018015300860),true⟩,⟨(-1324252024522605473189772),502891020529549220085801,true⟩⟩
  | 1,5 => ⟨⟨(-4119805554272588122214711),(-1856272703230451184735474),true⟩,⟨(-1295723296743833451108296),627039184466771297224335,true⟩⟩
  | 1,6 => ⟨⟨(-4395490991734389349661456),(-2018355956445878889635594),true⟩,⟨(-1270305434142211638311464),730136865739938011895575,true⟩⟩
  | 1,7 => ⟨⟨(-4568375764396199131713087),(-2122267365060863688176151),true⟩,⟨(-1253747975358334542947594),797235737955082144622786,true⟩⟩
  | 2,0 => ⟨⟨(-2048271101333938816638356),(-738719518149382617979264),true⟩,⟨(-1431889070074314146529268),(-238480923585368872624703),true⟩⟩
  | 2,1 => ⟨⟨(-1863943564051841575926456),(-639701762564137601567341),true⟩,⟨(-1437078239124532013489301),(-309205458820754603823818),true⟩⟩
  | 2,2 => ⟨⟨(-1726406130748305095559147),(-564424820949906811717217),true⟩,⟨(-1440913989434780648378197),(-360535361864101028392902),true⟩⟩
  | 2,3 => ⟨⟨(-1646811610059591374350351),(-519315821321557491857869),true⟩,⟨(-1444303728032497174835965),(-389433241926858163913462),true⟩⟩
  | 2,4 => ⟨⟨(-2260551529640665941361209),(-852199116251467399546205),true⟩,⟨(-1423780167144929293135913),(-155274155916959771530521),true⟩⟩
  | 2,5 => ⟨⟨(-2476374921516025914968220),(-965882390763055283172614),true⟩,⟨(-1413704938217386576964017),(-65220188252029204139068),true⟩⟩
  | 2,6 => ⟨⟨(-2661915534483080912908500),(-1062167332858204306269530),true⟩,⟨(-1403889508898749795353192),17537724867809142987676,true⟩⟩
  | 2,7 => ⟨⟨(-2779072588678729853689862),(-1123222620548127685770683),true⟩,⟨(-1397140792927543121836157),70336721380464447330313,true⟩⟩
  | 3,0 => ⟨⟨(-1121526869737685328806528),(-211379276005839203768124),true⟩,⟨(-1453968566714497475870481),(-562347145866938809634287),true⟩⟩
  | 3,1 => ⟨⟨(-993286454406311046628109),(-132918932472656577191155),true⟩,⟨(-1452055424583338713861494),(-598514182374431547380584),true⟩⟩
  | 3,2 => ⟨⟨(-896496525855885617791332),(-72711471481505877812268),true⟩,⟨(-1449234218679735135800496),(-623878682720279311943706),true⟩⟩
  | 3,3 => ⟨⟨(-840191481161584550654773),(-37166735450603264214408),true⟩,⟨(-1447036209265953237054808),(-637699045364387645419076),true⟩⟩
  | 3,4 => ⟨⟨(-1267379012089355503020779),(-298913491701995033204195),true⟩,⟨(-1453865846679154557452891),(-517991151292439131099218),true⟩⟩
  | 3,5 => ⟨⟨(-1411967965314489795189498),(-384054240984075936642926),true⟩,⟨(-1451656248192394486587994),(-471026646547924097122854),true⟩⟩
  | 3,6 => ⟨⟨(-1533025958297836172622100),(-454210780616952312067253),true⟩,⟨(-1448395606089993149626913),(-429707924398746655284980),true⟩⟩
  | 3,7 => ⟨⟨(-1609058777682043083042895),(-497798856052701298761356),true⟩,⟨(-1445764039613685154201430),(-402938272507209967391667),true⟩⟩
  | 4,0 => ⟨⟨300085875109014632198918,861274605353941209033562,true⟩,⟨(-1285347181137015293361933),(-690115384464345322515065),true⟩⟩
  | 4,1 => ⟨⟨514909589601850357014449,1072649887816387374833055,true⟩,⟨(-1228550677103607194937352),(-652319378285867014316957),true⟩⟩
  | 4,2 => ⟨⟨669206304573328279307209,1226405751159194228788615,true⟩,⟨(-1181096067388244366983723),(-617124469315217775987937),true⟩⟩
  | 4,3 => ⟨⟨756351981725353039498204,1313849286238793630134295,true⟩,⟨(-1152150207501519127674968),(-594629042395987696272797),true⟩⟩
  | 4,4 => ⟨⟨19202045586566604646344,609868739577790739384651,true⟩,⟨(-1350394400482247842529714),(-716302852171768533064082),true⟩⟩
  | 4,5 => ⟨⟨(-293274356182060588054489),351416104632715517247192,true⟩,⟨(-1402525051609052180850092),(-716692566086528496433541),true⟩⟩
  | 4,6 => ⟨⟨(-581089704804839629745784),141680699758966143686485,true⟩,⟨(-1432667715673019543368266),(-684071609112615061092619),true⟩⟩
  | 4,7 => ⟨⟨(-776883352968682965509315),5291436249258407308196,true⟩,⟨(-1444528728385161845925426),(-650388222693385377741493),true⟩⟩
  | 5,0 => ⟨⟨1682346700511479123898323,2261645142108052153939946,true⟩,⟨(-817402374593736875882010),(-305694588347731046702801),true⟩⟩
  | 5,1 => ⟨⟨1868061809247464034389148,2457163228717474221052032,true⟩,⟨(-775285920311578231610272),(-263682509141666264926748),true⟩⟩
  | 5,2 => ⟨⟨2003113264874683527233909,2602428435824776533694730,true⟩,⟨(-763275930272052682198017),(-247197169625445066613673),true⟩⟩
  | 5,3 => ⟨⟨2081362441803424916168766,2688419830385051676225404,true⟩,⟨(-766251324323365770426263),(-245123396217161332856293),true⟩⟩
  | 5,4 => ⟨⟨1454630684805860988036280,2025571753284194293806671,true⟩,⟨(-892386330303593119704403),(-374391294255124276180374),true⟩⟩
  | 5,5 => ⟨⟨1205143635189713111555576,1769385042729717427516508,true⟩,⟨(-986534101309885628684519),(-457107070535092083124651),true⟩⟩
  | 5,6 => ⟨⟨974116662311969839717417,1533931632076538024426186,true⟩,⟨(-1074373455729507046068167),(-531556727211075146491550),true⟩⟩
  | 5,7 => ⟨⟨817210965211333351321501,1375144143261729241746140,true⟩,⟨(-1131128416197548572205773),(-577917626269927106115031),true⟩⟩
  | 6,0 => ⟨⟨2626000429629082612341391,3503778797569183433695315,true⟩,⟨(-1214775839097552181122813),(-444850888036878018680653),true⟩⟩
  | 6,1 => ⟨⟨2800415438202776824581695,3825321296188341843192914,true⟩,⟨(-1561264310341327167407920),(-641937462384399914978455),true⟩⟩
  | 6,2 => ⟨⟨2940611691616616494206238,4126586428623454388444090,true⟩,⟨(-1977780753587465233958674),(-888100567377581348748533),true⟩⟩
  | 6,3 => ⟨⟨3017450943991941319950025,4327765704213281686537219,true⟩,⟨(-2318214276048447250175088),(-1093000276405899648298509),true⟩⟩
  | 6,4 => ⟨⟨2453078990980295485524666,3218378873841636577824072,true⟩,⟨(-984457627724081790648248),(-323436860791240466093107),true⟩⟩
  | 6,5 => ⟨⟨2302906259911451110748146,2990809950605718928389749,true⟩,⟨(-855256367553646747958614),(-265333643383954186812112),true⟩⟩
  | 6,6 => ⟨⟨2187218232727106464478169,2826797392095608788577841,true⟩,⟨(-794535404099234563428318),(-246687881705796909370958),true⟩⟩
  | 6,7 => ⟨⟨2117076303131138594760368,2731785306946921607335606,true⟩,⟨(-772146018804486629771270),(-244987440289578873919033),true⟩⟩
  | 7,0 => ⟨⟨3100600097561073913908975,4758643738475703700824838,true⟩,⟨(-3331872914040566206133276),(-1711800006573917909498596),true⟩⟩
  | 7,1 => ⟨⟨3087245517616923428242255,4860056011439064406290861,true⟩,⟨(-3681698401055027549279314),(-1926665814173998274985318),true⟩⟩
  | 7,2 => ⟨⟨3059246633220453101931221,4932294781297201563407435,true⟩,⟨(-3992183370752181242593648),(-2117508949811759857787626),true⟩⟩
  | 7,3 => ⟨⟨3033027935491242043499840,4970841946676551247201473,true⟩,⟨(-4195013839678547863122795),(-2242177069296912526249344),true⟩⟩
  | 7,4 => ⟨⟨3094603869432470326647955,4642672493093275654949816,true⟩,⟨(-3003060838647255169347426),(-1510222067847398355480999),true⟩⟩
  | 7,5 => ⟨⟨3075389354859192817697991,4531770524661621251996097,true⟩,⟨(-2734364332804767287320603),(-1345976719869808402441877),true⟩⟩
  | 7,6 => ⟨⟨3053415776619268259208396,4443770273782621801955938,true⟩,⟨(-2544303429987313704620201),(-1230180800003916062570740),true⟩⟩
  | 7,7 => ⟨⟨3037960693757369310761612,4391058826819717647187602,true⟩,⟨(-2438447279506056531193525),(-1165864886518156552240197),true⟩⟩
  | 8,0 => ⟨⟨2474943731250849379675222,5010451019755948705770656,true⟩,⟨(-6130942170732232380906041),(-3425640235227192413161078),true⟩⟩
  | 8,1 => ⟨⟨2140292983221439377839687,4878971146847791542207518,true⟩,⟨(-6808514790011321052926579),(-3834426606572000070028733),true⟩⟩
  | 8,2 => ⟨⟨1791991608033521767631806,4700394710500061347109245,true⟩,⟨(-7379440814703404875272483),(-4175374765687061629707332),true⟩⟩
  | 8,3 => ⟨⟨1540327087886618238784236,4553620280413152888932003,true⟩,⟨(-7733849986134508884170814),(-4384998202417396254727169),true⟩⟩
  | 8,4 => ⟨⟨2729208244277797303798473,5063684562447057856454270,true⟩,⟨(-5468799931323508166452393),(-3022852354248848368012301),true⟩⟩
  | 8,5 => ⟨⟨2890659941584664005806401,5054593029458056346179546,true⟩,⟨(-4915125639924520589168530),(-2684205947091662913079830),true⟩⟩
  | 8,6 => ⟨⟨2978382248602359640962087,5018685638789137537071515,true⟩,⟨(-4519231032167064538708221),(-2441346739470778908710129),true⟩⟩
  | 8,7 => ⟨⟨3017377830861219446405091,4987840386800715753482352,true⟩,⟨(-4297877392396383183902178),(-2305386050707630757333943),true⟩⟩
  | 9,0 => ⟨⟨108172752849882751716723,3634813526228875614642271,true⟩,⟨(-9150713824894744731547936),(-5164062541913436898974944),true⟩⟩
  | 9,1 => ⟨⟨(-422888195102766920470315),3270852338132605437408252,true⟩,⟨(-9515420342764766550636593),(-5346043406654210413806567),true⟩⟩
  | 9,2 => ⟨⟨(-885186119243848288373201),2942962429490914897479442,true⟩,⟨(-9783925874709575473482460),(-5473337529704519808322629),true⟩⟩
  | 9,3 => ⟨⟨(-1181176043300261867303828),2727722714522472297730384,true⟩,⟨(-9934347081853339132832119),(-5541137708424833959259649),true⟩⟩
  | 9,4 => ⟨⟨609901156450575602884845,3966739263008137389419650,true⟩,⟨(-8738843374003523252172899),(-4949742099944260365847102),true⟩⟩
  | 9,5 => ⟨⟨1023426499125132304786011,4225883134068139846912750,true⟩,⟨(-8344947417614602220670207),(-4738339714810161311092911),true⟩⟩
  | 9,6 => ⟨⟨1295049361160724585253337,4399633454826470767994635,true⟩,⟨(-8042919523758192242797927),(-4566269628938299727104768),true⟩⟩
  | 9,7 => ⟨⟨1440247050143470570556526,4491972010349868770993842,true⟩,⟨(-7863912151131007834166679),(-4461469373067739235851937),true⟩⟩
  | 10,0 => ⟨⟨(-3748483055290719107477995),841081931087663858901691,true⟩,⟨(-10609601177077889289178510),(-5663810730082059635389648),true⟩⟩
  | 10,1 => ⟨⟨(-4542659591818986497194947),246180610460014734202740,true⟩,⟨(-10593999889470878047605351),(-5541064188363935927291073),true⟩⟩
  | 10,2 => ⟨⟨(-5176416184443346737640535),(-239935432728867177990713),true⟩,⟨(-10497488271235736883101950),(-5389546802076028372180211),true⟩⟩
  | 10,3 => ⟨⟨(-5555778452968822072971160),(-535729470832172016671498),true⟩,⟨(-10400007191562550713828872),(-5273710767618711048699158),true⟩⟩
  | 10,4 => ⟨⟨(-2922523848983515890365062),1439097375725852750570133,true⟩,⟨(-10511549817393690408791214),(-5718092461626709690177024),true⟩⟩
  | 10,5 => ⟨⟨(-2190808013975335472749746),1965421202090136157631235,true⟩,⟨(-10330892461454060978334345),(-5698323626960102461745630),true⟩⟩
  | 10,6 => ⟨⟨(-1643837365740721194625959),2383602268152040860946440,true⟩,⟨(-10137836196523199715332870),(-5626987028515673563110433),true⟩⟩
  | 10,7 => ⟨⟨(-1329378406294232538323724),2618486894282150913693245,true⟩,⟨(-10003651838864494141176259),(-5571258214697612851158482),true⟩⟩
  | 11,0 => ⟨⟨(-8007327431789173525778676),(-2658210901422039638448066),true⟩,⟨(-8648358167017418319703430),(-3825999274794424042814883),true⟩⟩
  | 11,1 => ⟨⟨(-8461612542290290086390427),(-3147967083402132351083774),true⟩,⟨(-7845073194895561416070906),(-3263265263501429167405773),true⟩⟩
  | 11,2 => ⟨⟨(-8730226300439519412308458),(-3478918650852082015439232),true⟩,⟨(-7130253355924429444449764),(-2769083673915800064156201),true⟩⟩
  | 11,3 => ⟨⟨(-8853271836021304841943365),(-3650363688611581925376064),true⟩,⟨(-6671865743340277474370681),(-2448326619599475442756256),true⟩⟩
  | 11,4 => ⟨⟨(-7381352023935581821996518),(-2063762122613481003549441),true⟩,⟨(-9365354608851906813202398),(-4362476942608168607137301),true⟩⟩
  | 11,5 => ⟨⟨(-6698037940748350798465097),(-1466458492812537358810641),true⟩,⟨(-9886997946825019573074785),(-4787154011070784420292658),true⟩⟩
  | 11,6 => ⟨⟨(-6108134245750490199489244),(-977387055769078664608531),true⟩,⟨(-10197497726226210560684658),(-5066931470355099556489572),true⟩⟩
  | 11,7 => ⟨⟨(-5738078747262397689910302),(-679968053699141949052030),true⟩,⟨(-10341549517228974466557891),(-5210726893895966297481090),true⟩⟩
  | 12,0 => ⟨⟨(-8448912873639771962365777),(-4171081109353867297229191),true⟩,⟨(-3016519191700672604860296),(-197297608326782026587379),true⟩⟩
  | 12,1 => ⟨⟨(-7966304082500747214781094),(-4082860417092208502979808),true⟩,⟨(-2072218682187480583372482),361810293079564814750387,true⟩⟩
  | 12,2 => ⟨⟨(-7498297560818328747258119),(-3953883644896312012832739),true⟩,⟨(-1391607902143987761821672),807842447639863156246209,true⟩⟩
  | 12,3 => ⟨⟨(-7188164254023484945508367),(-3852740876646226754236837),true⟩,⟨(-1015407300152811703087534),1040042265514935143867727,true⟩⟩
  | 12,4 => ⟨⟨(-8807942575069814423248412),(-4158196526099813139241367),true⟩,⟨(-4102621916329617255172803),(-812486876515630423515222),true⟩⟩
  | 12,5 => ⟨⟨(-8965279594853373858907054),(-4036361873331388010782063),true⟩,⟨(-5144162834109378024701934),(-1444435312369790762010971),true⟩⟩
  | 12,6 => ⟨⟨(-8958853747149176664431583),(-3862623554805304367701245),true⟩,⟨(-5962088193035292237998580),(-1970063211110972055713913),true⟩⟩
  | 12,7 => ⟨⟨(-8898054158993385598755233),(-3725433826178435769910617),true⟩,⟨(-6443260600987352066001968),(-2291932850849427206621105),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP503Value0_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 0 (0:Fin 8))=sharedDiskP503Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value0_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 0 (1:Fin 8))=sharedDiskP503Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value0_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 0 (2:Fin 8))=sharedDiskP503Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value0_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 0 (3:Fin 8))=sharedDiskP503Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value0_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 0 (4:Fin 8))=sharedDiskP503Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value0_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 0 (5:Fin 8))=sharedDiskP503Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value0_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 0 (6:Fin 8))=sharedDiskP503Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value0_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 0 (7:Fin 8))=sharedDiskP503Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 0 j)=sharedDiskP503Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value0_0
  · exact sharedDiskP503Value0_1
  · exact sharedDiskP503Value0_2
  · exact sharedDiskP503Value0_3
  · exact sharedDiskP503Value0_4
  · exact sharedDiskP503Value0_5
  · exact sharedDiskP503Value0_6
  · exact sharedDiskP503Value0_7
private theorem sharedDiskP503Value1_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 1 (0:Fin 8))=sharedDiskP503Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value1_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 1 (1:Fin 8))=sharedDiskP503Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value1_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 1 (2:Fin 8))=sharedDiskP503Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value1_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 1 (3:Fin 8))=sharedDiskP503Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value1_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 1 (4:Fin 8))=sharedDiskP503Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value1_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 1 (5:Fin 8))=sharedDiskP503Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value1_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 1 (6:Fin 8))=sharedDiskP503Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value1_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 1 (7:Fin 8))=sharedDiskP503Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 1 j)=sharedDiskP503Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value1_0
  · exact sharedDiskP503Value1_1
  · exact sharedDiskP503Value1_2
  · exact sharedDiskP503Value1_3
  · exact sharedDiskP503Value1_4
  · exact sharedDiskP503Value1_5
  · exact sharedDiskP503Value1_6
  · exact sharedDiskP503Value1_7
private theorem sharedDiskP503Value2_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 2 (0:Fin 8))=sharedDiskP503Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value2_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 2 (1:Fin 8))=sharedDiskP503Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value2_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 2 (2:Fin 8))=sharedDiskP503Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value2_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 2 (3:Fin 8))=sharedDiskP503Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value2_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 2 (4:Fin 8))=sharedDiskP503Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value2_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 2 (5:Fin 8))=sharedDiskP503Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value2_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 2 (6:Fin 8))=sharedDiskP503Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value2_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 2 (7:Fin 8))=sharedDiskP503Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 2 j)=sharedDiskP503Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value2_0
  · exact sharedDiskP503Value2_1
  · exact sharedDiskP503Value2_2
  · exact sharedDiskP503Value2_3
  · exact sharedDiskP503Value2_4
  · exact sharedDiskP503Value2_5
  · exact sharedDiskP503Value2_6
  · exact sharedDiskP503Value2_7
private theorem sharedDiskP503Value3_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 3 (0:Fin 8))=sharedDiskP503Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value3_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 3 (1:Fin 8))=sharedDiskP503Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value3_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 3 (2:Fin 8))=sharedDiskP503Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value3_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 3 (3:Fin 8))=sharedDiskP503Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value3_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 3 (4:Fin 8))=sharedDiskP503Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value3_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 3 (5:Fin 8))=sharedDiskP503Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value3_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 3 (6:Fin 8))=sharedDiskP503Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value3_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 3 (7:Fin 8))=sharedDiskP503Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 3 j)=sharedDiskP503Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value3_0
  · exact sharedDiskP503Value3_1
  · exact sharedDiskP503Value3_2
  · exact sharedDiskP503Value3_3
  · exact sharedDiskP503Value3_4
  · exact sharedDiskP503Value3_5
  · exact sharedDiskP503Value3_6
  · exact sharedDiskP503Value3_7
private theorem sharedDiskP503Value4_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 4 (0:Fin 8))=sharedDiskP503Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value4_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 4 (1:Fin 8))=sharedDiskP503Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value4_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 4 (2:Fin 8))=sharedDiskP503Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value4_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 4 (3:Fin 8))=sharedDiskP503Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value4_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 4 (4:Fin 8))=sharedDiskP503Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value4_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 4 (5:Fin 8))=sharedDiskP503Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value4_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 4 (6:Fin 8))=sharedDiskP503Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value4_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 4 (7:Fin 8))=sharedDiskP503Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 4 j)=sharedDiskP503Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value4_0
  · exact sharedDiskP503Value4_1
  · exact sharedDiskP503Value4_2
  · exact sharedDiskP503Value4_3
  · exact sharedDiskP503Value4_4
  · exact sharedDiskP503Value4_5
  · exact sharedDiskP503Value4_6
  · exact sharedDiskP503Value4_7
private theorem sharedDiskP503Value5_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 5 (0:Fin 8))=sharedDiskP503Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value5_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 5 (1:Fin 8))=sharedDiskP503Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value5_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 5 (2:Fin 8))=sharedDiskP503Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value5_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 5 (3:Fin 8))=sharedDiskP503Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value5_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 5 (4:Fin 8))=sharedDiskP503Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value5_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 5 (5:Fin 8))=sharedDiskP503Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value5_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 5 (6:Fin 8))=sharedDiskP503Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value5_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 5 (7:Fin 8))=sharedDiskP503Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 5 j)=sharedDiskP503Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value5_0
  · exact sharedDiskP503Value5_1
  · exact sharedDiskP503Value5_2
  · exact sharedDiskP503Value5_3
  · exact sharedDiskP503Value5_4
  · exact sharedDiskP503Value5_5
  · exact sharedDiskP503Value5_6
  · exact sharedDiskP503Value5_7
private theorem sharedDiskP503Value6_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 6 (0:Fin 8))=sharedDiskP503Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value6_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 6 (1:Fin 8))=sharedDiskP503Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value6_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 6 (2:Fin 8))=sharedDiskP503Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value6_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 6 (3:Fin 8))=sharedDiskP503Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value6_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 6 (4:Fin 8))=sharedDiskP503Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value6_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 6 (5:Fin 8))=sharedDiskP503Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value6_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 6 (6:Fin 8))=sharedDiskP503Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value6_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 6 (7:Fin 8))=sharedDiskP503Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 6 j)=sharedDiskP503Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value6_0
  · exact sharedDiskP503Value6_1
  · exact sharedDiskP503Value6_2
  · exact sharedDiskP503Value6_3
  · exact sharedDiskP503Value6_4
  · exact sharedDiskP503Value6_5
  · exact sharedDiskP503Value6_6
  · exact sharedDiskP503Value6_7
private theorem sharedDiskP503Value7_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 7 (0:Fin 8))=sharedDiskP503Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value7_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 7 (1:Fin 8))=sharedDiskP503Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value7_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 7 (2:Fin 8))=sharedDiskP503Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value7_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 7 (3:Fin 8))=sharedDiskP503Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value7_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 7 (4:Fin 8))=sharedDiskP503Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value7_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 7 (5:Fin 8))=sharedDiskP503Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value7_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 7 (6:Fin 8))=sharedDiskP503Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value7_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 7 (7:Fin 8))=sharedDiskP503Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 7 j)=sharedDiskP503Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value7_0
  · exact sharedDiskP503Value7_1
  · exact sharedDiskP503Value7_2
  · exact sharedDiskP503Value7_3
  · exact sharedDiskP503Value7_4
  · exact sharedDiskP503Value7_5
  · exact sharedDiskP503Value7_6
  · exact sharedDiskP503Value7_7
private theorem sharedDiskP503Value8_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 8 (0:Fin 8))=sharedDiskP503Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value8_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 8 (1:Fin 8))=sharedDiskP503Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value8_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 8 (2:Fin 8))=sharedDiskP503Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value8_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 8 (3:Fin 8))=sharedDiskP503Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value8_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 8 (4:Fin 8))=sharedDiskP503Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value8_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 8 (5:Fin 8))=sharedDiskP503Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value8_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 8 (6:Fin 8))=sharedDiskP503Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value8_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 8 (7:Fin 8))=sharedDiskP503Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 8 j)=sharedDiskP503Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value8_0
  · exact sharedDiskP503Value8_1
  · exact sharedDiskP503Value8_2
  · exact sharedDiskP503Value8_3
  · exact sharedDiskP503Value8_4
  · exact sharedDiskP503Value8_5
  · exact sharedDiskP503Value8_6
  · exact sharedDiskP503Value8_7
private theorem sharedDiskP503Value9_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 9 (0:Fin 8))=sharedDiskP503Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value9_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 9 (1:Fin 8))=sharedDiskP503Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value9_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 9 (2:Fin 8))=sharedDiskP503Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value9_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 9 (3:Fin 8))=sharedDiskP503Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value9_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 9 (4:Fin 8))=sharedDiskP503Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value9_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 9 (5:Fin 8))=sharedDiskP503Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value9_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 9 (6:Fin 8))=sharedDiskP503Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value9_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 9 (7:Fin 8))=sharedDiskP503Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values9_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 9 j)=sharedDiskP503Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value9_0
  · exact sharedDiskP503Value9_1
  · exact sharedDiskP503Value9_2
  · exact sharedDiskP503Value9_3
  · exact sharedDiskP503Value9_4
  · exact sharedDiskP503Value9_5
  · exact sharedDiskP503Value9_6
  · exact sharedDiskP503Value9_7
private theorem sharedDiskP503Value10_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 10 (0:Fin 8))=sharedDiskP503Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value10_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 10 (1:Fin 8))=sharedDiskP503Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value10_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 10 (2:Fin 8))=sharedDiskP503Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value10_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 10 (3:Fin 8))=sharedDiskP503Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value10_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 10 (4:Fin 8))=sharedDiskP503Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value10_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 10 (5:Fin 8))=sharedDiskP503Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value10_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 10 (6:Fin 8))=sharedDiskP503Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value10_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 10 (7:Fin 8))=sharedDiskP503Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values10_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 10 j)=sharedDiskP503Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value10_0
  · exact sharedDiskP503Value10_1
  · exact sharedDiskP503Value10_2
  · exact sharedDiskP503Value10_3
  · exact sharedDiskP503Value10_4
  · exact sharedDiskP503Value10_5
  · exact sharedDiskP503Value10_6
  · exact sharedDiskP503Value10_7
private theorem sharedDiskP503Value11_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 11 (0:Fin 8))=sharedDiskP503Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value11_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 11 (1:Fin 8))=sharedDiskP503Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value11_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 11 (2:Fin 8))=sharedDiskP503Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value11_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 11 (3:Fin 8))=sharedDiskP503Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value11_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 11 (4:Fin 8))=sharedDiskP503Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value11_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 11 (5:Fin 8))=sharedDiskP503Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value11_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 11 (6:Fin 8))=sharedDiskP503Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value11_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 11 (7:Fin 8))=sharedDiskP503Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values11_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 11 j)=sharedDiskP503Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value11_0
  · exact sharedDiskP503Value11_1
  · exact sharedDiskP503Value11_2
  · exact sharedDiskP503Value11_3
  · exact sharedDiskP503Value11_4
  · exact sharedDiskP503Value11_5
  · exact sharedDiskP503Value11_6
  · exact sharedDiskP503Value11_7
private theorem sharedDiskP503Value12_0 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 12 (0:Fin 8))=sharedDiskP503Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value12_1 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 12 (1:Fin 8))=sharedDiskP503Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value12_2 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 12 (2:Fin 8))=sharedDiskP503Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value12_3 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 12 (3:Fin 8))=sharedDiskP503Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value12_4 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 12 (4:Fin 8))=sharedDiskP503Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value12_5 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 12 (5:Fin 8))=sharedDiskP503Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value12_6 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 12 (6:Fin 8))=sharedDiskP503Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP503Value12_7 : truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 12 (7:Fin 8))=sharedDiskP503Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP503Values12_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points 12 j)=sharedDiskP503Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP503Value12_0
  · exact sharedDiskP503Value12_1
  · exact sharedDiskP503Value12_2
  · exact sharedDiskP503Value12_3
  · exact sharedDiskP503Value12_4
  · exact sharedDiskP503Value12_5
  · exact sharedDiskP503Value12_6
  · exact sharedDiskP503Value12_7
theorem sharedDiskP503Values_eq : ∀ (i : Fin 13) (j : Fin 8), truncatedChordCell 2 sharedDiskP503Params (sharedChord493Gauss8Points i j)=sharedDiskP503Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP503Values0_eq
  · exact sharedDiskP503Values1_eq
  · exact sharedDiskP503Values2_eq
  · exact sharedDiskP503Values3_eq
  · exact sharedDiskP503Values4_eq
  · exact sharedDiskP503Values5_eq
  · exact sharedDiskP503Values6_eq
  · exact sharedDiskP503Values7_eq
  · exact sharedDiskP503Values8_eq
  · exact sharedDiskP503Values9_eq
  · exact sharedDiskP503Values10_eq
  · exact sharedDiskP503Values11_eq
  · exact sharedDiskP503Values12_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP503Box : HorizontalRectangle := ⟨(139/200),(141/200),(896432009617469/1649267441664000),(182238814541941/329853488332800),(808176994551784737867902790456805/2596148429267413814265248164610048),(4395289722471361657213374847348473/1298074214633706907132624082305024),(-713987677575056145465237433792365/162259276829213363391578010288128),(-1577008368110372535403305287138151/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP503Grid : CGrid := momentChordGrid sharedDiskP503Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984)
theorem sharedDiskP503Columns : containedInReported sharedDiskP503Grid.re sharedDiskP503Box.reLo sharedDiskP503Box.reHi=true ∧ containedInReported sharedDiskP503Grid.im sharedDiskP503Box.imLo sharedDiskP503Box.imHi=true := by
  rw [sharedDiskP503Grid,momentChordGrid_eq_tabulated sharedDiskP503Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984) sharedChord493Gauss8Points sharedChord493Gauss8Weights sharedDiskP503Values sharedChord493Gauss8Points_eq sharedChord493Gauss8Weights_eq sharedDiskP503Values_eq]
  decide +kernel
theorem sharedDiskP503Sound : sharedDiskP503Box.Sound := by
  intro t a tl tu al au
  change (((139/200):ℚ):ℝ)≤t at tl
  change t≤(((141/200):ℚ):ℝ) at tu
  change (((896432009617469/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((182238814541941/329853488332800):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP503Params_ok] at ps
  have band := sharedChord493ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(139/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((141/200):ℚ)≤(3/4)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((878940159632233/1649267441664000):ℚ)≤(896432009617469/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((182238814541941/329853488332800):ℚ)≤(929134916903873/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord493Bd (by decide +kernel) (by decide +kernel) sharedChord493M (by decide +kernel) (sharedChord493Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP503Columns.1 sharedDiskP503Columns.2
def sharedDiskP503Rows : List SignRow := [positive_503.toSignRow, positive_504.toSignRow]
theorem sharedDiskP503Rows_actual : ∀ r∈sharedDiskP503Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP503Rows.all (sharedDiskP503Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP503Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP505Params : ChordParams := ⟨⟨(-14934166069401630452855),(-14031821289093377396969),true⟩,⟨2364808289716588540404651,2446722348079279558165402,true⟩,⟨102022941316783159567885,109862201995948879501757,true⟩,⟨159749378259261280185403,170948770220400308274215,true⟩,⟨257308872680975743197375,265649222243125739566274,true⟩,⟨1179421956154918829878632,1181184170214462155547750,true⟩,⟨(-2631772703320787361131663),(-2591093253803354000552098),true⟩,⟨⟨1123744443642349132504226,1237887361393458540694563,true⟩,⟨(-69412),69412,true⟩⟩⟩
theorem sharedDiskP505Params_ok : chordParams (Grid.ofRats (141/200) (143/200)) (Grid.ofRats (900209581535287/1649267441664000) (36600725696323/65970697666560))=sharedDiskP505Params := by decide +kernel
def sharedDiskP505Values (i : Fin 13) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-5487191065073364329034346),(-2744545333770665515454498),true⟩,⟨(-1119961672176473812227399),1066417239718679204273215,true⟩⟩
  | 0,1 => ⟨⟨(-5099612303494931062261219),(-2485362296461781145005715),true⟩,⟨(-1159493760432682462967502),975248094152102855916811,true⟩⟩
  | 0,2 => ⟨⟨(-4804509729298791665339229),(-2295734352887867981135094),true⟩,⟨(-1190085141826840396980246),887178035870161425592570,true⟩⟩
  | 0,3 => ⟨⟨(-4631875551147651821114786),(-2187849939424841772537751),true⟩,⟨(-1207435267808663706974903),828869447621247533753356,true⟩⟩
  | 0,4 => ⟨⟨(-5920028648309222178694702),(-3046512782587272716608504),true⟩,⟨(-1094262458415239037236263),1131833322516400545359588,true⟩⟩
  | 0,5 => ⟨⟨(-6337598711730113850803821),(-3351068858531088287907840),true⟩,⟨(-1074261564600407160690225),1155242712042955467462767,true⟩⟩
  | 0,6 => ⟨⟨(-6676597742605413546467004),(-3611032276509468088036851),true⟩,⟨(-1062391164225310019493563),1143748589238407316265616,true⟩⟩
  | 0,7 => ⟨⟨(-6884067767605114877018353),(-3776851779859256022506602),true⟩,⟨(-1057426751967875951954576),1122736041458195838559843,true⟩⟩
  | 1,0 => ⟨⟨(-3480574180207031840241538),(-1516891578165655881524546),true⟩,⟨(-1310819559351445279348267),393281774766173245284105,true⟩⟩
  | 1,1 => ⟨⟨(-3202198147548357199049512),(-1365280536430737141483126),true⟩,⟨(-1331986716971008552924738),276022717674578257400723,true⟩⟩
  | 1,2 => ⟨⟨(-2994452713635929928600823),(-1254124664422881614134947),true⟩,⟨(-1346631030738846565218352),185535616567747754872705,true⟩⟩
  | 1,3 => ⟨⟨(-2874409242075799762638377),(-1190528942040278529303308),true⟩,⟨(-1354609623898696342921275),132383121261236843821584,true⟩⟩
  | 1,4 => ⟨⟨(-3799931410775945410565994),(-1695381360997163109558956),true⟩,⟨(-1284527319904215291223185),520409962818925857683405,true⟩⟩
  | 1,5 => ⟨⟨(-4117538913905400829166035),(-1878558339853012083462643),true⟩,⟨(-1256411898696645371758358),637063839426120572964095,true⟩⟩
  | 1,6 => ⟨⟨(-4383283624943039826658097),(-2036262282317373941017413),true⟩,⟨(-1231617186697263251768373),736918401256442925303773,true⟩⟩
  | 1,7 => ⟨⟨(-4549602341793726596594483),(-2137198411662810294243017),true⟩,⟨(-1215547205560328441606215),799441892152677216724213,true⟩⟩
  | 2,0 => ⟨⟨(-2099754845102716184546066),(-782174899837035154333643),true⟩,⟨(-1396009009967935726929364),(-201312475386858777186342),true⟩⟩
  | 2,1 => ⟨⟨(-1918786230655694881586354),(-684746006488993084972156),true⟩,⟨(-1402409331666787077297066),(-271662802550098419336983),true⟩⟩
  | 2,2 => ⟨⟨(-1783616572935712540378177),(-611570653652165437908128),true⟩,⟨(-1406024299295910464141823),(-323123340863940541824137),true⟩⟩
  | 2,3 => ⟨⟨(-1705343142858089768238064),(-568716397871935702914925),true⟩,⟨(-1407974512637125153654213),(-352344288422987176776225),true⟩⟩
  | 2,4 => ⟨⟨(-2307877165552289309832958),(-893863724066915400808740),true⟩,⟨(-1386752014057839400675702),(-119111846906652048847009),true⟩⟩
  | 2,5 => ⟨⟨(-2521972414031064828235918),(-1005753053506289436710481),true⟩,⟨(-1375757854280814278355496),(-25400713403078138065425),true⟩⟩
  | 2,6 => ⟨⟨(-2703242005142744059277045),(-1100492104000201069139646),true⟩,⟨(-1365326642148813102457020),55828123760258086912717,true⟩⟩
  | 2,7 => ⟨⟨(-2817550108477612390480108),(-1160544058340046062671339),true⟩,⟨(-1358258131172321916162158),107036789896542341859421,true⟩⟩
  | 3,0 => ⟨⟨(-1188077642876140649388553),(-266925986918599770485102),true⟩,⟨(-1423223775623412729451283),(-528839288721871853009108),true⟩⟩
  | 3,1 => ⟨⟨(-1061670068120155994688450),(-190099073305459775163624),true⟩,⟨(-1423111374524892910855462),(-566501502986806664344053),true⟩⟩
  | 3,2 => ⟨⟨(-966247215640135288057610),(-131159513085610405015708),true⟩,⟨(-1421770570051031177906853),(-593147485338517705359015),true⟩⟩
  | 3,3 => ⟨⟨(-910557488332954060645390),(-96368148272774897840172),true⟩,⟨(-1420447982802495508719517),(-607935783907476164442542),true⟩⟩
  | 3,4 => ⟨⟨(-1331800814469587952118189),(-352667777566649869454381),true⟩,⟨(-1421290239053214967798340),(-483073451428134085936822),true⟩⟩
  | 3,5 => ⟨⟨(-1474214819488026241786291),(-436098980463293646357192),true⟩,⟨(-1417484772833337089323529),(-435024650993565784136071),true⟩⟩
  | 3,6 => ⟨⟨(-1593389332882492783777556),(-504873133468339873691658),true⟩,⟨(-1413047329312703295540701),(-393041237738239988469489),true⟩⟩
  | 3,7 => ⟨⟨(-1668205211829704935898572),(-547614248612241735942454),true⟩,⟨(-1409747265914007402366367),(-365967713523970343817277),true⟩⟩
  | 4,0 => ⟨⟨222996531656799265423563,777065172395493267759339,true⟩,⟨(-1282349738426463609672079),(-692170414846603184352369),true⟩⟩
  | 4,1 => ⟨⟨438205245793781103871117,985323765757077572583616,true⟩,⟨(-1230108123418041836733258),(-660309395621619925429724),true⟩⟩
  | 4,2 => ⟨⟨590872456924454390049766,1137329885660669165585690,true⟩,⟨(-1187328826578524660182878),(-629262112124697434234608),true⟩⟩
  | 4,3 => ⟨⟨677251740486237540673935,1224018099484881080105895,true⟩,⟨(-1160998320220026741696602),(-609037419402349472770529),true⟩⟩
  | 4,4 => ⟨⟨(-58249990932324279851055),530130214056140873665711,true⟩,⟨(-1341625749186520407628011),(-711165680196951590642168),true⟩⟩
  | 4,5 => ⟨⟨(-366759753460713696777606),282938755849941508990166,true⟩,⟨(-1386014717594009006172046),(-700715612047455521442795),true⟩⟩
  | 4,6 => ⟨⟨(-650727506437245026899626),77694508385993333685145,true⟩,⟨(-1409950722818738485088507),(-662380782286399894960301),true⟩⟩
  | 4,7 => ⟨⟨(-844789076961204791368578),(-54894462483694683196810),true⟩,⟨(-1418342974797794842880416),(-624638282252930637084859),true⟩⟩
  | 5,0 => ⟨⟨1608012107929333399514097,2181661057435086245373572,true⟩,⟨(-851452907590067299378048),(-338789331451208478899497),true⟩⟩
  | 5,1 => ⟨⟨1798967893799571992670673,2384919815572147432470126,true⟩,⟨(-814131273662124466659540),(-299351209098043027758823),true⟩⟩
  | 5,2 => ⟨⟨1938826623032881083765348,2537194075572184670502661,true⟩,⟨(-805925854301046344878436),(-284775686164705983501222),true⟩⟩
  | 5,3 => ⟨⟨2020156900609216114052640,2627691965020562606289829,true⟩,⟨(-811343679307803909808639),(-283924101010058494403544),true⟩⟩
  | 5,4 => ⟨⟨1376163899165580339034772,1939174844099181295141773,true⟩,⟨(-920676115601685265417016),(-403934671590606444123443),true⟩⟩
  | 5,5 => ⟨⟨1124708587454668157274743,1679381422832372060596787,true⟩,⟨(-1008241386433215569394461),(-481970705227632940460875),true⟩⟩
  | 5,6 => ⟨⟨893737035793607171870347,1443134140606434756183784,true⟩,⟨(-1089612138900792087957065),(-551331076458706153528132),true⟩⟩
  | 5,7 => ⟨⟨737654398926631875641531,1284901362965056246679330,true⟩,⟨(-1141786033970621070984159),(-593873490993433037382748),true⟩⟩
  | 6,0 => ⟨⟨2587374746725591129571958,3476285845915146209146786,true⟩,⟨(-1291164493212141563925941),(-502790502193144077442160),true⟩⟩
  | 6,1 => ⟨⟨2763088755167670858789688,3804150932044176190823473,true⟩,⟨(-1655831039936815577607179),(-711890594836506921380332),true⟩⟩
  | 6,2 => ⟨⟨2899236373838976359211696,4106255794609150238170035,true⟩,⟨(-2092067087486069745570910),(-971440306099733580432597),true⟩⟩
  | 6,3 => ⟨⟨2969875675497795729001528,4304527333208275672076076,true⟩,⟨(-2447027642984750959349720),(-1186363399026660293014276),true⟩⟩
  | 6,4 => ⟨⟨2409138625965902020454418,3181410821510319099525917,true⟩,⟨(-1047427316612613712727692),(-372843780463131832391148),true⟩⟩
  | 6,5 => ⟨⟨2252379692176841633413336,2944254228606720210607770,true⟩,⟨(-909484747953989185071144),(-309425168523729337513609),true⟩⟩
  | 6,6 => ⟨⟨2131045073363829136444111,2772676356394932887362333,true⟩,⟨(-843522151082401012055993),(-287701987699059865623611),true⟩⟩
  | 6,7 => ⟨⟨2057463561463047330766176,2673230860944977729798603,true⟩,⟨(-818459330506257454917135),(-284450043995647006545971),true⟩⟩
  | 7,0 => ⟨⟨3024924579641704478778821,4714004555246437121962201,true⟩,⟨(-3495331457450677141317276),(-1829552458932803637425633),true⟩⟩
  | 7,1 => ⟨⟨2999565811800475219845642,4804731820513298979422817,true⟩,⟨(-3854009062025084402181967),(-2050801436949488072715826),true⟩⟩
  | 7,2 => ⟨⟨2960213579555113138915832,4866375541278521733537457,true⟩,⟨(-4170961022375854979758329),(-2246388854956808243559349),true⟩⟩
  | 7,3 => ⟨⟨2926280775115393479567154,4897495110431491567924723,true⟩,⟨(-4377294168487225389804856),(-2373677259264764930249557),true⟩⟩
  | 7,4 => ⟨⟨3029285159504960539499376,4606695478750087649136086,true⟩,⟨(-3156723486990777529221384),(-1621000778823125770797658),true⟩⟩
  | 7,5 => ⟨⟨3017728687748583094042517,4501731773080121143255753,true⟩,⟨(-2878984139616976982778677),(-1450377209872358893686239),true⟩⟩
  | 7,6 => ⟨⟨3000656973293650129651890,4417229256267378236948618,true⟩,⟨(-2681973175505062813909104),(-1329711532903282393955415),true⟩⟩
  | 7,7 => ⟨⟨2987722626224873056815309,4366186980294908941947649,true⟩,⟨(-2572049613306501713420136),(-1262557851380349824037340),true⟩⟩
  | 8,0 => ⟨⟨2287985037358659967104743,4851047015159006750599243,true⟩,⟨(-6315561469937966849834905),(-3561665657564942603038108),true⟩⟩
  | 8,1 => ⟨⟨1924778202453925091276205,4684964748551952662909990,true⟩,⟨(-6978987546979861932959664),(-3962325332139649809929904),true⟩⟩
  | 8,2 => ⟨⟨1553359145204240757839281,4476282787034623826696432,true⟩,⟨(-7530784116170470150019792),(-4291849836845299350616157),true⟩⟩
  | 8,3 => ⟨⟨1288120613908183647159842,4310606519856650578803170,true⟩,⟨(-7869537737123883183683963),(-4492014308713123233471007),true⟩⟩
  | 8,4 => ⟨⟨2570436974249659081049743,4936274823162862872759742,true⟩,⟨(-5659302153096844847472291),(-3161704369433442945965110),true⟩⟩
  | 8,5 => ⟨⟨2755079866346107788702025,4952086573845898990246448,true⟩,⟨(-5105063834783351271529307),(-2821845125370618161618851),true⟩⟩
  | 8,6 => ⟨⟨2858897812372855810702040,4932715514565578346406933,true⟩,⟨(-4705896854890691728303875),(-2576230998618963887172469),true⟩⟩
  | 8,7 => ⟨⟨2906639971629718182885368,4910584961837451321041811,true⟩,⟨(-4481712234852099287114298),(-2438067978387450696687824),true⟩⟩
  | 9,0 => ⟨⟨(-223738351873737085489371),3321440656269873149576528,true⟩,⟨(-9210845653557263730430776),(-5213028222038708910934217),true⟩⟩
  | 9,1 => ⟨⟨(-762044786170195662120537),2942068458503039489625102,true⟩,⟨(-9539561890868870067057609),(-5373032253655767988574033),true⟩⟩
  | 9,2 => ⟨⟨(-1225273300420429881700790),2604216563512942707151371,true⟩,⟨(-9776270875472060486232868),(-5481145393765250099449448),true⟩⟩
  | 9,3 => ⟨⟨(-1520093058257046706004749),2384172530532210784668354,true⟩,⟨(-9906192784084585986866447),(-5536695596704670187058905),true⟩⟩
  | 9,4 => ⟨⟨291572763661217021674426,3672386789951555144018192,true⟩,⟨(-8832296005585665203413493),(-5019315332477010291546670),true⟩⟩
  | 9,5 => ⟨⟨717442564072564441126517,3950695447852279097206867,true⟩,⟨(-8464624458195582214476211),(-4824320590334531375119330),true⟩⟩
  | 9,6 => ⟨⟨1021194264080938976004221,4140132573491088319980213,true⟩,⟨(-8168279155954313856545097),(-4663373991323684424659348),true⟩⟩
  | 9,7 => ⟨⟨1183262792391898566870489,4242013880746093464654296,true⟩,⟨(-7993047309322452620864291),(-4564513369510920142622939),true⟩⟩
  | 10,0 => ⟨⟨(-4025439252021144417992226),538591494461509286545831,true⟩,⟨(-10408102475819332199186958),(-5541366006108905261702053),true⟩⟩
  | 10,1 => ⟨⟨(-4782850452105730563643041),(-39717654070410155663456),true⟩,⟨(-10343891919407770276871750),(-5393574660998901828913619),true⟩⟩
  | 10,2 => ⟨⟨(-5381368449266847334439453),(-504577514281615625150893),true⟩,⟨(-10211705183002703751110761),(-5224832965420280614876441),true⟩⟩
  | 10,3 => ⟨⟨(-5737058691326409762120289),(-787752366024547248977944),true⟩,⟨(-10094557549068205766557329),(-5100093481869828847011021),true⟩⟩
  | 10,4 => ⟨⟨(-3229066299986427371492945),1127233082751963875449033,true⟩,⟨(-10363940196198395552252478),(-5624969704640522337929378),true⟩⟩
  | 10,5 => ⟨⟨(-2516060870034744809840754),1637651606959291123620576,true⟩,⟨(-10232900777511305531180418),(-5640567198119115476751185),true⟩⟩
  | 10,6 => ⟨⟨(-1978301777221200717068589),2034904411450833613743356,true⟩,⟨(-10077592160777425396287038),(-5603553429602483867890351),true⟩⟩
  | 10,7 => ⟨⟨(-1667211643655973736305087),2272978275779900543638624,true⟩,⟨(-9965216753819380058066977),(-5560706965744091430159349),true⟩⟩
  | 11,0 => ⟨⟨(-7978957326070658473324948),(-2777617788030183999765601),true⟩,⟨(-8272267438825783694211109),(-3637035872731901680061635),true⟩⟩
  | 11,1 => ⟨⟨(-8376655396778725608463552),(-3225399118560312837837876),true⟩,⟨(-7480961863142792953092612),(-3088762962903507367002711),true⟩⟩
  | 11,2 => ⟨⟨(-8610667902633433889952964),(-3524588967447346721444843),true⟩,⟨(-6786309327119378130915061),(-2605327244994694748406300),true⟩⟩
  | 11,3 => ⟨⟨(-8711307740853235593560892),(-3678238694168410924163057),true⟩,⟨(-6344118880586230515707628),(-2298643566409342758525329),true⟩⟩
  | 11,4 => ⟨⟨(-7418069471466662844436804),(-2227900426398696108966051),true⟩,⟨(-8993117951257101626032153),(-4167318461400064322033171),true⟩⟩
  | 11,5 => ⟨⟨(-6795442975348788177349296),(-1669466442176010240142421),true⟩,⟨(-9532834715983161151360999),(-4594940628868660426654638),true⟩⟩
  | 11,6 => ⟨⟨(-6251327193354151271043917),(-1207898137312896215456522),true⟩,⟨(-9866230816973773108278207),(-4882593289683627697159210),true⟩⟩
  | 11,7 => ⟨⟨(-5907273729770796432327964),(-925314646208914297701376),true⟩,⟨(-10027179075268463663670622),(-5033257468316255518032983),true⟩⟩
  | 12,0 => ⟨⟨(-8249262321329765918650510),(-4118702039662467412185407),true⟩,⟨(-2871151619587530791994086),(-164653543783051249495906),true⟩⟩
  | 12,1 => ⟨⟨(-7784676317528686881511344),(-4027266147271490018235482),true⟩,⟨(-1980413689235088718070816),366127174792160381987534,true⟩⟩
  | 12,2 => ⟨⟨(-7339105809940232989279427),(-3900898243858490531636570),true⟩,⟨(-1337688613512782322587865),787705542148318596910174,true⟩⟩
  | 12,3 => ⟨⟨(-7045028125424224588104042),(-3803165549493310307417059),true⟩,⟨(-981699066448775789144558),1008112091385268322137745,true⟩⟩
  | 12,4 => ⟨⟨(-8603820098132674869452517),(-4118588997082245505253922),true⟩,⟨(-3896793703637708969682776),(-747969343040525522008872),true⟩⟩
  | 12,5 => ⟨⟨(-8773969054274221018972989),(-4017754769708362086874666),true⟩,⟨(-4884052541170056806947381),(-1345046786572787431368116),true⟩⟩
  | 12,6 => ⟨⟨(-8789292671575677800738246),(-3866524444481589634945567),true⟩,⟨(-5663526600581148985078541),(-1843325646849341330686232),true⟩⟩
  | 12,7 => ⟨⟨(-8746284655491691169775042),(-3745122961581288464136421),true⟩,⟨(-6124416342507366452588673),(-2149515296266267398820637),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP505Value0_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 0 (0:Fin 8))=sharedDiskP505Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value0_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 0 (1:Fin 8))=sharedDiskP505Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value0_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 0 (2:Fin 8))=sharedDiskP505Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value0_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 0 (3:Fin 8))=sharedDiskP505Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value0_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 0 (4:Fin 8))=sharedDiskP505Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value0_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 0 (5:Fin 8))=sharedDiskP505Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value0_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 0 (6:Fin 8))=sharedDiskP505Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value0_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 0 (7:Fin 8))=sharedDiskP505Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 0 j)=sharedDiskP505Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value0_0
  · exact sharedDiskP505Value0_1
  · exact sharedDiskP505Value0_2
  · exact sharedDiskP505Value0_3
  · exact sharedDiskP505Value0_4
  · exact sharedDiskP505Value0_5
  · exact sharedDiskP505Value0_6
  · exact sharedDiskP505Value0_7
private theorem sharedDiskP505Value1_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 1 (0:Fin 8))=sharedDiskP505Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value1_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 1 (1:Fin 8))=sharedDiskP505Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value1_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 1 (2:Fin 8))=sharedDiskP505Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value1_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 1 (3:Fin 8))=sharedDiskP505Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value1_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 1 (4:Fin 8))=sharedDiskP505Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value1_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 1 (5:Fin 8))=sharedDiskP505Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value1_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 1 (6:Fin 8))=sharedDiskP505Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value1_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 1 (7:Fin 8))=sharedDiskP505Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 1 j)=sharedDiskP505Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value1_0
  · exact sharedDiskP505Value1_1
  · exact sharedDiskP505Value1_2
  · exact sharedDiskP505Value1_3
  · exact sharedDiskP505Value1_4
  · exact sharedDiskP505Value1_5
  · exact sharedDiskP505Value1_6
  · exact sharedDiskP505Value1_7
private theorem sharedDiskP505Value2_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 2 (0:Fin 8))=sharedDiskP505Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value2_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 2 (1:Fin 8))=sharedDiskP505Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value2_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 2 (2:Fin 8))=sharedDiskP505Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value2_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 2 (3:Fin 8))=sharedDiskP505Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value2_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 2 (4:Fin 8))=sharedDiskP505Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value2_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 2 (5:Fin 8))=sharedDiskP505Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value2_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 2 (6:Fin 8))=sharedDiskP505Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value2_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 2 (7:Fin 8))=sharedDiskP505Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 2 j)=sharedDiskP505Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value2_0
  · exact sharedDiskP505Value2_1
  · exact sharedDiskP505Value2_2
  · exact sharedDiskP505Value2_3
  · exact sharedDiskP505Value2_4
  · exact sharedDiskP505Value2_5
  · exact sharedDiskP505Value2_6
  · exact sharedDiskP505Value2_7
private theorem sharedDiskP505Value3_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 3 (0:Fin 8))=sharedDiskP505Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value3_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 3 (1:Fin 8))=sharedDiskP505Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value3_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 3 (2:Fin 8))=sharedDiskP505Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value3_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 3 (3:Fin 8))=sharedDiskP505Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value3_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 3 (4:Fin 8))=sharedDiskP505Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value3_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 3 (5:Fin 8))=sharedDiskP505Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value3_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 3 (6:Fin 8))=sharedDiskP505Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value3_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 3 (7:Fin 8))=sharedDiskP505Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 3 j)=sharedDiskP505Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value3_0
  · exact sharedDiskP505Value3_1
  · exact sharedDiskP505Value3_2
  · exact sharedDiskP505Value3_3
  · exact sharedDiskP505Value3_4
  · exact sharedDiskP505Value3_5
  · exact sharedDiskP505Value3_6
  · exact sharedDiskP505Value3_7
private theorem sharedDiskP505Value4_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 4 (0:Fin 8))=sharedDiskP505Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value4_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 4 (1:Fin 8))=sharedDiskP505Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value4_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 4 (2:Fin 8))=sharedDiskP505Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value4_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 4 (3:Fin 8))=sharedDiskP505Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value4_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 4 (4:Fin 8))=sharedDiskP505Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value4_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 4 (5:Fin 8))=sharedDiskP505Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value4_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 4 (6:Fin 8))=sharedDiskP505Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value4_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 4 (7:Fin 8))=sharedDiskP505Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 4 j)=sharedDiskP505Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value4_0
  · exact sharedDiskP505Value4_1
  · exact sharedDiskP505Value4_2
  · exact sharedDiskP505Value4_3
  · exact sharedDiskP505Value4_4
  · exact sharedDiskP505Value4_5
  · exact sharedDiskP505Value4_6
  · exact sharedDiskP505Value4_7
private theorem sharedDiskP505Value5_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 5 (0:Fin 8))=sharedDiskP505Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value5_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 5 (1:Fin 8))=sharedDiskP505Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value5_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 5 (2:Fin 8))=sharedDiskP505Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value5_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 5 (3:Fin 8))=sharedDiskP505Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value5_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 5 (4:Fin 8))=sharedDiskP505Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value5_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 5 (5:Fin 8))=sharedDiskP505Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value5_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 5 (6:Fin 8))=sharedDiskP505Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value5_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 5 (7:Fin 8))=sharedDiskP505Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 5 j)=sharedDiskP505Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value5_0
  · exact sharedDiskP505Value5_1
  · exact sharedDiskP505Value5_2
  · exact sharedDiskP505Value5_3
  · exact sharedDiskP505Value5_4
  · exact sharedDiskP505Value5_5
  · exact sharedDiskP505Value5_6
  · exact sharedDiskP505Value5_7
private theorem sharedDiskP505Value6_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 6 (0:Fin 8))=sharedDiskP505Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value6_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 6 (1:Fin 8))=sharedDiskP505Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value6_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 6 (2:Fin 8))=sharedDiskP505Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value6_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 6 (3:Fin 8))=sharedDiskP505Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value6_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 6 (4:Fin 8))=sharedDiskP505Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value6_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 6 (5:Fin 8))=sharedDiskP505Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value6_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 6 (6:Fin 8))=sharedDiskP505Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value6_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 6 (7:Fin 8))=sharedDiskP505Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 6 j)=sharedDiskP505Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value6_0
  · exact sharedDiskP505Value6_1
  · exact sharedDiskP505Value6_2
  · exact sharedDiskP505Value6_3
  · exact sharedDiskP505Value6_4
  · exact sharedDiskP505Value6_5
  · exact sharedDiskP505Value6_6
  · exact sharedDiskP505Value6_7
private theorem sharedDiskP505Value7_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 7 (0:Fin 8))=sharedDiskP505Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value7_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 7 (1:Fin 8))=sharedDiskP505Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value7_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 7 (2:Fin 8))=sharedDiskP505Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value7_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 7 (3:Fin 8))=sharedDiskP505Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value7_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 7 (4:Fin 8))=sharedDiskP505Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value7_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 7 (5:Fin 8))=sharedDiskP505Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value7_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 7 (6:Fin 8))=sharedDiskP505Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value7_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 7 (7:Fin 8))=sharedDiskP505Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 7 j)=sharedDiskP505Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value7_0
  · exact sharedDiskP505Value7_1
  · exact sharedDiskP505Value7_2
  · exact sharedDiskP505Value7_3
  · exact sharedDiskP505Value7_4
  · exact sharedDiskP505Value7_5
  · exact sharedDiskP505Value7_6
  · exact sharedDiskP505Value7_7
private theorem sharedDiskP505Value8_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 8 (0:Fin 8))=sharedDiskP505Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value8_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 8 (1:Fin 8))=sharedDiskP505Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value8_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 8 (2:Fin 8))=sharedDiskP505Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value8_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 8 (3:Fin 8))=sharedDiskP505Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value8_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 8 (4:Fin 8))=sharedDiskP505Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value8_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 8 (5:Fin 8))=sharedDiskP505Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value8_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 8 (6:Fin 8))=sharedDiskP505Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value8_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 8 (7:Fin 8))=sharedDiskP505Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 8 j)=sharedDiskP505Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value8_0
  · exact sharedDiskP505Value8_1
  · exact sharedDiskP505Value8_2
  · exact sharedDiskP505Value8_3
  · exact sharedDiskP505Value8_4
  · exact sharedDiskP505Value8_5
  · exact sharedDiskP505Value8_6
  · exact sharedDiskP505Value8_7
private theorem sharedDiskP505Value9_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 9 (0:Fin 8))=sharedDiskP505Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value9_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 9 (1:Fin 8))=sharedDiskP505Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value9_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 9 (2:Fin 8))=sharedDiskP505Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value9_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 9 (3:Fin 8))=sharedDiskP505Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value9_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 9 (4:Fin 8))=sharedDiskP505Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value9_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 9 (5:Fin 8))=sharedDiskP505Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value9_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 9 (6:Fin 8))=sharedDiskP505Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value9_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 9 (7:Fin 8))=sharedDiskP505Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values9_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 9 j)=sharedDiskP505Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value9_0
  · exact sharedDiskP505Value9_1
  · exact sharedDiskP505Value9_2
  · exact sharedDiskP505Value9_3
  · exact sharedDiskP505Value9_4
  · exact sharedDiskP505Value9_5
  · exact sharedDiskP505Value9_6
  · exact sharedDiskP505Value9_7
private theorem sharedDiskP505Value10_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 10 (0:Fin 8))=sharedDiskP505Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value10_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 10 (1:Fin 8))=sharedDiskP505Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value10_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 10 (2:Fin 8))=sharedDiskP505Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value10_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 10 (3:Fin 8))=sharedDiskP505Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value10_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 10 (4:Fin 8))=sharedDiskP505Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value10_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 10 (5:Fin 8))=sharedDiskP505Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value10_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 10 (6:Fin 8))=sharedDiskP505Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value10_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 10 (7:Fin 8))=sharedDiskP505Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values10_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 10 j)=sharedDiskP505Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value10_0
  · exact sharedDiskP505Value10_1
  · exact sharedDiskP505Value10_2
  · exact sharedDiskP505Value10_3
  · exact sharedDiskP505Value10_4
  · exact sharedDiskP505Value10_5
  · exact sharedDiskP505Value10_6
  · exact sharedDiskP505Value10_7
private theorem sharedDiskP505Value11_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 11 (0:Fin 8))=sharedDiskP505Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value11_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 11 (1:Fin 8))=sharedDiskP505Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value11_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 11 (2:Fin 8))=sharedDiskP505Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value11_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 11 (3:Fin 8))=sharedDiskP505Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value11_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 11 (4:Fin 8))=sharedDiskP505Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value11_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 11 (5:Fin 8))=sharedDiskP505Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value11_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 11 (6:Fin 8))=sharedDiskP505Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value11_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 11 (7:Fin 8))=sharedDiskP505Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values11_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 11 j)=sharedDiskP505Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value11_0
  · exact sharedDiskP505Value11_1
  · exact sharedDiskP505Value11_2
  · exact sharedDiskP505Value11_3
  · exact sharedDiskP505Value11_4
  · exact sharedDiskP505Value11_5
  · exact sharedDiskP505Value11_6
  · exact sharedDiskP505Value11_7
private theorem sharedDiskP505Value12_0 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 12 (0:Fin 8))=sharedDiskP505Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value12_1 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 12 (1:Fin 8))=sharedDiskP505Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value12_2 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 12 (2:Fin 8))=sharedDiskP505Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value12_3 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 12 (3:Fin 8))=sharedDiskP505Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value12_4 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 12 (4:Fin 8))=sharedDiskP505Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value12_5 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 12 (5:Fin 8))=sharedDiskP505Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value12_6 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 12 (6:Fin 8))=sharedDiskP505Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP505Value12_7 : truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 12 (7:Fin 8))=sharedDiskP505Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP505Values12_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points 12 j)=sharedDiskP505Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP505Value12_0
  · exact sharedDiskP505Value12_1
  · exact sharedDiskP505Value12_2
  · exact sharedDiskP505Value12_3
  · exact sharedDiskP505Value12_4
  · exact sharedDiskP505Value12_5
  · exact sharedDiskP505Value12_6
  · exact sharedDiskP505Value12_7
theorem sharedDiskP505Values_eq : ∀ (i : Fin 13) (j : Fin 8), truncatedChordCell 2 sharedDiskP505Params (sharedChord493Gauss8Points i j)=sharedDiskP505Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP505Values0_eq
  · exact sharedDiskP505Values1_eq
  · exact sharedDiskP505Values2_eq
  · exact sharedDiskP505Values3_eq
  · exact sharedDiskP505Values4_eq
  · exact sharedDiskP505Values5_eq
  · exact sharedDiskP505Values6_eq
  · exact sharedDiskP505Values7_eq
  · exact sharedDiskP505Values8_eq
  · exact sharedDiskP505Values9_eq
  · exact sharedDiskP505Values10_eq
  · exact sharedDiskP505Values11_eq
  · exact sharedDiskP505Values12_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP505Box : HorizontalRectangle := ⟨(141/200),(143/200),(900209581535287/1649267441664000),(36600725696323/65970697666560),(659653442561195494742720051768099/2596148429267413814265248164610048),(4159675184527704271074756407975441/1298074214633706907132624082305024),(-2839200268473914728842241502622029/649037107316853453566312041152512),(-856217627068199914393673242521933/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP505Grid : CGrid := momentChordGrid sharedDiskP505Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984)
theorem sharedDiskP505Columns : containedInReported sharedDiskP505Grid.re sharedDiskP505Box.reLo sharedDiskP505Box.reHi=true ∧ containedInReported sharedDiskP505Grid.im sharedDiskP505Box.imLo sharedDiskP505Box.imHi=true := by
  rw [sharedDiskP505Grid,momentChordGrid_eq_tabulated sharedDiskP505Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984) sharedChord493Gauss8Points sharedChord493Gauss8Weights sharedDiskP505Values sharedChord493Gauss8Points_eq sharedChord493Gauss8Weights_eq sharedDiskP505Values_eq]
  decide +kernel
theorem sharedDiskP505Sound : sharedDiskP505Box.Sound := by
  intro t a tl tu al au
  change (((141/200):ℚ):ℝ)≤t at tl
  change t≤(((143/200):ℚ):ℝ) at tu
  change (((900209581535287/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((36600725696323/65970697666560):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP505Params_ok] at ps
  have band := sharedChord493ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(141/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((143/200):ℚ)≤(3/4)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((878940159632233/1649267441664000):ℚ)≤(900209581535287/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((36600725696323/65970697666560):ℚ)≤(929134916903873/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord493Bd (by decide +kernel) (by decide +kernel) sharedChord493M (by decide +kernel) (sharedChord493Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP505Columns.1 sharedDiskP505Columns.2
def sharedDiskP505Rows : List SignRow := [positive_505.toSignRow, positive_506.toSignRow]
theorem sharedDiskP505Rows_actual : ∀ r∈sharedDiskP505Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP505Rows.all (sharedDiskP505Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP505Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP507Params : ChordParams := ⟨⟨(-15867234275413482437108),(-14934166069401630452513),true⟩,⟨2319748502346204639677080,2400036460957990045055210,true⟩,⟨104515948465728588021393,112408204536777403657676,true⟩,⟨166039192850139712000793,177440706421791341874380,true⟩,⟨265251133740939768282827,273620326427707422591973,true⟩,⟨1177602472147076183578672,1179421956154918829879302,true⟩,⟨(-2591093253803354000561826),(-2551411914032023206502176),true⟩,⟨⟨1121187600523313754771048,1236684844975543794298281,true⟩,⟨(-132528),132528,true⟩⟩⟩
theorem sharedDiskP507Params_ok : chordParams (Grid.ofRats (143/200) (29/40)) (Grid.ofRats (904080147915859/1649267441664000) (918935207220221/1649267441664000))=sharedDiskP507Params := by decide +kernel
def sharedDiskP507Values (i : Fin 13) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-5428399319024338249856882),(-2736322881621393633510232),true⟩,⟨(-1089384849244124686825718),1045737786992785720770859,true⟩⟩
  | 0,1 => ⟨⟨(-5057189984003948815757355),(-2486744067273735867123644),true⟩,⟨(-1125485787821418881414131),962684684693022765017860,true⟩⟩
  | 0,2 => ⟨⟨(-4774059037623678804443597),(-2303440505114636357365628),true⟩,⟨(-1154745149393622437788130),881628140767615680983789,true⟩⟩
  | 0,3 => ⟨⟨(-4608207446830783938525239),(-2198931276796990953664329),true⟩,⟨(-1171433035331338568366233),827642852944219020660777,true⟩⟩
  | 0,4 => ⟨⟨(-5842219001635673718912452),(-3026393278882146119805791),true⟩,⟨(-1066061605203464443949329),1104158035886970957961298,true⟩⟩
  | 0,5 => ⟨⟨(-6240840668614044794477183),(-3318142143909564872750134),true⟩,⟨(-1048298338709895777154974),1123455223365901410946093,true⟩⟩
  | 0,6 => ⟨⟨(-6564108610031066454175030),(-3566653075807518381719465),true⟩,⟨(-1038091448141264791455652),1110839609903050769161800,true⟩⟩
  | 0,7 => ⟨⟨(-6761913274859617005810863),(-3724871521132748796646680),true⟩,⟨(-1034030517373525931649383),1090202955371792469530399,true⟩⟩
  | 1,0 => ⟨⟨(-3497012792416024791685764),(-1545194922915934436897305),true⟩,⟨(-1272640154594701600769458),415566294059496238932449,true⟩⟩
  | 1,1 => ⟨⟨(-3226860325117006126591539),(-1396588886184951056704314),true⟩,⟨(-1293893450515282161832008),303778591577414197713889,true⟩⟩
  | 1,2 => ⟨⟨(-3024829595830606216701903),(-1287469276458288176633441),true⟩,⟨(-1308764408769446892704827),216972032443779261318496,true⟩⟩
  | 1,3 => ⟨⟨(-2907920232549018588371282),(-1224984540596285899348364),true⟩,⟨(-1316940155051631559669607),165758185358574812596117,true⟩⟩
  | 1,4 => ⟨⟨(-3806170168291287791133569),(-1719759757254905677211596),true⟩,⟨(-1246545511177819750888014),535867201608904260168146,true⟩⟩
  | 1,5 => ⟨⟨(-4112872208065730449476585),(-1898433375115988070550386),true⟩,⟨(-1218935824218978394998230),645409507746714355536285,true⟩⟩
  | 1,6 => ⟨⟨(-4369070144624845019391115),(-2051801787280486001843178),true⟩,⟨(-1194817656250318948401278),742073333305851217416823,true⟩⟩
  | 1,7 => ⟨⟨(-4529105321377951802812001),(-2149806762278641711576576),true⟩,⟨(-1179260524899061254840809),800313060282087050083356,true⟩⟩
  | 2,0 => ⟨⟨(-2147773527160311074748046),(-823217069516849112081326),true⟩,⟨(-1361005270623006335484518),(-165672616547419106825811),true⟩⟩
  | 2,1 => ⟨⟨(-1970141995757974824534049),(-727328908568328501669096),true⟩,⟨(-1368473533916356674716968),(-235459402579729364326738),true⟩⟩
  | 2,2 => ⟨⟨(-1837324462734701241767088),(-655330176472821182880786),true⟩,⟨(-1373022047008006259456555),(-286799138385224309137793),true⟩⟩
  | 2,3 => ⟨⟨(-1760362489804760159821762),(-613428998940726702402056),true⟩,⟨(-1375200730293966620838616),(-316098656620723821678438),true⟩⟩
  | 2,4 => ⟨⟨(-2353679222353823734740775),(-933152453919060705210056),true⟩,⟨(-1350749031872290719313622),(-81078543279737246538880),true⟩⟩
  | 2,5 => ⟨⟨(-2563967252787878287942265),(-1043267351289677170629976),true⟩,⟨(-1338970249101664117929116),12332992311458427515130,true⟩⟩
  | 2,6 => ⟨⟨(-2741007041404587244419148),(-1136464920346875976661528),true⟩,⟨(-1328026729215659639628316),91698308438522525704827,true⟩⟩
  | 2,7 => ⟨⟨(-2852502278144312175659576),(-1195511609425692682563088),true⟩,⟨(-1320699638039687398229355),141277169919547887773339,true⟩⟩
  | 3,0 => ⟨⟨(-1251015866503423613993239),(-319438756403365422570808),true⟩,⟨(-1392610629711566960628386),(-495659158694849734011967),true⟩⟩
  | 3,1 => ⟨⟨(-1126401490525696014563557),(-244167364924525265611798),true⟩,⟨(-1394139020341787165176469),(-534634836235544807717958),true⟩⟩
  | 3,2 => ⟨⟨(-1032311007854562520298934),(-186435026554342704475369),true⟩,⟨(-1394154824761455345794295),(-562425991291410448444136),true⟩⟩
  | 3,3 => ⟨⟨(-977392676616551669776801),(-152361076659738526244674),true⟩,⟨(-1393671668350451645389865),(-577942045253802018596446),true⟩⟩
  | 3,4 => ⟨⟨(-1392646845123403884603371),(-403472221290125098887822),true⟩,⟨(-1389021183148124044712940),(-448689322312325314391867),true⟩⟩
  | 3,5 => ⟨⟨(-1532914717101767324172625),(-485271469717118500607626),true⟩,⟨(-1383784648058601368615475),(-399756576274127360308884),true⟩⟩
  | 3,6 => ⟨⟨(-1650225158448962229887802),(-552723152427178549146653),true⟩,⟨(-1378301170165606603882025),(-357271246303948412961480),true⟩⟩
  | 3,7 => ⟨⟨(-1723834609355124559347869),(-593484769357888660314037),true⟩,⟨(-1376107966053880463610654),(-329868844207288974093731),true⟩⟩
  | 4,0 => ⟨⟨146664654681748584382012,697222552521379394946716,true⟩,⟨(-1279816413922142702948700),(-692588869625833893523831),true⟩⟩
  | 4,1 => ⟨⟨365063167626266026080447,902351454381116725029460,true⟩,⟨(-1230177297491632172818592),(-666562884733296363631761),true⟩⟩
  | 4,2 => ⟨⟨516069062112869271434941,1052534725096591454042464,true⟩,⟨(-1191996894503803571055282),(-639639089790739206601451),true⟩⟩
  | 4,3 => ⟨⟨601642654251880356072792,1138399131333825542127317,true⟩,⟨(-1168255134200951987154605),(-621689712549407596283371),true⟩⟩
  | 4,4 => ⟨⟨(-132085877523557345620464),454665871570399076665122,true⟩,⟨(-1331584351077526542901524),(-704608957186552042841712),true⟩⟩
  | 4,5 => ⟨⟨(-436503550927818670062895),218110721553073971007870,true⟩,⟨(-1368616037323875792080958),(-683886189998080728371966),true⟩⟩
  | 4,6 => ⟨⟨(-716794779981705893404797),17164837328899525308592,true⟩,⟨(-1386736826506878705849944),(-640196896320516653559567),true⟩⟩
  | 4,7 => ⟨⟨(-912530982545042434095747),(-111746489222225870737548),true⟩,⟨(-1392603634088584428908139),(-595558913695453881396382),true⟩⟩
  | 5,0 => ⟨⟨1535437971842886700269749,2103586784144062197652805,true⟩,⟨(-884393916277047002248221),(-370991754101999841201467),true⟩⟩
  | 5,1 => ⟨⟨1730937271226771068126521,2313729078065697561595945,true⟩,⟨(-852121202569285171154796),(-334459129687837860763069),true⟩⟩
  | 5,2 => ⟨⟨1875023688014372935645916,2472314815205951363220902,true⟩,⟨(-847926236689103213676242),(-322052096822541837894916),true⟩⟩
  | 5,3 => ⟨⟨1959074577080983049798696,2566891463764386167186905,true⟩,⟨(-855909787645669281501323),(-322574742513677084487364),true⟩⟩
  | 5,4 => ⟨⟨1300142639589461972603190,1855554587548735389054111,true⟩,⟨(-947609674769973472161832),(-432240544850210396906409),true⟩⟩
  | 5,5 => ⟨⟨1047261187829208114719089,1592867375821686385507880,true⟩,⟨(-1028416352166114914338899),(-505314009748908709297153),true⟩⟩
  | 5,6 => ⟨⟨816672387686620275176714,1356280834318496127765567,true⟩,⟨(-1103246770135103980570170),(-569419265523793273154605),true⟩⟩
  | 5,7 => ⟨⟨661551451473768251565140,1198810329928339992063281,true⟩,⟨(-1150841009064543100672356),(-608084374907064326539163),true⟩⟩
  | 6,0 => ⟨⟨2545577891447308794259869,3444978892836483815427463,true⟩,⟨(-1367648008394879496806168),(-561526476737141710469070),true⟩⟩
  | 6,1 => ⟨⟨2721232089817734945881304,3777531523250088522258451,true⟩,⟨(-1750291198957312050044055),(-782684285442533488445968),true⟩⟩
  | 6,2 => ⟨⟨2851957025671281592524322,4078739421276937744520846,true⟩,⟨(-2205646718263118428874164),(-1055374389733720634313401),true⟩⟩
  | 6,3 => ⟨⟨2915417907820972347699314,4272797995210345017056771,true⟩,⟨(-2574401962914950008793475),(-1279928432884203173259439),true⟩⟩
  | 6,4 => ⟨⟨2363177992718017821383557,3141963831966827337777707,true⟩,⟨(-1110415032799646543237592),(-422823263668970387640311),true⟩⟩
  | 6,5 => ⟨⟨2200745390425677679510211,2896252408817132692154204,true⟩,⟨(-963547167233836120505502),(-353818185348772725338316),true⟩⟩
  | 6,6 => ⟨⟨2074428249751647050368837,2717849509336351648565644,true⟩,⟨(-892160840621033884857848),(-328783868469455473813159),true⟩⟩
  | 6,7 => ⟨⟨1997793047679586121417832,2614397435888142635914192,true⟩,⟨(-864305600138942635460871),(-323834595866339653606770),true⟩⟩
  | 7,0 => ⟨⟨2940176704899083444057529,4657561934762993381753530,true⟩,⟨(-3654108424358745691110465),(-1945531400959507955796408),true⟩⟩
  | 7,1 => ⟨⟨2902328177941535103149066,4736688554008106843957893,true⟩,⟨(-4020211046144524637534222),(-2172252937019840295592481),true⟩⟩
  | 7,2 => ⟨⟨2851318368602037309029817,4787037745356364076999017,true⟩,⟨(-4342254956039078570837013),(-2371697137295821739456559),true⟩⟩
  | 7,3 => ⟨⟨2809539887350532825187122,4810334431859526380396958,true⟩,⟨(-4551143612687375070955146),(-2500990496593519848785915),true⟩⟩
  | 7,4 => ⟨⟨2955481431166415294967956,4559888652846737052044886,true⟩,⟨(-3306912700547191232148987),(-1730763689552650812974130),true⟩⟩
  | 7,5 => ⟨⟨2952152439975919981864090,4461733336363393227157808,true⟩,⟨(-3021011231068257928113719),(-1554301832127645224345595),true⟩⟩
  | 7,6 => ⟨⟨2940432041585228171364663,4381381712191126823867405,true⟩,⟨(-2817610327401353757428172),(-1429101136698758316223522),true⟩⟩
  | 7,7 => ⟨⟨2930285119636321395070767,4332385329278771094074243,true⟩,⟨(-2703907396865248531985277),(-1359278025087607625442717),true⟩⟩
  | 8,0 => ⟨⟨2092747523789395225284481,4676982183543820982956061,true⟩,⟨(-6481492050701364821180930),(-3686747892015007074991001),true⟩⟩
  | 8,1 => ⟨⟨1703000422858375562693559,4477499758106296832217470,true⟩,⟨(-7127061519737577729042134),(-4076817644489190500019213),true⟩⟩
  | 8,2 => ⟨⟨1310805122061245431742703,4240462414051419876223691,true⟩,⟨(-7656780143993879157099171),(-4392953162182530287374297),true⟩⟩
  | 8,3 => ⟨⟨1023933549492059742581587,4057352462234019615992852,true⟩,⟨(-7983873916748245522304936),(-4582535501528235858226443),true⟩⟩
  | 8,4 => ⟨⟨2402159391741020392922647,4793838819381071754786890,true⟩,⟨(-5834778422691597414768881),(-3292037305847213110992653),true⟩⟩
  | 8,5 => ⟨⟨2609492461638765932223982,4834794514778957472471087,true⟩,⟨(-5282953317929026104941447),(-2952928219798718247368051),true⟩⟩
  | 8,6 => ⟨⟨2729323941525259911035518,4832407539076201994692333,true⟩,⟨(-4882547432466534436194928),(-2705893783301019341127527),true⟩⟩
  | 8,7 => ⟨⟨2785862541036083360611123,4819334751503448310872214,true⟩,⟨(-4656622415873996546213705),(-2566241161558877467837194),true⟩⟩
  | 9,0 => ⟨⟨(-548203116563876807156503),3006857358406329517008337,true⟩,⟨(-9238969402040672596873741),(-5242637211937654870915203),true⟩⟩
  | 9,1 => ⟨⟨(-1088464352387347029372410),2615426719427389094551343,true⟩,⟨(-9531522809364310981436580),(-5380616923670689443736603),true⟩⟩
  | 9,2 => ⟨⟨(-1549704760111839912610767),2270484356046496796390991,true⟩,⟨(-9736821715958560825530822),(-5469835574277661253063915),true⟩⟩
  | 9,3 => ⟨⟨(-1841591258206114481322824),2047437321291411422827219,true⟩,⟨(-9846733289329429336477114),(-5513464215603470082550849),true⟩⟩
  | 9,4 => ⟨⟨(-21690370394715265111736),3373635431576957780244048,true⟩,⟨(-8894591306021366171454783),(-5070004687185062082288266),true⟩⟩
  | 9,5 => ⟨⟨413876735857881119399369,3668551043662731527337924,true⟩,⟨(-8554409661553157741363241),(-4892165394410083023651492),true⟩⟩
  | 9,6 => ⟨⟨726710939071357256121893,3871937406789280813262052,true⟩,⟨(-8276918297598629791029265),(-4743092879235870339028201),true⟩⟩
  | 9,7 => ⟨⟨902232827919498930658678,3982434441907796131661342,true⟩,⟨(-8107593036006699246738304),(-4650676107568814674721974),true⟩⟩
  | 10,0 => ⟨⟨(-4274251815757750155303277),252860756992455616564228,true⟩,⟨(-10186122684591355183096436),(-5408331234608439371852321),true⟩⟩
  | 10,1 => ⟨⟨(-4993658345959006526333729),(-303008432182677398366944),true⟩,⟨(-10078584493477111170612066),(-5238739683452765242255181),true⟩⟩
  | 10,2 => ⟨⟨(-5556824233262300916625198),(-749122805888244966683872),true⟩,⟨(-9915428925514405008485757),(-5055549748597406901368701),true⟩⟩
  | 10,3 => ⟨⟨(-5889188369625370910566359),(-1019147518838506678558762),true⟩,⟨(-9781605968123531351141847),(-4923619278874942928819412),true⟩⟩
  | 10,4 => ⟨⟨(-3509897015336305169377772),828953214538638936314822,true⟩,⟨(-10191221045736551964945465),(-5518272274257521472289123),true⟩⟩
  | 10,5 => ⟨⟨(-2818611806301741743900387),1333944322895038215370826,true⟩,⟨(-10106554212267331275283862),(-5559815683101922324273845),true⟩⟩
  | 10,6 => ⟨⟨(-2292777485545402626793620),1708057203963523822689692,true⟩,⟨(-9987159082862424226344732),(-5555543287117874270905165),true⟩⟩
  | 10,7 => ⟨⟨(-1986777209561612565519202),1935172177337029318657176,true⟩,⟨(-9895788460606064564188483),(-5531570671962701833018850),true⟩⟩
  | 11,0 => ⟨⟨(-7933885171302497356438075),(-2879844756076756734504028),true⟩,⟨(-7909332686553693982813377),(-3455691374147361760352518),true⟩⟩
  | 11,1 => ⟨⟨(-8280643274371839975394458),(-3288641559596256649280736),true⟩,⟨(-7133342826207382001419587),(-2923085147399331449040437),true⟩⟩
  | 11,2 => ⟨⟨(-8483748170810782191560323),(-3558758713328239578444841),true⟩,⟨(-6460223339385553950663846),(-2451543723769166584691799),true⟩⟩
  | 11,3 => ⟨⟨(-8564793869607807402280628),(-3696276462735285245135895),true⟩,⟨(-6034514451098192203906525),(-2158621309978706468839561),true⟩⟩
  | 11,4 => ⟨⟨(-7432731675723968727245273),(-2372476427384140982886270),true⟩,⟨(-8628832459429178802544642),(-3977441592438298977815258),true⟩⟩
  | 11,5 => ⟨⟨(-6866925122138844839887501),(-1851691461629161067928157),true⟩,⟨(-9180734580892485360500633),(-4405066536299926528309076),true⟩⟩
  | 11,6 => ⟨⟨(-6366489251059721298716091),(-1417412024382801016563447),true⟩,⟨(-9532003966710521853165895),(-4697921115730516906611111),true⟩⟩
  | 11,7 => ⟨⟨(-6047603592742648399277654),(-1149856088627195058916894),true⟩,⟨(-9706783659729244937871569),(-4853761903684360224331640),true⟩⟩
  | 12,0 => ⟨⟨(-8056942176357601569812797),(-4065908026791847903160955),true⟩,⟨(-2735314751432360252764936),(-134949207739048371793007),true⟩⟩
  | 12,1 => ⟨⟨(-7610067377032756742446751),(-3972160005583699943411728),true⟩,⟨(-1894298364075594561671805),369521120622157132055936,true⟩⟩
  | 12,2 => ⟨⟨(-7185727306610171304491382),(-3848576277892568888675911),true⟩,⟨(-1286708135655759697172424),768443273441053156972638,true⟩⟩
  | 12,3 => ⟨⟨(-6906687088317731402570616),(-3754158222452399006210487),true⟩,⟨(-949498350902156557928768),977862634277463599515399,true⟩⟩
  | 12,4 => ⟨⟨(-8405665733052334902651161),(-4076660065016372745309558),true⟩,⟨(-3704476829676046069706049),(-688586025217051992852159),true⟩⟩
  | 12,5 => ⟨⟨(-8585514900744770135214503),(-3994226754094454984689846),true⟩,⟨(-4640363885496480826471513),(-1253014819603558904667534),true⟩⟩
  | 12,6 => ⟨⟨(-8619018358230519866672056),(-3863011716420543677266029),true⟩,⟨(-5382761353875432632537241),(-1725376920842037025540937),true⟩⟩
  | 12,7 => ⟨⟨(-8591272101844420395077509),(-3755778085467910247568907),true⟩,⟨(-5823700361383498871600185),(-2016523943959508684850700),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP507Value0_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 0 (0:Fin 8))=sharedDiskP507Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value0_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 0 (1:Fin 8))=sharedDiskP507Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value0_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 0 (2:Fin 8))=sharedDiskP507Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value0_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 0 (3:Fin 8))=sharedDiskP507Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value0_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 0 (4:Fin 8))=sharedDiskP507Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value0_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 0 (5:Fin 8))=sharedDiskP507Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value0_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 0 (6:Fin 8))=sharedDiskP507Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value0_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 0 (7:Fin 8))=sharedDiskP507Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 0 j)=sharedDiskP507Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value0_0
  · exact sharedDiskP507Value0_1
  · exact sharedDiskP507Value0_2
  · exact sharedDiskP507Value0_3
  · exact sharedDiskP507Value0_4
  · exact sharedDiskP507Value0_5
  · exact sharedDiskP507Value0_6
  · exact sharedDiskP507Value0_7
private theorem sharedDiskP507Value1_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 1 (0:Fin 8))=sharedDiskP507Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value1_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 1 (1:Fin 8))=sharedDiskP507Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value1_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 1 (2:Fin 8))=sharedDiskP507Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value1_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 1 (3:Fin 8))=sharedDiskP507Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value1_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 1 (4:Fin 8))=sharedDiskP507Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value1_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 1 (5:Fin 8))=sharedDiskP507Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value1_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 1 (6:Fin 8))=sharedDiskP507Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value1_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 1 (7:Fin 8))=sharedDiskP507Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 1 j)=sharedDiskP507Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value1_0
  · exact sharedDiskP507Value1_1
  · exact sharedDiskP507Value1_2
  · exact sharedDiskP507Value1_3
  · exact sharedDiskP507Value1_4
  · exact sharedDiskP507Value1_5
  · exact sharedDiskP507Value1_6
  · exact sharedDiskP507Value1_7
private theorem sharedDiskP507Value2_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 2 (0:Fin 8))=sharedDiskP507Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value2_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 2 (1:Fin 8))=sharedDiskP507Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value2_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 2 (2:Fin 8))=sharedDiskP507Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value2_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 2 (3:Fin 8))=sharedDiskP507Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value2_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 2 (4:Fin 8))=sharedDiskP507Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value2_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 2 (5:Fin 8))=sharedDiskP507Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value2_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 2 (6:Fin 8))=sharedDiskP507Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value2_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 2 (7:Fin 8))=sharedDiskP507Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 2 j)=sharedDiskP507Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value2_0
  · exact sharedDiskP507Value2_1
  · exact sharedDiskP507Value2_2
  · exact sharedDiskP507Value2_3
  · exact sharedDiskP507Value2_4
  · exact sharedDiskP507Value2_5
  · exact sharedDiskP507Value2_6
  · exact sharedDiskP507Value2_7
private theorem sharedDiskP507Value3_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 3 (0:Fin 8))=sharedDiskP507Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value3_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 3 (1:Fin 8))=sharedDiskP507Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value3_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 3 (2:Fin 8))=sharedDiskP507Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value3_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 3 (3:Fin 8))=sharedDiskP507Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value3_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 3 (4:Fin 8))=sharedDiskP507Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value3_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 3 (5:Fin 8))=sharedDiskP507Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value3_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 3 (6:Fin 8))=sharedDiskP507Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value3_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 3 (7:Fin 8))=sharedDiskP507Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 3 j)=sharedDiskP507Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value3_0
  · exact sharedDiskP507Value3_1
  · exact sharedDiskP507Value3_2
  · exact sharedDiskP507Value3_3
  · exact sharedDiskP507Value3_4
  · exact sharedDiskP507Value3_5
  · exact sharedDiskP507Value3_6
  · exact sharedDiskP507Value3_7
private theorem sharedDiskP507Value4_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 4 (0:Fin 8))=sharedDiskP507Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value4_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 4 (1:Fin 8))=sharedDiskP507Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value4_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 4 (2:Fin 8))=sharedDiskP507Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value4_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 4 (3:Fin 8))=sharedDiskP507Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value4_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 4 (4:Fin 8))=sharedDiskP507Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value4_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 4 (5:Fin 8))=sharedDiskP507Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value4_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 4 (6:Fin 8))=sharedDiskP507Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value4_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 4 (7:Fin 8))=sharedDiskP507Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 4 j)=sharedDiskP507Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value4_0
  · exact sharedDiskP507Value4_1
  · exact sharedDiskP507Value4_2
  · exact sharedDiskP507Value4_3
  · exact sharedDiskP507Value4_4
  · exact sharedDiskP507Value4_5
  · exact sharedDiskP507Value4_6
  · exact sharedDiskP507Value4_7
private theorem sharedDiskP507Value5_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 5 (0:Fin 8))=sharedDiskP507Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value5_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 5 (1:Fin 8))=sharedDiskP507Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value5_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 5 (2:Fin 8))=sharedDiskP507Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value5_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 5 (3:Fin 8))=sharedDiskP507Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value5_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 5 (4:Fin 8))=sharedDiskP507Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value5_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 5 (5:Fin 8))=sharedDiskP507Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value5_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 5 (6:Fin 8))=sharedDiskP507Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value5_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 5 (7:Fin 8))=sharedDiskP507Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 5 j)=sharedDiskP507Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value5_0
  · exact sharedDiskP507Value5_1
  · exact sharedDiskP507Value5_2
  · exact sharedDiskP507Value5_3
  · exact sharedDiskP507Value5_4
  · exact sharedDiskP507Value5_5
  · exact sharedDiskP507Value5_6
  · exact sharedDiskP507Value5_7
private theorem sharedDiskP507Value6_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 6 (0:Fin 8))=sharedDiskP507Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value6_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 6 (1:Fin 8))=sharedDiskP507Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value6_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 6 (2:Fin 8))=sharedDiskP507Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value6_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 6 (3:Fin 8))=sharedDiskP507Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value6_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 6 (4:Fin 8))=sharedDiskP507Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value6_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 6 (5:Fin 8))=sharedDiskP507Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value6_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 6 (6:Fin 8))=sharedDiskP507Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value6_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 6 (7:Fin 8))=sharedDiskP507Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 6 j)=sharedDiskP507Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value6_0
  · exact sharedDiskP507Value6_1
  · exact sharedDiskP507Value6_2
  · exact sharedDiskP507Value6_3
  · exact sharedDiskP507Value6_4
  · exact sharedDiskP507Value6_5
  · exact sharedDiskP507Value6_6
  · exact sharedDiskP507Value6_7
private theorem sharedDiskP507Value7_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 7 (0:Fin 8))=sharedDiskP507Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value7_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 7 (1:Fin 8))=sharedDiskP507Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value7_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 7 (2:Fin 8))=sharedDiskP507Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value7_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 7 (3:Fin 8))=sharedDiskP507Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value7_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 7 (4:Fin 8))=sharedDiskP507Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value7_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 7 (5:Fin 8))=sharedDiskP507Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value7_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 7 (6:Fin 8))=sharedDiskP507Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value7_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 7 (7:Fin 8))=sharedDiskP507Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 7 j)=sharedDiskP507Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value7_0
  · exact sharedDiskP507Value7_1
  · exact sharedDiskP507Value7_2
  · exact sharedDiskP507Value7_3
  · exact sharedDiskP507Value7_4
  · exact sharedDiskP507Value7_5
  · exact sharedDiskP507Value7_6
  · exact sharedDiskP507Value7_7
private theorem sharedDiskP507Value8_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 8 (0:Fin 8))=sharedDiskP507Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value8_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 8 (1:Fin 8))=sharedDiskP507Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value8_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 8 (2:Fin 8))=sharedDiskP507Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value8_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 8 (3:Fin 8))=sharedDiskP507Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value8_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 8 (4:Fin 8))=sharedDiskP507Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value8_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 8 (5:Fin 8))=sharedDiskP507Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value8_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 8 (6:Fin 8))=sharedDiskP507Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value8_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 8 (7:Fin 8))=sharedDiskP507Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 8 j)=sharedDiskP507Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value8_0
  · exact sharedDiskP507Value8_1
  · exact sharedDiskP507Value8_2
  · exact sharedDiskP507Value8_3
  · exact sharedDiskP507Value8_4
  · exact sharedDiskP507Value8_5
  · exact sharedDiskP507Value8_6
  · exact sharedDiskP507Value8_7
private theorem sharedDiskP507Value9_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 9 (0:Fin 8))=sharedDiskP507Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value9_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 9 (1:Fin 8))=sharedDiskP507Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value9_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 9 (2:Fin 8))=sharedDiskP507Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value9_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 9 (3:Fin 8))=sharedDiskP507Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value9_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 9 (4:Fin 8))=sharedDiskP507Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value9_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 9 (5:Fin 8))=sharedDiskP507Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value9_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 9 (6:Fin 8))=sharedDiskP507Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value9_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 9 (7:Fin 8))=sharedDiskP507Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values9_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 9 j)=sharedDiskP507Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value9_0
  · exact sharedDiskP507Value9_1
  · exact sharedDiskP507Value9_2
  · exact sharedDiskP507Value9_3
  · exact sharedDiskP507Value9_4
  · exact sharedDiskP507Value9_5
  · exact sharedDiskP507Value9_6
  · exact sharedDiskP507Value9_7
private theorem sharedDiskP507Value10_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 10 (0:Fin 8))=sharedDiskP507Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value10_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 10 (1:Fin 8))=sharedDiskP507Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value10_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 10 (2:Fin 8))=sharedDiskP507Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value10_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 10 (3:Fin 8))=sharedDiskP507Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value10_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 10 (4:Fin 8))=sharedDiskP507Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value10_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 10 (5:Fin 8))=sharedDiskP507Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value10_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 10 (6:Fin 8))=sharedDiskP507Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value10_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 10 (7:Fin 8))=sharedDiskP507Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values10_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 10 j)=sharedDiskP507Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value10_0
  · exact sharedDiskP507Value10_1
  · exact sharedDiskP507Value10_2
  · exact sharedDiskP507Value10_3
  · exact sharedDiskP507Value10_4
  · exact sharedDiskP507Value10_5
  · exact sharedDiskP507Value10_6
  · exact sharedDiskP507Value10_7
private theorem sharedDiskP507Value11_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 11 (0:Fin 8))=sharedDiskP507Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value11_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 11 (1:Fin 8))=sharedDiskP507Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value11_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 11 (2:Fin 8))=sharedDiskP507Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value11_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 11 (3:Fin 8))=sharedDiskP507Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value11_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 11 (4:Fin 8))=sharedDiskP507Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value11_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 11 (5:Fin 8))=sharedDiskP507Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value11_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 11 (6:Fin 8))=sharedDiskP507Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value11_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 11 (7:Fin 8))=sharedDiskP507Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values11_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 11 j)=sharedDiskP507Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value11_0
  · exact sharedDiskP507Value11_1
  · exact sharedDiskP507Value11_2
  · exact sharedDiskP507Value11_3
  · exact sharedDiskP507Value11_4
  · exact sharedDiskP507Value11_5
  · exact sharedDiskP507Value11_6
  · exact sharedDiskP507Value11_7
private theorem sharedDiskP507Value12_0 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 12 (0:Fin 8))=sharedDiskP507Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value12_1 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 12 (1:Fin 8))=sharedDiskP507Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value12_2 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 12 (2:Fin 8))=sharedDiskP507Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value12_3 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 12 (3:Fin 8))=sharedDiskP507Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value12_4 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 12 (4:Fin 8))=sharedDiskP507Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value12_5 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 12 (5:Fin 8))=sharedDiskP507Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value12_6 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 12 (6:Fin 8))=sharedDiskP507Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP507Value12_7 : truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 12 (7:Fin 8))=sharedDiskP507Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP507Values12_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points 12 j)=sharedDiskP507Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP507Value12_0
  · exact sharedDiskP507Value12_1
  · exact sharedDiskP507Value12_2
  · exact sharedDiskP507Value12_3
  · exact sharedDiskP507Value12_4
  · exact sharedDiskP507Value12_5
  · exact sharedDiskP507Value12_6
  · exact sharedDiskP507Value12_7
theorem sharedDiskP507Values_eq : ∀ (i : Fin 13) (j : Fin 8), truncatedChordCell 2 sharedDiskP507Params (sharedChord493Gauss8Points i j)=sharedDiskP507Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP507Values0_eq
  · exact sharedDiskP507Values1_eq
  · exact sharedDiskP507Values2_eq
  · exact sharedDiskP507Values3_eq
  · exact sharedDiskP507Values4_eq
  · exact sharedDiskP507Values5_eq
  · exact sharedDiskP507Values6_eq
  · exact sharedDiskP507Values7_eq
  · exact sharedDiskP507Values8_eq
  · exact sharedDiskP507Values9_eq
  · exact sharedDiskP507Values10_eq
  · exact sharedDiskP507Values11_eq
  · exact sharedDiskP507Values12_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP507Box : HorizontalRectangle := ⟨(143/200),(29/40),(904080147915859/1649267441664000),(918935207220221/1649267441664000),(514100594659378944793252179391453/2596148429267413814265248164610048),(3928481979492009799233612474685457/1298074214633706907132624082305024),(-1411139732604085152116185312608237/324518553658426726783156020576256),(-1839121215568778842002683324596147/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP507Grid : CGrid := momentChordGrid sharedDiskP507Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984)
theorem sharedDiskP507Columns : containedInReported sharedDiskP507Grid.re sharedDiskP507Box.reLo sharedDiskP507Box.reHi=true ∧ containedInReported sharedDiskP507Grid.im sharedDiskP507Box.imLo sharedDiskP507Box.imHi=true := by
  rw [sharedDiskP507Grid,momentChordGrid_eq_tabulated sharedDiskP507Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984) sharedChord493Gauss8Points sharedChord493Gauss8Weights sharedDiskP507Values sharedChord493Gauss8Points_eq sharedChord493Gauss8Weights_eq sharedDiskP507Values_eq]
  decide +kernel
theorem sharedDiskP507Sound : sharedDiskP507Box.Sound := by
  intro t a tl tu al au
  change (((143/200):ℚ):ℝ)≤t at tl
  change t≤(((29/40):ℚ):ℝ) at tu
  change (((904080147915859/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((918935207220221/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP507Params_ok] at ps
  have band := sharedChord493ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(143/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((29/40):ℚ)≤(3/4)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((878940159632233/1649267441664000):ℚ)≤(904080147915859/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((918935207220221/1649267441664000):ℚ)≤(929134916903873/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord493Bd (by decide +kernel) (by decide +kernel) sharedChord493M (by decide +kernel) (sharedChord493Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP507Columns.1 sharedDiskP507Columns.2
def sharedDiskP507Rows : List SignRow := [positive_507.toSignRow, positive_508.toSignRow]
theorem sharedDiskP507Rows_actual : ∀ r∈sharedDiskP507Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP507Rows.all (sharedDiskP507Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP507Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP509Params : ChordParams := ⟨⟨(-16830820727356637357446),(-15867234275413482436745),true⟩,⟨2275623409999350768058220,2354343059928077379368077,true⟩,⟨106972445402167803717862,114913831759012478979959,true⟩,⟨172435035104925286830682,184036834614701134654134,true⟩,⟨273196944453219003640050,281591413421754395296869,true⟩,⟨1175726384958611901709354,1177602472147076183579382,true⟩,⟨(-2551411914032023206511844),(-2512689369807932198378277),true⟩,⟨⟨1118584924123579032544626,1235386730123317216519499,true⟩,⟨(-248707),248707,true⟩⟩⟩
theorem sharedDiskP509Params_ok : chordParams (Grid.ofRats (29/40) (147/200)) (Grid.ofRats (908043715960367/1649267441664000) (922945286541007/1649267441664000))=sharedDiskP509Params := by decide +kernel
def sharedDiskP509Values (i : Fin 13) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-5369937800425972713759941),(-2726541100095933515446572),true⟩,⟨(-1060565626384460746761807),1025566512982071992126798,true⟩⟩
  | 0,1 => ⟨⟨(-5014280322667557445250235),(-2486227236609646938088549),true⟩,⟨(-1093310740426156305427568),949964212193139414111673,true⟩⟩
  | 0,2 => ⟨⟨(-4742553470893695852408387),(-2309071981747380590160238),true⟩,⟨(-1121249647325194079776742),875390673865436104349123,true⟩⟩
  | 0,3 => ⟨⟨(-4583177374934635111027677),(-2207862155060801263690871),true⟩,⟨(-1137268315942426092529190),825424058043263372665247,true⟩⟩
  | 0,4 => ⟨⟨(-5765732083631321523895555),(-3005220030881763124336532),true⟩,⟨(-1039487832879562658749033),1077605740855822908355308,true⟩⟩
  | 0,5 => ⟨⟨(-6146422888094779901523383),(-3284796774113782316526518),true⟩,⟨(-1023811776216747387019727),1093170215740007925937058,true⟩⟩
  | 0,6 => ⟨⟨(-6454816291646267169833572),(-3522449962692008683768708),true⟩,⟨(-1015141296158841249247319),1079539152394432402919293,true⟩⟩
  | 0,7 => ⟨⟨(-6643608270120358412822657),(-3673486658185078854831565),true⟩,⟨(-1011909590625628721474285),1059241674381116175307461,true⟩⟩
  | 1,0 => ⟨⟨(-3510598553265969506324578),(-1571211024815343009713168),true⟩,⟨(-1236042573412832847576097),435736464253796004760477,true⟩⟩
  | 1,1 => ⟨⟨(-3248459268567452465571378),(-1425630531457586616160642),true⟩,⟨(-1257275175434637875954773),329275676902858905918674,true⟩⟩
  | 1,2 => ⟨⟨(-3052023949145040299289350),(-1318563206247096273355362),true⟩,⟨(-1272283558247992665202244),246104835198726047635516,true⟩⟩
  | 1,3 => ⟨⟨(-2938193634841331796851945),(-1257197185592425231401601),true⟩,⟨(-1280601125087514255519854),196829016413756456003013,true⟩⟩
  | 1,4 => ⟨⟨(-3809871480481883674117071),(-1741840628406815037900233),true⟩,⟨(-1210249273512324373980480),549485039248788989934924,true⟩⟩
  | 1,5 => ⟨⟨(-4106060401502205115409666),(-1916029059534477352648617),true⟩,⟨(-1183225976430850266997461),652286788523313094550128,true⟩⟩
  | 1,6 => ⟨⟨(-4353087631987335347935838),(-2065113148602615385095923),true⟩,⟨(-1159828914505231642632782),745820990539865766710501,true⟩⟩
  | 1,7 => ⟨⟨(-4507106896813979525352334),(-2160235030738623099919536),true⟩,⟨(-1144804629559976818413120),800050845096330049766563,true⟩⟩
  | 2,0 => ⟨⟨(-2192570173095331308658168),(-861988177167745259329444),true⟩,⟨(-1326889234519888335076840),(-131516545136903972695172),true⟩⟩
  | 2,1 => ⟨⟨(-2018253853286795537836508),(-767604311868126114635514),true⟩,⟨(-1335292700827822685783365),(-200572355338073645917505),true⟩⟩
  | 2,2 => ⟨⟨(-1887773997089490948880607),(-696746131908738590548954),true⟩,⟨(-1340667007990483334851982),(-251649818221003227530177),true⟩⟩
  | 2,3 => ⟨⟨(-1812115097123838001387408),(-655516442663902611250285),true⟩,⟨(-1343378320003494724704215),(-280912594591469487982694),true⟩⟩
  | 2,4 => ⟨⟨(-2396946518835523703038757),(-970196003418116969824310),true⟩,⟨(-1315771807158622867641070),(-43473925455973144794843),true⟩⟩
  | 2,5 => ⟨⟨(-2602615536529085172682032),(-1078547022448624482914427),true⟩,⟨(-1303333064010257326760733),48265870378820565293106,true⟩⟩
  | 2,6 => ⟨⟨(-2775472325991920166411280),(-1170202095140249079644807),true⟩,⟨(-1291973276779679002193863),125295456770928961086349,true⟩⟩
  | 2,7 => ⟨⟨(-2884194144645728185727312),(-1228239197939599359026651),true⟩,⟨(-1284444368700744131721347),173219511442875569688301,true⟩⟩
  | 3,0 => ⟨⟨(-1310606632616281680689937),(-369139637158447290905594),true⟩,⟨(-1362199091595877136977555),(-462861413304158853652426),true⟩⟩
  | 3,1 => ⟨⟨(-1187753512246398181025629),(-295355672943433402539762),true⟩,⟨(-1365217128015208418511951),(-502977597847783873921851),true⟩⟩
  | 3,2 => ⟨⟨(-1094967103847424929069530),(-238777192235163374316178),true⟩,⟨(-1366472055650159360873726),(-531783318342915875674229),true⟩⟩
  | 3,3 => ⟨⟨(-1040801942096299476260140),(-205388908448551070415673),true⟩,⟨(-1366758648415492409177285),(-547951258287981230586916),true⟩⟩
  | 3,4 => ⟨⟨(-1450174736388153815770156),(-451537689477368194417808),true⟩,⟨(-1357118237069173022880572),(-414881850950353250299941),true⟩⟩
  | 3,5 => ⟨⟨(-1588319398138256025459601),(-531771619331957068016880),true⟩,⟨(-1350604949444267159373831),(-365252456329834233998567),true⟩⟩
  | 3,6 => ⟨⟨(-1703781430339136820090339),(-596232994336753309335326),true⟩,⟨(-1346686916079411691756855),(-322232104458329579671430),true⟩⟩
  | 3,7 => ⟨⟨(-1776193160476503106941221),(-635894315409458267314072),true⟩,⟨(-1344553045898579844499372),(-294695461800711962328452),true⟩⟩
  | 4,0 => ⟨⟨73954104582942595342851,621402186664003760491806,true⟩,⟨(-1275831457097303671911665),(-691461954544805429484914),true⟩⟩
  | 4,1 => ⟨⟨295197906176244643952961,823396646335046263230992,true⟩,⟨(-1228835002327733328633250),(-671154962216639307058854),true⟩⟩
  | 4,2 => ⟨⟨444518710502972666190032,971696073038431658494775,true⟩,⟨(-1195165206548802178284209),(-648316064511610989057458),true⟩⟩
  | 4,3 => ⟨⟨529253776729294694198079,1056677360030701441005927,true⟩,⟨(-1173977936681398839754199),(-632637505163212664981653),true⟩⟩
  | 4,4 => ⟨⟨(-202330261194399807031794),383133531711750561473271,true⟩,⟨(-1320382289056784781281128),(-696736017044772507989728),true⟩⟩
  | 4,5 => ⟨⟨(-502818336668911092770930),156644203882954839341250,true⟩,⟨(-1350439394285217216851991),(-666294814587364927814875),true⟩⟩
  | 4,6 => ⟨⟨(-779583042615618358688062),(-39567744991292189052298),true⟩,⟨(-1363125762424229811094660),(-617604841957297541071977),true⟩⟩
  | 4,7 => ⟨⟨(-976823818186434238144653),(-165595495049547765588258),true⟩,⟨(-1366644434908698270779635),(-566393504076999594882797),true⟩⟩
  | 5,0 => ⟨⟨1464498594899310626984116,2027290521947851996760282,true⟩,⟨(-916171634315416575686401),(-402235388467489884806911),true⟩⟩
  | 5,1 => ⟨⟨1663881680636600371011702,2243502061188961472106857,true⟩,⟨(-889174419475578669496976),(-368915365396643948592035),true⟩⟩
  | 5,2 => ⟨⟨1811641039105266241893397,2407728451127749400387545,true⟩,⟨(-889174071644451113781388),(-358917837452690652065410),true⟩⟩
  | 5,3 => ⟨⟨1898064765830720082368881,2505968924700610952634796,true⟩,⟨(-899833029308697207114578),(-360956319895490940968472),true⟩⟩
  | 5,4 => ⟨⟨1226395432223211155392001,1774524217576596262451571,true⟩,⟨(-973164566933176924338407),(-459272955768924003953371),true⟩⟩
  | 5,5 => ⟨⟨972585516221688646401432,1509600586438220681523464,true⟩,⟨(-1047068189819570411364378),(-527134255182912355220364),true⟩⟩
  | 5,6 => ⟨⟨742674027626169996227764,1273086868160083670470011,true⟩,⟨(-1115312940430121529080728),(-585847831803691086406559),true⟩⟩
  | 5,7 => ⟨⟨588636521381653984887390,1116563424708291036675517,true⟩,⟨(-1158344919051407689253313),(-620595176060382804959799),true⟩⟩
  | 6,0 => ⟨⟨2500610480874779714065813,3409828689292442842602522,true⟩,⟨(-1443938919995851243453415),(-620812179626320167811518),true⟩⟩
  | 6,1 => ⟨⟨2674867574936074138868518,3745434446900612221962596,true⟩,⟨(-1844243029808341869114421),(-853986000965887049373239),true⟩⟩
  | 6,2 => ⟨⟨2798844529619866231613345,4044034857602195113619403,true⟩,⟨(-2317978632286947270078411),(-1139463724796712529682751),true⟩⟩
  | 6,3 => ⟨⟨2854208989441318765082133,4232620230130910769110154,true⟩,⟨(-2699685251945850750579996),(-1373169918208033237787103),true⟩⟩
  | 6,4 => ⟨⟨2315187624875009117971375,3100013285628787041474866,true⟩,⟨(-1173208797126846225539264),(-473184619033104574982818),true⟩⟩
  | 6,5 => ⟨⟨2147982582033755909478967,2846777435167441345148349,true⟩,⟨(-1017277893205200271731295),(-398356267442136557827729),true⟩⟩
  | 6,6 => ⟨⟨2017333390792821850872407,2662280998147842737311072,true⟩,⟨(-940313482632985189240917),(-369798041483753236433528),true⟩⟩
  | 6,7 => ⟨⟨1938019741679156950188108,2555240738011838484766325,true⟩,⟨(-909561428568142979820022),(-363016902906922819222177),true⟩⟩
  | 7,0 => ⟨⟨2846769551213682075093198,4589617367710218456817447,true⟩,⟨(-3807276804793868194845786),(-2058988458775218162626946),true⟩⟩
  | 7,1 => ⟨⟨2796072538730425299944582,4656356908221303002784084,true⟩,⟨(-4179313628776979030172919),(-2290215660179600284230338),true⟩⟩
  | 7,2 => ⟨⟨2733223181685824234687255,4694841595969482097625355,true⟩,⟨(-4505035689948046774949268),(-2492591181535231789912611),true⟩⟩
  | 7,3 => ⟨⟨2683551328745351820012543,4710011507662899694847580,true⟩,⟨(-4715517407016385833433908),(-2623256145963917659715817),true⟩⟩
  | 7,4 => ⟨⟨2873499145742282973830721,4502449819443806866847469,true⟩,⟨(-3452778044913005105366741),(-1838826494242265304357834),true⟩⟩
  | 7,5 => ⟨⟨2878890318203617838350490,4411902010550220463537216,true⟩,⟨(-3159667735394536429097556),(-1657125224712476588487286),true⟩⟩
  | 7,6 => ⟨⟨2872922546718809209861003,4336312006881135547844240,true⟩,⟨(-2950492776278474946029884),(-1527768802146763617123513),true⟩⟩
  | 7,7 => ⟨⟨2865805252504082961531499,4289717475946774743162964,true⟩,⟨(-2833330901100120347913679),(-1455470240089474273489861),true⟩⟩
  | 8,0 => ⟨⟨1890819559918549500306906,4489947362960131985367713,true⟩,⟨(-6628034810022576472503072),(-3800184822745493739525119),true⟩⟩
  | 8,1 => ⟨⟨1476793206696098946799414,4258639349238912535520195,true⟩,⟨(-7252404659815118311004825),(-4177420428265250434436379),true⟩⟩
  | 8,2 => ⟨⟨1060812359953419979355744,3995277163724240814802041,true⟩,⟨(-7760720971324172457753649),(-4478458696356291261385352),true⟩⟩
  | 8,3 => ⟨⟨740646836978607524435443,3796348650230710542473226,true⟩,⟨(-8082582873334858662664983),(-4656529472400423208931161),true⟩⟩
  | 8,4 => ⟨⟨2225682943100822381971637,4637692183612209637501289,true⟩,⟨(-5994301369348782246817085),(-3413021198406578076169561),true⟩⟩
  | 8,5 => ⟨⟨2454958180734013565414019,4703728634944045809594707,true⟩,⟨(-5447767257035438058137639),(-3076579358544788914204910),true⟩⟩
  | 8,6 => ⟨⟨2590545804703427381664819,4718569249300391525900889,true⟩,⟨(-5048131500237948634022462),(-2829457767467101932379681),true⟩⟩
  | 8,7 => ⟨⟨2655835136649366808807480,4714789580774211127775736,true⟩,⟨(-4821558651050168129288896),(-2689038009924216953474159),true⟩⟩
  | 9,0 => ⟨⟨(-861495845943564440334132),2693736922212679357601840,true⟩,⟨(-9236928816014667995621181),(-5253838300446899136462297),true⟩⟩
  | 9,1 => ⟨⟨(-1400407707365801511036238),2293478672188042656116701,true⟩,⟨(-9493638638609988873719200),(-5370042129954117691730254),true⟩⟩
  | 9,2 => ⟨⟨(-1857028955488010747262743),1944150808577466992927199,true⟩,⟨(-9668294090079710265892803),(-5440878475225505669880952),true⟩⟩
  | 9,3 => ⟨⟨(-2144423926093459572941160),1727326209093295253399691,true⟩,⟨(-9758902148324196860288629),(-5469012773006945318791023),true⟩⟩
  | 9,4 => ⟨⟨(-331756043526406935477675),3073193101518379279090566,true⟩,⟨(-8927058306643075133270460),(-5102445316799431922712782),true⟩⟩
  | 9,5 => ⟨⟨114984029374880152539458,3382116736445080245758776,true⟩,⟨(-8615184092702857407032139),(-4942233537061253684097087),true⟩⟩
  | 9,6 => ⟨⟨434797487222511173344589,3597642507359062381923152,true⟩,⟨(-8357461505119294165290829),(-4805584455308374525042581),true⟩⟩
  | 9,7 => ⟨⟨615165855762277576278795,3715771124710799448439529,true⟩,⟨(-8198947501416503837321614),(-4720002988088174481661128),true⟩⟩
  | 10,0 => ⟨⟨(-4495780927127200534100304),(-15305462113825120018764),true⟩,⟨(-9947483820951720431165840),(-5266806256678001095066257),true⟩⟩
  | 10,1 => ⟨⟨(-5176582861723165861650158),(-547500356280330012647699),true⟩,⟨(-9801765120470726579677611),(-5078526045369898570360584),true⟩⟩
  | 10,2 => ⟨⟨(-5704737993193205036575172),(-973959999710322196183455),true⟩,⟨(-9612089272315804597217824),(-4883474052008966289779151),true⟩⟩
  | 10,3 => ⟨⟨(-6014359338482492733171329),(-1230544718238327115502771),true⟩,⟨(-9464362584565501623062264),(-4745916802974778174646354),true⟩⟩
  | 10,4 => ⟨⟨(-3765173418574247277527523),545378495184919047739553,true⟩,⟨(-9997140053032637221196657),(-5400112529221962854243096),true⟩⟩
  | 10,5 => ⟨⟨(-3098000033251989010735260),1042085169657744390529998,true⟩,⟨(-9955361566673196900340130),(-5465291235954795922902925),true⟩⟩
  | 10,6 => ⟨⟨(-2586363876471099565826702),1413366524116433900640701,true⟩,⟨(-9869767650472389786083085),(-5480291748958507067817047),true⟩⟩
  | 10,7 => ⟨⟨(-2286936106615041223785625),1626775292188501591856814,true⟩,⟨(-9798401604453924753793083),(-5475115041998240426945954),true⟩⟩
  | 11,0 => ⟨⟨(-7874602630539371640969449),(-2966486259193682423043269),true⟩,⟨(-7560121179969059386764384),(-3282084116693215894956379),true⟩⟩
  | 11,1 => ⟨⟨(-8175639689117232205906460),(-3339203369587281077606627),true⟩,⟨(-6802041626268286409389716),(-2765992013485305234475962),true⟩⟩
  | 11,2 => ⟨⟨(-8351202307394224092654227),(-3582771275049602250788000),true⟩,⟨(-6151355966888658312106220),(-2307185059305033550732426),true⟩⟩
  | 11,3 => ⟨⟨(-8415155250327561906360131),(-3705689044409201453145004),true⟩,⟨(-5742196184838902921156638),(-2027636208013362342295655),true⟩⟩
  | 11,4 => ⟨⟨(-7428053197180715045361977),(-2498995909094765985569823),true⟩,⟨(-8273947507882588208816519),(-3793429449659943313113149),true⟩⟩
  | 11,5 => ⟨⟨(-6915157230182471103627016),(-2014388076295866636185905),true⟩,⟨(-8832944419240836709251955),(-4218566279270008036139636),true⟩⟩
  | 11,6 => ⟨⟨(-6456095818420859232192830),(-1606884198563291872005349),true⟩,⟨(-9197618588648620718366088),(-4514283108117787419156279),true⟩⟩
  | 11,7 => ⟨⟨(-6161362707339222501730154),(-1354333507539004070480051),true⟩,⟨(-9383450228761293344967065),(-4673788627515562179558404),true⟩⟩
  | 12,0 => ⟨⟨(-7871624525775715211033904),(-4012875540111804801387225),true⟩,⟨(-2608211047369386776247267),(-107856128158842327592893),true⟩⟩
  | 12,1 => ⟨⟨(-7442072607692858115603154),(-3917583959242002217500878),true⟩,⟨(-1813405403692973105437464),372139837728199767142780,true⟩⟩
  | 12,2 => ⟨⟨(-7037826724693481730446344),(-3796918012387126224853341),true⟩,⟨(-1238448926180798532536243),750032496681844907160039,true⟩⟩
  | 12,3 => ⟨⟨(-6772887082158943144244524),(-3705718381627379068559296),true⟩,⟨(-918716179233376633692772),949198240855068060664697,true⟩⟩
  | 12,4 => ⟨⟨(-8213451548021750397361804),(-4032834379322058625713626),true⟩,⟨(-3524596113676744667453735),(-633838606021080585635218),true⟩⟩
  | 12,5 => ⟨⟨(-8400382829307929533926708),(-3966507065526507889575118),true⟩,⟨(-4411932251403851434748119),(-1167703160739131914816447),true⟩⟩
  | 12,6 => ⟨⟨(-8448986568816242750226594),(-3853075440143428803618102),true⟩,⟨(-5118719059922228295443166),(-1615547377051062914731284),true⟩⟩
  | 12,7 => ⟨⟨(-8434287748841789904210303),(-3758541428600561117060098),true⟩,⟨(-5540171322093316571642337),(-1892311563455538562005963),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP509Value0_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 0 (0:Fin 8))=sharedDiskP509Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value0_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 0 (1:Fin 8))=sharedDiskP509Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value0_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 0 (2:Fin 8))=sharedDiskP509Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value0_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 0 (3:Fin 8))=sharedDiskP509Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value0_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 0 (4:Fin 8))=sharedDiskP509Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value0_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 0 (5:Fin 8))=sharedDiskP509Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value0_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 0 (6:Fin 8))=sharedDiskP509Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value0_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 0 (7:Fin 8))=sharedDiskP509Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 0 j)=sharedDiskP509Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value0_0
  · exact sharedDiskP509Value0_1
  · exact sharedDiskP509Value0_2
  · exact sharedDiskP509Value0_3
  · exact sharedDiskP509Value0_4
  · exact sharedDiskP509Value0_5
  · exact sharedDiskP509Value0_6
  · exact sharedDiskP509Value0_7
private theorem sharedDiskP509Value1_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 1 (0:Fin 8))=sharedDiskP509Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value1_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 1 (1:Fin 8))=sharedDiskP509Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value1_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 1 (2:Fin 8))=sharedDiskP509Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value1_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 1 (3:Fin 8))=sharedDiskP509Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value1_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 1 (4:Fin 8))=sharedDiskP509Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value1_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 1 (5:Fin 8))=sharedDiskP509Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value1_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 1 (6:Fin 8))=sharedDiskP509Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value1_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 1 (7:Fin 8))=sharedDiskP509Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 1 j)=sharedDiskP509Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value1_0
  · exact sharedDiskP509Value1_1
  · exact sharedDiskP509Value1_2
  · exact sharedDiskP509Value1_3
  · exact sharedDiskP509Value1_4
  · exact sharedDiskP509Value1_5
  · exact sharedDiskP509Value1_6
  · exact sharedDiskP509Value1_7
private theorem sharedDiskP509Value2_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 2 (0:Fin 8))=sharedDiskP509Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value2_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 2 (1:Fin 8))=sharedDiskP509Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value2_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 2 (2:Fin 8))=sharedDiskP509Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value2_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 2 (3:Fin 8))=sharedDiskP509Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value2_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 2 (4:Fin 8))=sharedDiskP509Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value2_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 2 (5:Fin 8))=sharedDiskP509Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value2_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 2 (6:Fin 8))=sharedDiskP509Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value2_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 2 (7:Fin 8))=sharedDiskP509Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 2 j)=sharedDiskP509Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value2_0
  · exact sharedDiskP509Value2_1
  · exact sharedDiskP509Value2_2
  · exact sharedDiskP509Value2_3
  · exact sharedDiskP509Value2_4
  · exact sharedDiskP509Value2_5
  · exact sharedDiskP509Value2_6
  · exact sharedDiskP509Value2_7
private theorem sharedDiskP509Value3_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 3 (0:Fin 8))=sharedDiskP509Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value3_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 3 (1:Fin 8))=sharedDiskP509Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value3_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 3 (2:Fin 8))=sharedDiskP509Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value3_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 3 (3:Fin 8))=sharedDiskP509Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value3_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 3 (4:Fin 8))=sharedDiskP509Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value3_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 3 (5:Fin 8))=sharedDiskP509Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value3_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 3 (6:Fin 8))=sharedDiskP509Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value3_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 3 (7:Fin 8))=sharedDiskP509Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 3 j)=sharedDiskP509Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value3_0
  · exact sharedDiskP509Value3_1
  · exact sharedDiskP509Value3_2
  · exact sharedDiskP509Value3_3
  · exact sharedDiskP509Value3_4
  · exact sharedDiskP509Value3_5
  · exact sharedDiskP509Value3_6
  · exact sharedDiskP509Value3_7
private theorem sharedDiskP509Value4_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 4 (0:Fin 8))=sharedDiskP509Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value4_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 4 (1:Fin 8))=sharedDiskP509Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value4_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 4 (2:Fin 8))=sharedDiskP509Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value4_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 4 (3:Fin 8))=sharedDiskP509Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value4_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 4 (4:Fin 8))=sharedDiskP509Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value4_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 4 (5:Fin 8))=sharedDiskP509Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value4_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 4 (6:Fin 8))=sharedDiskP509Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value4_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 4 (7:Fin 8))=sharedDiskP509Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 4 j)=sharedDiskP509Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value4_0
  · exact sharedDiskP509Value4_1
  · exact sharedDiskP509Value4_2
  · exact sharedDiskP509Value4_3
  · exact sharedDiskP509Value4_4
  · exact sharedDiskP509Value4_5
  · exact sharedDiskP509Value4_6
  · exact sharedDiskP509Value4_7
private theorem sharedDiskP509Value5_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 5 (0:Fin 8))=sharedDiskP509Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value5_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 5 (1:Fin 8))=sharedDiskP509Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value5_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 5 (2:Fin 8))=sharedDiskP509Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value5_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 5 (3:Fin 8))=sharedDiskP509Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value5_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 5 (4:Fin 8))=sharedDiskP509Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value5_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 5 (5:Fin 8))=sharedDiskP509Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value5_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 5 (6:Fin 8))=sharedDiskP509Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value5_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 5 (7:Fin 8))=sharedDiskP509Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 5 j)=sharedDiskP509Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value5_0
  · exact sharedDiskP509Value5_1
  · exact sharedDiskP509Value5_2
  · exact sharedDiskP509Value5_3
  · exact sharedDiskP509Value5_4
  · exact sharedDiskP509Value5_5
  · exact sharedDiskP509Value5_6
  · exact sharedDiskP509Value5_7
private theorem sharedDiskP509Value6_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 6 (0:Fin 8))=sharedDiskP509Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value6_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 6 (1:Fin 8))=sharedDiskP509Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value6_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 6 (2:Fin 8))=sharedDiskP509Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value6_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 6 (3:Fin 8))=sharedDiskP509Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value6_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 6 (4:Fin 8))=sharedDiskP509Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value6_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 6 (5:Fin 8))=sharedDiskP509Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value6_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 6 (6:Fin 8))=sharedDiskP509Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value6_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 6 (7:Fin 8))=sharedDiskP509Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 6 j)=sharedDiskP509Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value6_0
  · exact sharedDiskP509Value6_1
  · exact sharedDiskP509Value6_2
  · exact sharedDiskP509Value6_3
  · exact sharedDiskP509Value6_4
  · exact sharedDiskP509Value6_5
  · exact sharedDiskP509Value6_6
  · exact sharedDiskP509Value6_7
private theorem sharedDiskP509Value7_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 7 (0:Fin 8))=sharedDiskP509Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value7_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 7 (1:Fin 8))=sharedDiskP509Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value7_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 7 (2:Fin 8))=sharedDiskP509Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value7_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 7 (3:Fin 8))=sharedDiskP509Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value7_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 7 (4:Fin 8))=sharedDiskP509Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value7_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 7 (5:Fin 8))=sharedDiskP509Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value7_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 7 (6:Fin 8))=sharedDiskP509Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value7_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 7 (7:Fin 8))=sharedDiskP509Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 7 j)=sharedDiskP509Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value7_0
  · exact sharedDiskP509Value7_1
  · exact sharedDiskP509Value7_2
  · exact sharedDiskP509Value7_3
  · exact sharedDiskP509Value7_4
  · exact sharedDiskP509Value7_5
  · exact sharedDiskP509Value7_6
  · exact sharedDiskP509Value7_7
private theorem sharedDiskP509Value8_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 8 (0:Fin 8))=sharedDiskP509Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value8_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 8 (1:Fin 8))=sharedDiskP509Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value8_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 8 (2:Fin 8))=sharedDiskP509Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value8_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 8 (3:Fin 8))=sharedDiskP509Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value8_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 8 (4:Fin 8))=sharedDiskP509Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value8_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 8 (5:Fin 8))=sharedDiskP509Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value8_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 8 (6:Fin 8))=sharedDiskP509Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value8_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 8 (7:Fin 8))=sharedDiskP509Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 8 j)=sharedDiskP509Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value8_0
  · exact sharedDiskP509Value8_1
  · exact sharedDiskP509Value8_2
  · exact sharedDiskP509Value8_3
  · exact sharedDiskP509Value8_4
  · exact sharedDiskP509Value8_5
  · exact sharedDiskP509Value8_6
  · exact sharedDiskP509Value8_7
private theorem sharedDiskP509Value9_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 9 (0:Fin 8))=sharedDiskP509Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value9_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 9 (1:Fin 8))=sharedDiskP509Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value9_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 9 (2:Fin 8))=sharedDiskP509Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value9_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 9 (3:Fin 8))=sharedDiskP509Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value9_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 9 (4:Fin 8))=sharedDiskP509Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value9_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 9 (5:Fin 8))=sharedDiskP509Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value9_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 9 (6:Fin 8))=sharedDiskP509Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value9_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 9 (7:Fin 8))=sharedDiskP509Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values9_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 9 j)=sharedDiskP509Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value9_0
  · exact sharedDiskP509Value9_1
  · exact sharedDiskP509Value9_2
  · exact sharedDiskP509Value9_3
  · exact sharedDiskP509Value9_4
  · exact sharedDiskP509Value9_5
  · exact sharedDiskP509Value9_6
  · exact sharedDiskP509Value9_7
private theorem sharedDiskP509Value10_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 10 (0:Fin 8))=sharedDiskP509Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value10_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 10 (1:Fin 8))=sharedDiskP509Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value10_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 10 (2:Fin 8))=sharedDiskP509Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value10_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 10 (3:Fin 8))=sharedDiskP509Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value10_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 10 (4:Fin 8))=sharedDiskP509Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value10_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 10 (5:Fin 8))=sharedDiskP509Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value10_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 10 (6:Fin 8))=sharedDiskP509Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value10_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 10 (7:Fin 8))=sharedDiskP509Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values10_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 10 j)=sharedDiskP509Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value10_0
  · exact sharedDiskP509Value10_1
  · exact sharedDiskP509Value10_2
  · exact sharedDiskP509Value10_3
  · exact sharedDiskP509Value10_4
  · exact sharedDiskP509Value10_5
  · exact sharedDiskP509Value10_6
  · exact sharedDiskP509Value10_7
private theorem sharedDiskP509Value11_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 11 (0:Fin 8))=sharedDiskP509Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value11_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 11 (1:Fin 8))=sharedDiskP509Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value11_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 11 (2:Fin 8))=sharedDiskP509Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value11_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 11 (3:Fin 8))=sharedDiskP509Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value11_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 11 (4:Fin 8))=sharedDiskP509Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value11_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 11 (5:Fin 8))=sharedDiskP509Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value11_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 11 (6:Fin 8))=sharedDiskP509Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value11_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 11 (7:Fin 8))=sharedDiskP509Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values11_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 11 j)=sharedDiskP509Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value11_0
  · exact sharedDiskP509Value11_1
  · exact sharedDiskP509Value11_2
  · exact sharedDiskP509Value11_3
  · exact sharedDiskP509Value11_4
  · exact sharedDiskP509Value11_5
  · exact sharedDiskP509Value11_6
  · exact sharedDiskP509Value11_7
private theorem sharedDiskP509Value12_0 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 12 (0:Fin 8))=sharedDiskP509Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value12_1 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 12 (1:Fin 8))=sharedDiskP509Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value12_2 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 12 (2:Fin 8))=sharedDiskP509Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value12_3 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 12 (3:Fin 8))=sharedDiskP509Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value12_4 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 12 (4:Fin 8))=sharedDiskP509Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value12_5 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 12 (5:Fin 8))=sharedDiskP509Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value12_6 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 12 (6:Fin 8))=sharedDiskP509Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP509Value12_7 : truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 12 (7:Fin 8))=sharedDiskP509Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP509Values12_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points 12 j)=sharedDiskP509Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP509Value12_0
  · exact sharedDiskP509Value12_1
  · exact sharedDiskP509Value12_2
  · exact sharedDiskP509Value12_3
  · exact sharedDiskP509Value12_4
  · exact sharedDiskP509Value12_5
  · exact sharedDiskP509Value12_6
  · exact sharedDiskP509Value12_7
theorem sharedDiskP509Values_eq : ∀ (i : Fin 13) (j : Fin 8), truncatedChordCell 2 sharedDiskP509Params (sharedChord493Gauss8Points i j)=sharedDiskP509Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP509Values0_eq
  · exact sharedDiskP509Values1_eq
  · exact sharedDiskP509Values2_eq
  · exact sharedDiskP509Values3_eq
  · exact sharedDiskP509Values4_eq
  · exact sharedDiskP509Values5_eq
  · exact sharedDiskP509Values6_eq
  · exact sharedDiskP509Values7_eq
  · exact sharedDiskP509Values8_eq
  · exact sharedDiskP509Values9_eq
  · exact sharedDiskP509Values10_eq
  · exact sharedDiskP509Values11_eq
  · exact sharedDiskP509Values12_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP509Box : HorizontalRectangle := ⟨(29/40),(147/200),(908043715960367/1649267441664000),(922945286541007/1649267441664000),(346264121994920395637791607608443/2596148429267413814265248164610048),(3700291389566843982408712910965735/1298074214633706907132624082305024),(-1402183123418891151156839913101083/324518553658426726783156020576256),(-1958491564211763600961929943735403/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP509Grid : CGrid := momentChordGrid sharedDiskP509Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984)
theorem sharedDiskP509Columns : containedInReported sharedDiskP509Grid.re sharedDiskP509Box.reLo sharedDiskP509Box.reHi=true ∧ containedInReported sharedDiskP509Grid.im sharedDiskP509Box.imLo sharedDiskP509Box.imHi=true := by
  rw [sharedDiskP509Grid,momentChordGrid_eq_tabulated sharedDiskP509Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984) sharedChord493Gauss8Points sharedChord493Gauss8Weights sharedDiskP509Values sharedChord493Gauss8Points_eq sharedChord493Gauss8Weights_eq sharedDiskP509Values_eq]
  decide +kernel
theorem sharedDiskP509Sound : sharedDiskP509Box.Sound := by
  intro t a tl tu al au
  change (((29/40):ℚ):ℝ)≤t at tl
  change t≤(((147/200):ℚ):ℝ) at tu
  change (((908043715960367/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((922945286541007/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP509Params_ok] at ps
  have band := sharedChord493ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(29/40))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((147/200):ℚ)≤(3/4)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((878940159632233/1649267441664000):ℚ)≤(908043715960367/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((922945286541007/1649267441664000):ℚ)≤(929134916903873/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord493Bd (by decide +kernel) (by decide +kernel) sharedChord493M (by decide +kernel) (sharedChord493Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP509Columns.1 sharedDiskP509Columns.2
def sharedDiskP509Rows : List SignRow := [positive_509.toSignRow, positive_510.toSignRow]
theorem sharedDiskP509Rows_actual : ∀ r∈sharedDiskP509Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP509Rows.all (sharedDiskP509Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP509Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP503Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP505Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP507Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP509Rows_actual
