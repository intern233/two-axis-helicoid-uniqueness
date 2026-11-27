import TwoAxisHelicoid.PdfSharedChord521Gauss8
import TwoAxisHelicoid.PdfSharedChord521Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP527Params : ChordParams := ⟨⟨(-23238226565097918580625),(-22950339375117034577703),true⟩,⟨2040834202583960596309176,2056632261172643088784336,true⟩,⟨124810497601691772409002,126678863172673673987787,true⟩,⟨220584569902361972827302,223486052259403839320465,true⟩,⟨326855275655977835929370,328975772896301224714438,true⟩,⟨1163325897780026837432816,1163880288638121005883468,true⟩,⟨(-2306900797756144512577763),(-2298551002639297529092972),true⟩,⟨⟨1147102214246209390676866,1175408563686218392370406,true⟩,⟨(-7439026),7439026,true⟩⟩⟩
theorem sharedDiskP527Params_ok : chordParams (Grid.ofRats (317/400) (159/200)) (Grid.ofRats (62765917636291/109951162777600) (62980666001091/109951162777600))=sharedDiskP527Params := by decide +kernel
def sharedDiskP527Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3187837552936128584325259),(-2672053530812157314065753),true⟩,⟨(-353061922156001400683993),60684328909260321902235,true⟩⟩
  | 0,1 => ⟨⟨(-2799521618366524206153799),(-2329405033947196262120457),true⟩,⟨(-422523535266754951408475),(-33033352180529318741077),true⟩⟩
  | 0,2 => ⟨⟨(-2521473558710966323037288),(-2086999861867483019197298),true⟩,⟨(-480299556797986403028876),(-113148678322855318588343),true⟩⟩
  | 0,3 => ⟨⟨(-2366273087380721345920323),(-1952114990648372862602927),true⟩,⟨(-515249566159809597367246),(-161162055127920626153209),true⟩⟩
  | 0,4 => ⟨⟨(-3652454654014053714953400),(-3089111975914824557272210),true⟩,⟨(-289152481459814921029395),141359692248300530884285,true⟩⟩
  | 0,5 => ⟨⟨(-4130171778275927829827527),(-3526176763734862979034731),true⟩,⟨(-247155596853600533585560),188799385159477198167945,true⟩⟩
  | 0,6 => ⟨⟨(-4536974090056778318952376),(-3905054171804590035081099),true⟩,⟨(-231496194980047243458863),197220885472658940585081,true⟩⟩
  | 0,7 => ⟨⟨(-4793566095132740756740757),(-4146673720680670340257527),true⟩,⟨(-236166193947752010386057),186366574411172749529126,true⟩⟩
  | 1,0 => ⟨⟨(-1443431067782630997219693),(-1158265856470779188419565),true⟩,⟨(-745877351946378185767571),(-486313733222461446046600),true⟩⟩
  | 1,1 => ⟨⟨(-1244194778625403068040902),(-987093567932838130537265),true⟩,⟨(-795473647443342573033136),(-558090761392647093166455),true⟩⟩
  | 1,2 => ⟨⟨(-1099889193436146440805517),(-862708429643644659350563),true⟩,⟨(-829646435175644719863148),(-608200413315696388178865),true⟩⟩
  | 1,3 => ⟨⟨(-1017929386084765244663386),(-791847789384855884152602),true⟩,⟨(-848117752297490028030736),(-635608264212646978239673),true⟩⟩
  | 1,4 => ⟨⟨(-1681995533922927219454963),(-1362848053363387152904862),true⟩,⟨(-684730759235275763015434),(-398866459163077824871788),true⟩⟩
  | 1,5 => ⟨⟨(-1931766977999798659980461),(-1577203316755614170022664),true⟩,⟨(-620839383816856706173961),(-308445368484878437156355),true⟩⟩
  | 1,6 => ⟨⟨(-2151308244867498396798837),(-1766202584278889262483427),true⟩,⟨(-566267144934963104513279),(-231956697618274634368127),true⟩⟩
  | 1,7 => ⟨⟨(-2294036926262191386794261),(-1889531510652534708752082),true⟩,⟨(-532079650917462947690063),(-184431240834898280701259),true⟩⟩
  | 2,0 => ⟨⟨(-114943009665431852296864),21947267138976734840482,true⟩,⟨(-978824047945283523967681),(-835499152046225271551127),true⟩⟩
  | 2,1 => ⟨⟨77131838498457531331340,203727675788823089315973,true⟩,⟨(-980895618178704430247563),(-846563518080172880377712),true⟩⟩
  | 2,2 => ⟨⟨217087825901348892163405,338048533747149086028349,true⟩,⟨(-976244649792129499313013),(-847477707384619519340635),true⟩⟩
  | 2,3 => ⟨⟨297242741564319573634655,416532518548757296628698,true⟩,⟨(-971468337285404390346198),(-844849024682953792194362),true⟩⟩
  | 2,4 => ⟨⟨(-345014329287063210382652),(-191799324234354578370678),true⟩,⟨(-962839822021651498342216),(-806936760178496590966404),true⟩⟩
  | 2,5 => ⟨⟨(-588972928083449213013757),(-414720313161461413331080),true⟩,⟨(-930527158534896683422078),(-759117148334247461308219),true⟩⟩
  | 2,6 => ⟨⟨(-811360420935187530540187),(-612366182513376566743201),true⟩,⟨(-890659397795503540577698),(-700103940453064445473121),true⟩⟩
  | 2,7 => ⟨⟨(-960473653465292662700763),(-742062380178451001493721),true⟩,⟨(-860574573549957349107529),(-654261984557183828581241),true⟩⟩
  | 3,0 => ⟨⟨1232114039840935051422230,1361206835396672448599541,true⟩,⟨(-885731899318563348242142),(-760892487538858146724134),true⟩⟩
  | 3,1 => ⟨⟨1453214193340521091290810,1588592829228734269243140,true⟩,⟨(-889604281967101559288292),(-760838843254502900508303),true⟩⟩
  | 3,2 => ⟨⟨1622664461840469004530065,1764208921866818050987531,true⟩,⟨(-911738084469702593266708),(-778357561475189168576825),true⟩⟩
  | 3,3 => ⟨⟨1723707700466807990935873,1869591889795702213603703,true⟩,⟨(-935282511809616601206122),(-798362763663670994187214),true⟩⟩
  | 3,4 => ⟨⟨979672800865680122696461,1103591481453431907232331,true⟩,⟨(-903245867056877108316580),(-780545787576768127941050),true⟩⟩
  | 3,5 => ⟨⟨722885657208438235102468,843449575044032306156567,true⟩,⟨(-931495513948454708865552),(-808872672736472592813086),true⟩⟩
  | 3,6 => ⟨⟨499135909575082224594061,618313502519591585040769,true⟩,⟨(-955545914249043985595723),(-831461231428243652451179),true⟩⟩
  | 3,7 => ⟨⟨352965982138530224590340,472060362233962305482191,true⟩,⟨(-967829775785877459291398),(-842044805086443342309954),true⟩⟩
  | 4,0 => ⟨⟨2479955240002457369353995,2709335473214426178563504,true⟩,⟨(-1546479814246770651320507),(-1327061251330590010917879),true⟩⟩
  | 4,1 => ⟨⟨2679805123111545983207623,2952955378733042369637929,true⟩,⟨(-1965864874664366558937430),(-1699476803261779801500255),true⟩⟩
  | 4,2 => ⟨⟨2800627309150720149993040,3120007975828547419206203,true⟩,⟨(-2444507561242109125449928),(-2126599945585026124951971),true⟩⟩
  | 4,3 => ⟨⟨2836862967364486763049030,3190587474483204347472537,true⟩,⟨(-2816497124815018697445238),(-2459193730101788867785398),true⟩⟩
  | 4,4 => ⟨⟨2250693768968584434742308,2445813973390085817960270,true⟩,⟨(-1253835781238222179965245),(-1069682747432918517303139),true⟩⟩
  | 4,5 => ⟨⟨2038093291400931464512464,2209387420213179735192679,true⟩,⟨(-1079503542211795562501821),(-918866294382941050255356),true⟩⟩
  | 4,6 => ⟨⟨1872021723669882063794061,2028420599158456137511845,true⟩,⟨(-989023081137640443033502),(-842528022841004471535620),true⟩⟩
  | 4,7 => ⟨⟨1772344214188391708267856,1921087574673412284449040,true⟩,⟨(-950195937462226655093270),(-810754979072007298302204),true⟩⟩
  | 5,0 => ⟨⟨2726169896236448137190295,3169235155701289010525120,true⟩,⟨(-3826719283397275641352310),(-3362815036686671996661286),true⟩⟩
  | 5,1 => ⟨⟨2631720120355551944402164,3102025162554662813995615,true⟩,⟨(-4142875997418585088346844),(-3645318014356280237462561),true⟩⟩
  | 5,2 => ⟨⟨2528795674823660386545450,3021961899351441321807577,true⟩,⟨(-4410033146139711104993353),(-3883812034942671698687461),true⟩⟩
  | 5,3 => ⟨⟨2452747548916725577276669,2960220765858088143073257,true⟩,⟨(-4577847485641051449176422),(-4033490289619997102235125),true⟩⟩
  | 5,4 => ⟨⟨2791405114807931927796835,3207310923598948933184133,true⟩,⟨(-3514601225525753144985786),(-3083717229692288874439813),true⟩⟩
  | 5,5 => ⟨⟨2825304685734084038144434,3217786006144634572217201,true⟩,⟨(-3248550677318847137150215),(-2845717886534287395892607),true⟩⟩
  | 5,6 => ⟨⟨2837295956852854632240860,3212474632523019478490096,true⟩,⟨(-3054276101200442805737975),(-2671906822057947235716840),true⟩⟩
  | 5,7 => ⟨⟨2839201618792053292527177,3204458750723880966024994,true⟩,⟨(-2943856622035223906450176),(-2573121829049938114269170),true⟩⟩
  | 6,0 => ⟨⟨1437655313453911829799529,2059642582182493451309104,true⟩,⟨(-5921280594719836937997249),(-5225705949490347267397481),true⟩⟩
  | 6,1 => ⟨⟨966923343588248325704827,1627154994346642045258412,true⟩,⟨(-6285893824124086109111117),(-5542461036741092968600062),true⟩⟩
  | 6,2 => ⟨⟨521641686974010733679644,1220296983199490462626348,true⟩,⟨(-6549880192452941276754627),(-5764408516760853949177378),true⟩⟩
  | 6,3 => ⟨⟨222610580245899901338010,948407166055595786242363,true⟩,⟨(-6691407796053375152605472),(-5878974319112536755684269),true⟩⟩
  | 6,4 => ⟨⟨1838596761619870337559272,2425645920708506878315351,true⟩,⟨(-5513766710353703966951301),(-4865570034507149874506055),true⟩⟩
  | 6,5 => ⟨⟨2132556082469663934422544,2687099566438337725385170,true⟩,⟨(-5131676935127143939182831),(-4526531638269374396235690),true⟩⟩
  | 6,6 => ⟨⟨2317856781833623920093560,2847221607274024763716570,true⟩,⟨(-4835240032080575003723816),(-4262829490664636963023685),true⟩⟩
  | 6,7 => ⟨⟨2411678529941294200861302,2926225218194642312443760,true⟩,⟨(-4660948609313999150860348),(-4107567471148582174809274),true⟩⟩
  | 7,0 => ⟨⟨(-2639090690911494006054341),(-1703197330415592736087570),true⟩,⟨(-6921152491537970813925136),(-5958446271487425578240081),true⟩⟩
  | 7,1 => ⟨⟨(-3524811338685927914371675),(-2544795174033047047013859),true⟩,⟨(-6585912331017580206697159),(-5616737057644804893192351),true⟩⟩
  | 7,2 => ⟨⟨(-4187944990059341967729954),(-3184479273261216441014058),true⟩,⟨(-6163854555608970431729175),(-5207508789723684179665176),true⟩⟩
  | 7,3 => ⟨⟨(-4555297495017570105289941),(-3543972937974664923596509),true⟩,⟨(-5842291117487583719292429),(-4902335782755785869387585),true⟩⟩
  | 7,4 => ⟨⟨(-1693387555481913023281800),(-816744506282372391612064),true⟩,⟨(-7055364145910098853683414),(-6121991130592610456265904),true⟩⟩
  | 7,5 => ⟨⟨(-864459043379671204986037),(-48904658384793993974217),true⟩,⟨(-7004104712560415182238924),(-6112903952143126056023265),true⟩⟩
  | 7,6 => ⟨⟨(-264300827853950515394318),503336905532168139556083,true⟩,⟨(-6868118889783606708037102),(-6016909737591104994505998),true⟩⟩
  | 7,7 => ⟨⟨69248774068559509633364,808355097173285015039629,true⟩,⟨(-6754001926331541837660126),(-5928685543443919370190281),true⟩⟩
  | 8,0 => ⟨⟨(-5775662459094124817070893),(-4902195791772914570403062),true⟩,⟨(-2344653632958921819697664),(-1727993375234086420802611),true⟩⟩
  | 8,1 => ⟨⟨(-5526295734607167745095968),(-4749885052890782748257993),true⟩,⟨(-1319802563389718336045557),(-829174305895250400203812),true⟩⟩
  | 8,2 => ⟨⟨(-5172058000362456855383864),(-4484985387500437637083982),true⟩,⟨(-602397599547005385691927),(-211386674523390226608320),true⟩⟩
  | 8,3 => ⟨⟨(-4907034151387465324217250),(-4277127931565155108163127),true⟩,⟨(-224279853077143233609346),115952873188927319489046,true⟩⟩
  | 8,4 => ⟨⟨(-5753357524921644991880570),(-4800069368941866083169810),true⟩,⟨(-3503868614354647048403194),(-2758789512443077386128349),true⟩⟩
  | 8,5 => ⟨⟨(-5450267485444941705666033),(-4452210438518204180639720),true⟩,⟨(-4542107778549035491574512),(-3698225557776311662155253),true⟩⟩
  | 8,6 => ⟨⟨(-5034988512365394291064216),(-4022264999870272605857984),true⟩,⟨(-5277683429931584542371788),(-4374732082584544990673996),true⟩⟩
  | 8,7 => ⟨⟨(-4721664703116844102980511),(-3708465889049308631287466),true⟩,⟨(-5668793184706877860399447),(-4739251299868520728420356),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP527Value0_0 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP527Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value0_1 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP527Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value0_2 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP527Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value0_3 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP527Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value0_4 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP527Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value0_5 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP527Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value0_6 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP527Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value0_7 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP527Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP527Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 0 j)=sharedDiskP527Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP527Value0_0
  · exact sharedDiskP527Value0_1
  · exact sharedDiskP527Value0_2
  · exact sharedDiskP527Value0_3
  · exact sharedDiskP527Value0_4
  · exact sharedDiskP527Value0_5
  · exact sharedDiskP527Value0_6
  · exact sharedDiskP527Value0_7
private theorem sharedDiskP527Value1_0 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP527Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value1_1 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP527Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value1_2 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP527Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value1_3 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP527Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value1_4 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP527Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value1_5 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP527Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value1_6 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP527Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value1_7 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP527Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP527Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 1 j)=sharedDiskP527Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP527Value1_0
  · exact sharedDiskP527Value1_1
  · exact sharedDiskP527Value1_2
  · exact sharedDiskP527Value1_3
  · exact sharedDiskP527Value1_4
  · exact sharedDiskP527Value1_5
  · exact sharedDiskP527Value1_6
  · exact sharedDiskP527Value1_7
private theorem sharedDiskP527Value2_0 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP527Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value2_1 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP527Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value2_2 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP527Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value2_3 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP527Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value2_4 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP527Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value2_5 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP527Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value2_6 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP527Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value2_7 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP527Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP527Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 2 j)=sharedDiskP527Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP527Value2_0
  · exact sharedDiskP527Value2_1
  · exact sharedDiskP527Value2_2
  · exact sharedDiskP527Value2_3
  · exact sharedDiskP527Value2_4
  · exact sharedDiskP527Value2_5
  · exact sharedDiskP527Value2_6
  · exact sharedDiskP527Value2_7
private theorem sharedDiskP527Value3_0 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP527Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value3_1 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP527Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value3_2 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP527Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value3_3 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP527Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value3_4 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP527Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value3_5 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP527Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value3_6 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP527Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value3_7 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP527Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP527Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 3 j)=sharedDiskP527Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP527Value3_0
  · exact sharedDiskP527Value3_1
  · exact sharedDiskP527Value3_2
  · exact sharedDiskP527Value3_3
  · exact sharedDiskP527Value3_4
  · exact sharedDiskP527Value3_5
  · exact sharedDiskP527Value3_6
  · exact sharedDiskP527Value3_7
private theorem sharedDiskP527Value4_0 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP527Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value4_1 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP527Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value4_2 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP527Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value4_3 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP527Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value4_4 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP527Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value4_5 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP527Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value4_6 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP527Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value4_7 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP527Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP527Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 4 j)=sharedDiskP527Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP527Value4_0
  · exact sharedDiskP527Value4_1
  · exact sharedDiskP527Value4_2
  · exact sharedDiskP527Value4_3
  · exact sharedDiskP527Value4_4
  · exact sharedDiskP527Value4_5
  · exact sharedDiskP527Value4_6
  · exact sharedDiskP527Value4_7
private theorem sharedDiskP527Value5_0 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP527Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value5_1 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP527Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value5_2 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP527Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value5_3 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP527Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value5_4 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP527Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value5_5 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP527Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value5_6 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP527Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value5_7 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP527Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP527Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 5 j)=sharedDiskP527Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP527Value5_0
  · exact sharedDiskP527Value5_1
  · exact sharedDiskP527Value5_2
  · exact sharedDiskP527Value5_3
  · exact sharedDiskP527Value5_4
  · exact sharedDiskP527Value5_5
  · exact sharedDiskP527Value5_6
  · exact sharedDiskP527Value5_7
private theorem sharedDiskP527Value6_0 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP527Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value6_1 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP527Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value6_2 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP527Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value6_3 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP527Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value6_4 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP527Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value6_5 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP527Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value6_6 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP527Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value6_7 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP527Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP527Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 6 j)=sharedDiskP527Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP527Value6_0
  · exact sharedDiskP527Value6_1
  · exact sharedDiskP527Value6_2
  · exact sharedDiskP527Value6_3
  · exact sharedDiskP527Value6_4
  · exact sharedDiskP527Value6_5
  · exact sharedDiskP527Value6_6
  · exact sharedDiskP527Value6_7
private theorem sharedDiskP527Value7_0 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP527Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value7_1 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP527Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value7_2 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP527Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value7_3 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP527Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value7_4 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP527Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value7_5 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP527Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value7_6 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP527Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value7_7 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP527Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP527Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 7 j)=sharedDiskP527Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP527Value7_0
  · exact sharedDiskP527Value7_1
  · exact sharedDiskP527Value7_2
  · exact sharedDiskP527Value7_3
  · exact sharedDiskP527Value7_4
  · exact sharedDiskP527Value7_5
  · exact sharedDiskP527Value7_6
  · exact sharedDiskP527Value7_7
private theorem sharedDiskP527Value8_0 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP527Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value8_1 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP527Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value8_2 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP527Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value8_3 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP527Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value8_4 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP527Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value8_5 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP527Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value8_6 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP527Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP527Value8_7 : truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP527Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP527Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points 8 j)=sharedDiskP527Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP527Value8_0
  · exact sharedDiskP527Value8_1
  · exact sharedDiskP527Value8_2
  · exact sharedDiskP527Value8_3
  · exact sharedDiskP527Value8_4
  · exact sharedDiskP527Value8_5
  · exact sharedDiskP527Value8_6
  · exact sharedDiskP527Value8_7
theorem sharedDiskP527Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP527Params (sharedChord521Gauss8Points i j)=sharedDiskP527Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP527Values0_eq
  · exact sharedDiskP527Values1_eq
  · exact sharedDiskP527Values2_eq
  · exact sharedDiskP527Values3_eq
  · exact sharedDiskP527Values4_eq
  · exact sharedDiskP527Values5_eq
  · exact sharedDiskP527Values6_eq
  · exact sharedDiskP527Values7_eq
  · exact sharedDiskP527Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP527Box : HorizontalRectangle := ⟨(317/400),(159/200),(62765917636291/109951162777600),(62980666001091/109951162777600),(119548409175350552630902707195791/324518553658426726783156020576256),(380981494608233339574891774218127/324518553658426726783156020576256),(-4473261517279376490248474998011733/1298074214633706907132624082305024),(-3401416871085903755067568608442197/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP527Grid : CGrid := momentChordGrid sharedDiskP527Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP527Columns : containedInReported sharedDiskP527Grid.re sharedDiskP527Box.reLo sharedDiskP527Box.reHi=true ∧ containedInReported sharedDiskP527Grid.im sharedDiskP527Box.imLo sharedDiskP527Box.imHi=true := by
  rw [sharedDiskP527Grid,momentChordGrid_eq_tabulated sharedDiskP527Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP527Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP527Values_eq]
  decide +kernel
theorem sharedDiskP527Sound : sharedDiskP527Box.Sound := by
  intro t a tl tu al au
  change (((317/400):ℚ):ℝ)≤t at tl
  change t≤(((159/200):ℚ):ℝ) at tu
  change (((62765917636291/109951162777600):ℚ):ℝ)≤a at al
  change a≤(((62980666001091/109951162777600):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP527Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(317/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((159/200):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(62765917636291/109951162777600))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((62980666001091/109951162777600):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP527Columns.1 sharedDiskP527Columns.2
def sharedDiskP527Rows : List SignRow := [positive_527.toSignRow]
theorem sharedDiskP527Rows_actual : ∀ r∈sharedDiskP527Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP527Rows.all (sharedDiskP527Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP527Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP528Params : ChordParams := ⟨⟨(-23527886069253708668833),(-23238226565097918580125),true⟩,⟨2031086469294632277498911,2046804195204453100756184,true⟩,⟨125355941795089589546505,127224807096838003462741,true⟩,⟨222385140079613706845398,225295335135905364470057,true⟩,⟨328821609807488175506569,330942388808906465798028,true⟩,⟨1162768355331962255729080,1163325897780026837433780,true⟩,⟨(-2298551002639297529102201),(-2290247349804124710057570),true⟩,⟨⟨1146461518267553004657359,1174808414946611311826218,true⟩,⟨(-8492900),8492900,true⟩⟩⟩
theorem sharedDiskP528Params_ok : chordParams (Grid.ofRats (159/200) (319/400)) (Grid.ofRats (188529793740749/329853488332800) (189174038835149/329853488332800))=sharedDiskP528Params := by decide +kernel
def sharedDiskP528Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3186138165922113092537753),(-2670811883081908581939517),true⟩,⟨(-349983144062277510231428),63234434426363031822203,true⟩⟩
  | 0,1 => ⟨⟨(-2800831767783254591848653),(-2330764013602676543873382),true⟩,⟨(-418394918080515582270299),(-29095567126296829699821),true⟩⟩
  | 0,2 => ⟨⟨(-2524628536137397631149916),(-2089991526650104788835560),true⟩,⟨(-475450166317752961033909),(-108356924897344028890891),true⟩⟩
  | 0,3 => ⟨⟨(-2370402305296087075786158),(-1955941306959290536421730),true⟩,⟨(-510025448029019976742691),(-155867032205918068720824),true⟩⟩
  | 0,4 => ⟨⟨(-3646670835901689155719885),(-3084264071824260955796390),true⟩,⟨(-287272362379517019187355),142388622346117420359146,true⟩⟩
  | 0,5 => ⟨⟨(-4119701256232952303701302),(-3517088902898689371663129),true⟩,⟨(-246305029559218369836849),188648229841297284386151,true⟩⟩
  | 0,6 => ⟨⟨(-4522180994171817336440880),(-3891975523201124158888748),true⟩,⟨(-231269512615163224899525),196438384671964535959823,true⟩⟩
  | 0,7 => ⟨⟨(-4775926936858200052878281),(-4130924197066217788893271),true⟩,⟨(-236209277815924426795723),185428899744072955615237,true⟩⟩
  | 1,0 => ⟨⟨(-1452154253874030354307522),(-1166087347712273779316601),true⟩,⟨(-739385667133709284858380),(-479181352823629395102807),true⟩⟩
  | 1,1 => ⟨⟨(-1253695115145893013326940),(-995632481673404979468020),true⟩,⟨(-789049415939074720372983),(-550972574936795211108718),true⟩⟩
  | 1,2 => ⟨⟨(-1109923564856880137278429),(-871754448423830762219473),true⟩,⟨(-823374035228285714230746),(-601211915955311751141631),true⟩⟩
  | 1,3 => ⟨⟨(-1028259227608852981669019),(-801179650512906181620874),true⟩,⟨(-841972887690973724632433),(-628740235216918023189653),true⟩⟩
  | 1,4 => ⟨⟨(-1689706269983480885098361),(-1369763992007823910533396),true⟩,⟨(-678349916851451320203544),(-391945133540679281815139),true⟩⟩
  | 1,5 => ⟨⟨(-1938297591721442729657045),(-1583090181792842210805749),true⟩,⟨(-614760390997427233537960),(-301970835111221813612154),true⟩⟩
  | 1,6 => ⟨⟨(-2156684072333731319746698),(-1771096205073659369542897),true⟩,⟨(-560577306854014921705424),(-226026473542681384995038),true⟩⟩
  | 1,7 => ⟨⟨(-2298598223282072617380056),(-1893727633733691669473347),true⟩,⟨(-526691219118097617087802),(-178913513472585574603780),true⟩⟩
  | 2,0 => ⟨⟨(-128243330283404067660056),9093973269745168870555,true⟩,⟨(-975956913855670470071107),(-832385340245332319848167),true⟩⟩
  | 2,1 => ⟨⟨63218125744228160078602,190156628131823830237976,true⟩,⟨(-979185170567786127672299),(-844615260879037781046300),true⟩⟩
  | 2,2 => ⟨⟨202709385925924327101780,323754581075944685570423,true⟩,⟨(-975429321540111254584193),(-846573747872884808751192),true⟩⟩
  | 2,3 => ⟨⟨282609832033676089144098,401966005231157995654132,true⟩,⟨(-971178046674277410186570),(-844469866765189038090100),true⟩⟩
  | 2,4 => ⟨⟨(-357511583764101846844759),(-203732173042789151193011),true⟩,⟨(-958743162237439551960761),(-802570521682869192079537),true⟩⟩
  | 2,5 => ⟨⟨(-600629846721365440404946),(-425731899915463747344522),true⟩,⟨(-925367087594274508495166),(-753654050387720524009285),true⟩⟩
  | 2,6 => ⟨⟨(-822419344517190622862090),(-622418627126897227927712),true⟩,⟨(-884975128039646792975874),(-693693189896324941572754),true⟩⟩
  | 2,7 => ⟨⟨(-971008096578328802766778),(-751594345745372575801142),true⟩,⟨(-854537588993108214893489),(-647498998400008549728683),true⟩⟩
  | 3,0 => ⟨⟨1216145947783887578558926,1345081584491794001489373,true⟩,⟨(-891403672105213725546536),(-766489330072416078560982),true⟩⟩
  | 3,1 => ⟨⟨1437390450354251499117518,1572678138759835590603376,true⟩,⟨(-896653184527798314294420),(-767733254420256337163002),true⟩⟩
  | 3,2 => ⟨⟨1607049460415053647075698,1748570898201489816886125,true⟩,⟨(-919870023215533883772329),(-786260623509605083241548),true⟩⟩
  | 3,3 => ⟨⟨1708235528239374190749246,1854144067824036846336769,true⟩,⟨(-944087971739279176326140),(-806889196927028277841633),true⟩⟩
  | 3,4 => ⟨⟨963786029053587615010570,1087503401075666546803101,true⟩,⟨(-907328633303414002233593),(-784621698809948685985576),true⟩⟩
  | 3,5 => ⟨⟨707365290368983113268232,827716805787848632425793,true⟩,⟨(-933905553115331759751493),(-811321697197035384536227),true⟩⟩
  | 3,6 => ⟨⟨484137270846384641503608,603119477774148333272776,true⟩,⟨(-956457800414656819833244),(-832433536582749947088746),true⟩⟩
  | 3,7 => ⟨⟨338386968829118946501826,457309792468129470917641,true⟩,⟨(-967757866023191844059747),(-842038150311733590554425),true⟩⟩
  | 4,0 => ⟨⟨2463888846718433110330190,2693655802348188699087271,true⟩,⟨(-1562122464417149421613024),(-1341934499866317981332839),true⟩⟩
  | 4,1 => ⟨⟨2661569814595240896419282,2935245347221174538992054,true⟩,⟨(-1984310505241562064558960),(-1716946304034334470423663),true⟩⟩
  | 4,2 => ⟨⟨2779056107072767085885156,3099052941190934082019671,true⟩,⟨(-2465212050358504667264746),(-2146167104979008484428474),true⟩⟩
  | 4,3 => ⟨⟨2812261705232204137432677,3166627033956807563456033,true⟩,⟨(-2838306912061509544188989),(-2479793528516554913850096),true⟩⟩
  | 4,4 => ⟨⟨2235492431224543089430214,2430862709033903283755920,true⟩,⟨(-1266933280693731608270252),(-1082199824907545110939106),true⟩⟩
  | 4,5 => ⟨⟨2022990953028464573822030,2194430393041011603683133,true⟩,⟨(-1090666100487811763912628),(-929589237490929463579103),true⟩⟩
  | 4,6 => ⟨⟨1856761856934119564173726,2013239001951226190536814,true⟩,⟨(-998881568881603353156798),(-852037251434377606768596),true⟩⟩
  | 4,7 => ⟨⟨1756943201740758749752070,1905730723686737081941930,true⟩,⟨(-959336987118527634643638),(-819593610582613864743041),true⟩⟩
  | 5,0 => ⟨⟨2692162134161676709590088,3135730959137184532080386,true⟩,⟨(-3848568028072780638577811),(-3383503283302028058546942),true⟩⟩
  | 5,1 => ⟨⟨2594574280107048253829581,3065274682156094728675898,true⟩,⟨(-4163776361391659849524153),(-3665156097346615762936877),true⟩⟩
  | 5,2 => ⟨⟨2488978201458958235118388,2982421629408017776101789,true⟩,⟨(-4429736286324587068475481),(-3902571181649950654938671),true⟩⟩
  | 5,3 => ⟨⟨2411254917513023475896641,2918917775696317125423049,true⟩,⟨(-4596600849720358404891416),(-4051391912003836872540424),true⟩⟩
  | 5,4 => ⟨⟨2760433211484674544222915,3176917833849238900169823,true⟩,⟨(-3536919562173758987066304),(-3104818865728086257945252),true⟩⟩
  | 5,5 => ⟨⟨2796843386792814924785312,3189944089673538829166932,true⟩,⟨(-3270922423766561770852160),(-2866854735596196605087242),true⟩⟩
  | 5,6 => ⟨⟨2810608413009655322635128,3186422826990026771075487,true⟩,⟨(-3076492727159330779378803),(-2692891630548869090631100),true⟩⟩
  | 5,7 => ⟨⟨2813495517882267326527886,3179392779749445254570584,true⟩,⟨(-2965913723927228204622930),(-2593954816131911983834490),true⟩⟩
  | 6,0 => ⟨⟨1383973385710920029504551,2004977487789813290261102,true⟩,⟨(-5925473127767820824802888),(-5230448934727430359521140),true⟩⟩
  | 6,1 => ⟨⟨909773066222195324267476,1569724407304862524626069,true⟩,⟨(-6283819258700906755125780),(-5540893221700762215695275),true⟩⟩
  | 6,2 => ⟨⟨463579643088051023248524,1162765736330181750219907,true⟩,⟨(-6541301167721489164981535),(-5756241668203691761676633),true⟩⟩
  | 6,3 => ⟨⟨164518927737073515305828,890548405682449850715096,true⟩,⟨(-6678519145912188857371630),(-5866934496958959004035797),true⟩⟩
  | 6,4 => ⟨⟨1788205022710239496225957,2374732934849058521923829,true⟩,⟨(-5523934179185152468967124),(-4875709848176733035822444),true⟩⟩
  | 6,5 => ⟨⟨2085655204101507258781307,2640017986175323407224035,true⟩,⟨(-5146091603804454506383309),(-4540511114341943559236557),true⟩⟩
  | 6,6 => ⟨⟨2273818296478152191057823,2803216992628057855070318,true⟩,⟨(-4852218673363645272759488),(-4279127247006293304552876),true⟩⟩
  | 6,7 => ⟨⟨2369359868752190450691013,2884048827370337094382478,true⟩,⟨(-4679172232260896057199760),(-4124990497062435023682605),true⟩⟩
  | 7,0 => ⟨⟨(-2678900306651202011395587),(-1745929035535558220026010),true⟩,⟨(-6873358441608071059191439),(-5915822769025615277762865),true⟩⟩
  | 7,1 => ⟨⟨(-3552754243172041146922347),(-2576947484262920405501563),true⟩,⟨(-6531377695543787457229222),(-5568573581525451506919367),true⟩⟩
  | 7,2 => ⟨⟨(-4205013303193237296522708),(-3206741212089175703729924),true⟩,⟨(-6106548237952776583605723),(-5157325704889465987300424),true⟩⟩
  | 7,3 => ⟨⟨(-4565499720218282863700133),(-3559909026519576059672983),true⟩,⟨(-5784668013972985531906096),(-4852159924291968570894367),true⟩⟩
  | 7,4 => ⟨⟨(-1742732199278906029537467),(-867710309012588983595222),true⟩,⟨(-7017395345567436679826260),(-6087786107202087851239904),true⟩⟩
  | 7,5 => ⟨⟨(-919473667896091270188530),(-104486086215345306734501),true⟩,⟨(-6976325218890186779881646),(-6087617065731670726130741),true⟩⟩
  | 7,6 => ⟨⟨(-321752739504833998815381),445808764815860504609105,true⟩,⟨(-6848386831322444418232516),(-5998754764104746402592923),true⟩⟩
  | 7,7 => ⟨⟨11308613999620130843838,750489255921910668141651,true⟩,⟨(-6738929437271060665958307),(-5914689555893151313263094),true⟩⟩
  | 8,0 => ⟨⟨(-5749699274559959313939330),(-4882751825134922082432057),true⟩,⟨(-2316432093660120581151922),(-1705318185567887506916547),true⟩⟩
  | 8,1 => ⟨⟨(-5500361668865084054157626),(-4729400569767771833639636),true⟩,⟨(-1304372795967936371774335),(-817684336323159974573333),true⟩⟩
  | 8,2 => ⟨⟨(-5149257360000057000290874),(-4466531752810169957535923),true⟩,⟨(-595815330783677466323301),(-207482511356085153030746),true⟩⟩
  | 8,3 => ⟨⟨(-4887113245948437713460180),(-4260817412802645128087346),true⟩,⟨(-222097645515377409742059),116202963264115573809041,true⟩⟩
  | 8,4 => ⟨⟨(-5733036954729179497373216),(-4786800708782211164825218),true⟩,⟨(-3462276106577820811254473),(-2724110715649603514829002),true⟩⟩
  | 8,5 => ⟨⟨(-5440043030407856760576949),(-4448897197625114010276677),true⟩,⟨(-4490779326242670949702772),(-3654507320971115620525196),true⟩⟩
  | 8,6 => ⟨⟨(-5035086536867222653497612),(-4028772460794848240780424),true⟩,⟨(-5221655355366730529817276),(-4326403664875609064404178),true⟩⟩
  | 8,7 => ⟨⟨(-4728526197342964968418044),(-3721301200411680573904124),true⟩,⟨(-5611415252662729343637710),(-4689435187309745122519718),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP528Value0_0 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP528Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value0_1 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP528Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value0_2 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP528Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value0_3 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP528Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value0_4 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP528Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value0_5 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP528Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value0_6 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP528Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value0_7 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP528Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP528Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 0 j)=sharedDiskP528Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP528Value0_0
  · exact sharedDiskP528Value0_1
  · exact sharedDiskP528Value0_2
  · exact sharedDiskP528Value0_3
  · exact sharedDiskP528Value0_4
  · exact sharedDiskP528Value0_5
  · exact sharedDiskP528Value0_6
  · exact sharedDiskP528Value0_7
private theorem sharedDiskP528Value1_0 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP528Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value1_1 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP528Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value1_2 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP528Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value1_3 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP528Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value1_4 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP528Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value1_5 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP528Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value1_6 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP528Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value1_7 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP528Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP528Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 1 j)=sharedDiskP528Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP528Value1_0
  · exact sharedDiskP528Value1_1
  · exact sharedDiskP528Value1_2
  · exact sharedDiskP528Value1_3
  · exact sharedDiskP528Value1_4
  · exact sharedDiskP528Value1_5
  · exact sharedDiskP528Value1_6
  · exact sharedDiskP528Value1_7
private theorem sharedDiskP528Value2_0 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP528Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value2_1 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP528Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value2_2 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP528Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value2_3 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP528Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value2_4 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP528Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value2_5 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP528Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value2_6 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP528Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value2_7 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP528Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP528Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 2 j)=sharedDiskP528Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP528Value2_0
  · exact sharedDiskP528Value2_1
  · exact sharedDiskP528Value2_2
  · exact sharedDiskP528Value2_3
  · exact sharedDiskP528Value2_4
  · exact sharedDiskP528Value2_5
  · exact sharedDiskP528Value2_6
  · exact sharedDiskP528Value2_7
private theorem sharedDiskP528Value3_0 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP528Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value3_1 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP528Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value3_2 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP528Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value3_3 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP528Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value3_4 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP528Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value3_5 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP528Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value3_6 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP528Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value3_7 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP528Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP528Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 3 j)=sharedDiskP528Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP528Value3_0
  · exact sharedDiskP528Value3_1
  · exact sharedDiskP528Value3_2
  · exact sharedDiskP528Value3_3
  · exact sharedDiskP528Value3_4
  · exact sharedDiskP528Value3_5
  · exact sharedDiskP528Value3_6
  · exact sharedDiskP528Value3_7
private theorem sharedDiskP528Value4_0 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP528Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value4_1 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP528Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value4_2 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP528Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value4_3 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP528Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value4_4 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP528Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value4_5 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP528Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value4_6 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP528Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value4_7 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP528Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP528Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 4 j)=sharedDiskP528Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP528Value4_0
  · exact sharedDiskP528Value4_1
  · exact sharedDiskP528Value4_2
  · exact sharedDiskP528Value4_3
  · exact sharedDiskP528Value4_4
  · exact sharedDiskP528Value4_5
  · exact sharedDiskP528Value4_6
  · exact sharedDiskP528Value4_7
private theorem sharedDiskP528Value5_0 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP528Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value5_1 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP528Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value5_2 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP528Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value5_3 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP528Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value5_4 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP528Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value5_5 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP528Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value5_6 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP528Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value5_7 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP528Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP528Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 5 j)=sharedDiskP528Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP528Value5_0
  · exact sharedDiskP528Value5_1
  · exact sharedDiskP528Value5_2
  · exact sharedDiskP528Value5_3
  · exact sharedDiskP528Value5_4
  · exact sharedDiskP528Value5_5
  · exact sharedDiskP528Value5_6
  · exact sharedDiskP528Value5_7
private theorem sharedDiskP528Value6_0 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP528Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value6_1 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP528Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value6_2 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP528Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value6_3 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP528Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value6_4 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP528Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value6_5 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP528Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value6_6 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP528Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value6_7 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP528Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP528Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 6 j)=sharedDiskP528Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP528Value6_0
  · exact sharedDiskP528Value6_1
  · exact sharedDiskP528Value6_2
  · exact sharedDiskP528Value6_3
  · exact sharedDiskP528Value6_4
  · exact sharedDiskP528Value6_5
  · exact sharedDiskP528Value6_6
  · exact sharedDiskP528Value6_7
private theorem sharedDiskP528Value7_0 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP528Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value7_1 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP528Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value7_2 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP528Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value7_3 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP528Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value7_4 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP528Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value7_5 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP528Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value7_6 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP528Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value7_7 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP528Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP528Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 7 j)=sharedDiskP528Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP528Value7_0
  · exact sharedDiskP528Value7_1
  · exact sharedDiskP528Value7_2
  · exact sharedDiskP528Value7_3
  · exact sharedDiskP528Value7_4
  · exact sharedDiskP528Value7_5
  · exact sharedDiskP528Value7_6
  · exact sharedDiskP528Value7_7
private theorem sharedDiskP528Value8_0 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP528Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value8_1 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP528Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value8_2 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP528Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value8_3 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP528Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value8_4 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP528Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value8_5 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP528Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value8_6 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP528Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP528Value8_7 : truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP528Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP528Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points 8 j)=sharedDiskP528Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP528Value8_0
  · exact sharedDiskP528Value8_1
  · exact sharedDiskP528Value8_2
  · exact sharedDiskP528Value8_3
  · exact sharedDiskP528Value8_4
  · exact sharedDiskP528Value8_5
  · exact sharedDiskP528Value8_6
  · exact sharedDiskP528Value8_7
theorem sharedDiskP528Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP528Params (sharedChord521Gauss8Points i j)=sharedDiskP528Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP528Values0_eq
  · exact sharedDiskP528Values1_eq
  · exact sharedDiskP528Values2_eq
  · exact sharedDiskP528Values3_eq
  · exact sharedDiskP528Values4_eq
  · exact sharedDiskP528Values5_eq
  · exact sharedDiskP528Values6_eq
  · exact sharedDiskP528Values7_eq
  · exact sharedDiskP528Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP528Box : HorizontalRectangle := ⟨(159/200),(319/400),(188529793740749/329853488332800),(189174038835149/329853488332800),(1785653781597593214790753450689633/5192296858534827628530496329220096),(2966079728177235796349736519057969/2596148429267413814265248164610048),(-1117813335641648011498446239426699/324518553658426726783156020576256),(-852106291237352119906468138969227/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP528Grid : CGrid := momentChordGrid sharedDiskP528Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP528Columns : containedInReported sharedDiskP528Grid.re sharedDiskP528Box.reLo sharedDiskP528Box.reHi=true ∧ containedInReported sharedDiskP528Grid.im sharedDiskP528Box.imLo sharedDiskP528Box.imHi=true := by
  rw [sharedDiskP528Grid,momentChordGrid_eq_tabulated sharedDiskP528Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP528Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP528Values_eq]
  decide +kernel
theorem sharedDiskP528Sound : sharedDiskP528Box.Sound := by
  intro t a tl tu al au
  change (((159/200):ℚ):ℝ)≤t at tl
  change t≤(((319/400):ℚ):ℝ) at tu
  change (((188529793740749/329853488332800):ℚ):ℝ)≤a at al
  change a≤(((189174038835149/329853488332800):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP528Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(159/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((319/400):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(188529793740749/329853488332800))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((189174038835149/329853488332800):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP528Columns.1 sharedDiskP528Columns.2
def sharedDiskP528Rows : List SignRow := [positive_528.toSignRow]
theorem sharedDiskP528Rows_actual : ∀ r∈sharedDiskP528Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP528Rows.all (sharedDiskP528Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP528Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP529Params : ChordParams := ⟨⟨(-23819311874109026651201),(-23527886069253708668332),true⟩,⟨2021382713786015282049600,2037020748531514983618124,true⟩,⟨125898557303860764714939,127767878737040900414243,true⟩,⟨224192133123482099966328,227111003583035447677169,true⟩,⟨330786390820876565791506,332907412908823336637315,true⟩,⟨1162207677486924022063844,1162768355331962255730046,true⟩,⟨(-2290247349804124710066771),(-2281989438461610150720666),true⟩,⟨⟨1145816669092141084800147,1174203425571440441475844,true⟩,⟨(-9688148),9688148,true⟩⟩⟩
theorem sharedDiskP529Params_ok : chordParams (Grid.ofRats (319/400) (4/5)) (Grid.ofRats (943815059771497/1649267441664000) (947036285243497/1649267441664000))=sharedDiskP529Params := by decide +kernel
def sharedDiskP529Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3184379436343932621685432),(-2669481739862624396302611),true⟩,⟨(-346970200998727767427442),65750608271678253175685,true⟩⟩
  | 0,1 => ⟨⟨(-2802061652226600752600360),(-2332020430271721965831985),true⟩,⟨(-414340099150455421406331),(-25207327384267843052114),true⟩⟩
  | 0,2 => ⟨⟨(-2527748720878985144880446),(-2092874877242231519544217),true⟩,⟨(-470677307305730062701480),(-103517456357372036950051),true⟩⟩
  | 0,3 => ⟨⟨(-2374438093963722419608644),(-1959657340501904996833223),true⟩,⟨(-504877994153602915219232),(-150629539558449927436995),true⟩⟩
  | 0,4 => ⟨⟨(-3640863606259349514554389),(-3079355441692735666729692),true⟩,⟨(-285444991260218957769980),143405208895467794065961,true⟩⟩
  | 0,5 => ⟨⟨(-4109256419118054388618500),(-3507982013652598292363396),true⟩,⟨(-245493549267412339940102),188503690115128958199188,true⟩⟩
  | 0,6 => ⟨⟨(-4507468421230476121221054),(-3878923201259256776198977),true⟩,⟨(-231073067731052201692719),195673015871490418139561,true⟩⟩
  | 0,7 => ⟨⟨(-4758399015828699462152418),(-4115233607359394105650823),true⟩,⟨(-236279971106655543430447),184510374940196324528090,true⟩⟩
  | 1,0 => ⟨⟨(-1460771699058876335424168),(-1173795000564444106068748),true⟩,⟨(-732945284142245704921930),(-472089420100543307967260),true⟩⟩
  | 1,1 => ⟨⟨(-1263087638358005863708248),(-1004056412684946226254592),true⟩,⟨(-782664746716281862248075),(-543883783891143747178727),true⟩⟩
  | 1,2 => ⟨⟨(-1119848304667868418487824),(-880684217386495913583045),true⟩,⟨(-817131450518208444446178),(-594243495917534564203434),true⟩⟩
  | 1,3 => ⟨⟨(-1038478252827994450268400),(-810394365426342493302203),true⟩,⟨(-835851892871944656861046),(-621886584915145435885787),true⟩⟩
  | 1,4 => ⟨⟨(-1697313457697916841200449),(-1376566787177830554500335),true⟩,⟨(-672031543318850234609232),(-385074237175882942925350),true⟩⟩
  | 1,5 => ⟨⟨(-1944727261504163113558702),(-1588864376107572300365615),true⟩,⟨(-608752048376497233825619),(-295553014002969787861480),true⟩⟩
  | 1,6 => ⟨⟨(-2161962104979847628895770),(-1775877928010956734311307),true⟩,⟨(-554962403075260282008947),(-220154918425888984382929),true⟩⟩
  | 1,7 => ⟨⟨(-2303064455222077304993850),(-1897812805694630936401541),true⟩,⟨(-521379128632190337601269),(-173454018478634369437771),true⟩⟩
  | 2,0 => ⟨⟨(-141417656475868822093493),(-3612183125874420682029),true⟩,⟨(-973042241806577091679960),(-829216399842848815556623),true⟩⟩
  | 2,1 => ⟨⟨49431843398709902012748,176720620169041625007318,true⟩,⟨(-977413944037531938918327),(-842600087544387426205642),true⟩⟩
  | 2,2 => ⟨⟨188458473495562253556567,309815233707216991959716,true⟩,⟨(-974545014385691152588435),(-845448547315316668388244),true⟩⟩
  | 2,3 => ⟨⟨268103824212562758297300,387535856951872675205367,true⟩,⟨(-970814712221805816594680),(-844011057895541180434575),true⟩⟩
  | 2,4 => ⟨⟨(-369887190579333336258230),(-215534636419835736541104),true⟩,⟨(-954617099377359646080651),(-798165536915534185348779),true⟩⟩
  | 2,5 => ⟨⟨(-612170493642677399639204),(-436617253826816483839281),true⟩,⟨(-920198252176129258949018),(-748171114004075556312342),true⟩⟩
  | 2,6 => ⟨⟨(-833363940709281793282363),(-632351129392817938939336),true⟩,⟨(-879298683009203683422558),(-687281486293987281602224),true⟩⟩
  | 2,7 => ⟨⟨(-981430822246591738348689),(-761008461467354596056543),true⟩,⟨(-848520150407052659851523),(-640746249130016915963298),true⟩⟩
  | 3,0 => ⟨⟨1200242450987862033317323,1329026905339281140607366,true⟩,⟨(-896991050048124788158859),(-771999328350587863353687),true⟩⟩
  | 3,1 => ⟨⟨1421601427675982214737127,1556802324283567550421952,true⟩,⟨(-903621084362701059116347),(-774545601237383878543579),true⟩⟩
  | 3,2 => ⟨⟨1591442389320129215017701,1732943491790739920582916,true⟩,⟨(-927923577808014147821194),(-794085323044263784988755),true⟩⟩
  | 3,3 => ⟨⟨1692753790594712441054808,1838688460142651737649421,true⟩,⟨(-952816196698211312285907),(-815339081787064747662800),true⟩⟩
  | 3,4 => ⟨⟨947990490130234361493437,1071514463374485860662791,true⟩,⟨(-911325029173416766551535),(-788607206677012015519516),true⟩⟩
  | 3,5 => ⟨⟨691954914175824146190684,812103732527197726750907,true⟩,⟨(-936230919989340060509832),(-813680376173562277559682),true⟩⟩
  | 3,6 => ⟨⟨469258433296686322453205,588056392168972043607958,true⟩,⟨(-957290376264901756117107),(-833319378189965929149144),true⟩⟩
  | 3,7 => ⟨⟨323931210036374463307065,442694494940133828151924,true⟩,⟨(-967612268829010551047797),(-841949651139427316739383),true⟩⟩
  | 4,0 => ⟨⟨2447639986617511619994747,2677787914242392215473572,true⟩,⟨(-1577649007831589415316683),(-1356699590598233614107656),true⟩⟩
  | 4,1 => ⟨⟨2643088388595732547657926,2917278846126820472594326,true⟩,⟨(-2002584892766281705202081),(-1734257572471965450437397),true⟩⟩
  | 4,2 => ⟨⟨2757190043121475229132926,3077787186479414554210851,true⟩,⟨(-2485665487937260085683251),(-2165502719688784299648377),true⟩⟩
  | 4,3 => ⟨⟨2787343607565032307714390,3142329454808208741729652,true⟩,⟨(-2859794183268769986836343),(-2500095860082144288134285),true⟩⟩
  | 4,4 => ⟨⟨2220169647358867833992031,2415787437728026011162325,true⟩,⟨(-1279942058653231592137451),(-1094632870531222972076823),true⟩⟩
  | 4,5 => ⟨⟨2007816361984923729098025,2179400609350799221643305,true⟩,⟨(-1101749916287997573067698),(-940236157531792882504895),true⟩⟩
  | 4,6 => ⟨⟨1841464276252559289709591,1998020445263660009687680,true⟩,⟨(-1008663423142935871273910),(-861471413574080224247960),true⟩⟩
  | 4,7 => ⟨⟨1741523714733768418124381,1890356805237017343770288,true⟩,⟨(-968401176529254411336629),(-828356364909608504284716),true⟩⟩
  | 5,0 => ⟨⟨2657850473422214736216617,3101890384564815757149839,true⟩,⟨(-3869874591862845346447767),(-3403690923842784040804888),true⟩⟩
  | 5,1 => ⟨⟨2557152215490995315761510,3028211902708531984983917,true⟩,⟨(-4184062625276290518189166),(-3684426987589742722565063),true⟩⟩
  | 5,2 => ⟨⟨2448917537258483105305748,2942599248399660429749197,true⟩,⟨(-4448765157384767441527156),(-3920707399896911246250845),true⟩⟩
  | 5,3 => ⟨⟨2369544607842453353753876,2877356521966979810564411,true⟩,⟨(-4614642903462139813957098),(-4068636276562838363161475),true⟩⟩
  | 5,4 => ⟨⟨2729141558255465272604447,3146176219447060311140741,true⟩,⟨(-3558766145033677776224103),(-3125485070384325623710774),true⟩⟩
  | 5,5 => ⟨⟨2768057373231859674248558,3161751905571454406280242,true⟩,⟨(-3292881059784027620752350),(-2887610396279299053645094),true⟩⟩
  | 5,6 => ⟨⟨2783597305164427037621093,3160024269088071388138257,true⟩,⟨(-3098337818892254923793405),(-2713533687020893900451186),true⟩⟩
  | 5,7 => ⟨⟨2787468257858451417402620,3153983803627129009058958,true⟩,⟨(-2987622336080343899706081),(-2614466345695994887824747),true⟩⟩
  | 6,0 => ⟨⟨1330434862432584912003712,1950408681310443216855956,true⟩,⟨(-5928725051397108874388232),(-5234320797597789688655065),true⟩⟩
  | 6,1 => ⟨⟨852938585462674468532942,1512551295546453829704118,true⟩,⟨(-6280781860213923503761320),(-5538439835853044914985833),true⟩⟩
  | 6,2 => ⟨⟨405975911771055318859687,1105619096118611933535820,true⟩,⟨(-6531777570156144194229957),(-5747215648103766410605009),true⟩⟩
  | 6,3 => ⟨⟨106974647348232632199849,833162529498283722123851,true⟩,⟨(-6664713523024547657955173),(-5854062008455972600295987),true⟩⟩
  | 6,4 => ⟨⟨1737813808632840264362513,2323773504705828364972712,true⟩,⟨(-5533210618837003776140848),(-4885025324058414985691507),true⟩⟩
  | 6,5 => ⟨⟨2038649100236354504570339,2592786066149303348849611,true⟩,⟨(-5159680996309037178097893),(-4553727551924544794283252),true⟩⟩
  | 6,6 => ⟨⟨2229608798791828274280643,2758998463123126633871601,true⟩,⟨(-4868431073977713032263596),(-4294716799980528772939645),true⟩⟩
  | 6,7 => ⟨⟨2326837577961003751590007,2841627439376706178568560,true⟩,⟨(-4696666521741509432971064),(-4141739555129522816758596),true⟩⟩
  | 7,0 => ⟨⟨(-2717689058570533220554999),(-1787690209306848454845917),true⟩,⟨(-6825326178541655398825990),(-5872983031572989482163307),true⟩⟩
  | 7,1 => ⟨⟨(-3579716720083523704613118),(-2608144307018809807545136),true⟩,⟨(-6476899985764295132099687),(-5520454212548182337221623),true⟩⟩
  | 7,2 => ⟨⟨(-4221210885791488868100527),(-3228132669968943995666139),true⟩,⟨(-6049519735243264966518393),(-5107378322959834755136639),true⟩⟩
  | 7,3 => ⟨⟨(-4574928201118492959797214),(-3575055620049170545662573),true⟩,⟨(-5727437713057240102879120),(-4802317844846811124678992),true⟩⟩
  | 7,4 => ⟨⟨(-1791122159430523123081338),(-917790104536731623845274),true⟩,⟨(-6978901281907151853117068),(-6053107738141615439900339),true⟩⟩
  | 7,5 => ⟨⟨(-973669248277714738003122),(-159326191158107771209892),true⟩,⟨(-6947812212764469567583713),(-6061667629195757236869639),true⟩⟩
  | 7,6 => ⟨⟨(-378522495131385049899295),388885516506742507820115,true⟩,⟨(-6827805288877283095342745),(-5979830374650576482112399),true⟩⟩
  | 7,7 => ⟨⟨(-46207424144488841822505),693139574902514124854449,true⟩,⟨(-6722958404464527218884804),(-5899878313899581585963334),true⟩⟩
  | 8,0 => ⟨⟨(-5723837633170292342020504),(-4863320111167911599059113),true⟩,⟨(-2288633861647651894046927),(-1682974437609154723125475),true⟩⟩
  | 8,1 => ⟨⟨(-5474604152284471648563933),(-4709015320658857413047046),true⟩,⟨(-1289176364650012284725395),(-806361181504790116945218),true⟩⟩
  | 8,2 => ⟨⟨(-5126616906730536152962899),(-4448178336771141964043940),true⟩,⟨(-589326504874119046279201),(-203627103810634389281501),true⟩⟩
  | 8,3 => ⟨⟨(-4867318258853605532732762),(-4244585599841597732765964),true⟩,⟨(-219941625541061533243232),116459118528793793684087,true⟩⟩
  | 8,4 => ⟨⟨(-5712612421917220638249679),(-4773344089003724857897703),true⟩,⟨(-3421255140678692853054741),(-2689898976715166380243118),true⟩⟩
  | 8,5 => ⟨⟨(-5429445304113734163013858),(-4445147413437033203539714),true⟩,⟨(-4440047904011825546728319),(-3611288092558403865341000),true⟩⟩
  | 8,6 => ⟨⟨(-5034588109673977878364937),(-4034643976785346659868288),true⟩,⟨(-5166150694144157898824499),(-4278517707985589335778606),true⟩⟩
  | 8,7 => ⟨⟨(-4734668119733952067232941),(-3733393343751513215989076),true⟩,⟨(-5554478713009213934199824),(-4639993756108440599632258),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP529Value0_0 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP529Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value0_1 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP529Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value0_2 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP529Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value0_3 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP529Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value0_4 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP529Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value0_5 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP529Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value0_6 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP529Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value0_7 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP529Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP529Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 0 j)=sharedDiskP529Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP529Value0_0
  · exact sharedDiskP529Value0_1
  · exact sharedDiskP529Value0_2
  · exact sharedDiskP529Value0_3
  · exact sharedDiskP529Value0_4
  · exact sharedDiskP529Value0_5
  · exact sharedDiskP529Value0_6
  · exact sharedDiskP529Value0_7
private theorem sharedDiskP529Value1_0 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP529Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value1_1 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP529Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value1_2 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP529Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value1_3 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP529Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value1_4 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP529Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value1_5 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP529Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value1_6 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP529Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value1_7 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP529Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP529Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 1 j)=sharedDiskP529Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP529Value1_0
  · exact sharedDiskP529Value1_1
  · exact sharedDiskP529Value1_2
  · exact sharedDiskP529Value1_3
  · exact sharedDiskP529Value1_4
  · exact sharedDiskP529Value1_5
  · exact sharedDiskP529Value1_6
  · exact sharedDiskP529Value1_7
private theorem sharedDiskP529Value2_0 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP529Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value2_1 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP529Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value2_2 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP529Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value2_3 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP529Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value2_4 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP529Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value2_5 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP529Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value2_6 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP529Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value2_7 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP529Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP529Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 2 j)=sharedDiskP529Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP529Value2_0
  · exact sharedDiskP529Value2_1
  · exact sharedDiskP529Value2_2
  · exact sharedDiskP529Value2_3
  · exact sharedDiskP529Value2_4
  · exact sharedDiskP529Value2_5
  · exact sharedDiskP529Value2_6
  · exact sharedDiskP529Value2_7
private theorem sharedDiskP529Value3_0 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP529Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value3_1 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP529Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value3_2 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP529Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value3_3 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP529Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value3_4 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP529Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value3_5 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP529Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value3_6 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP529Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value3_7 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP529Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP529Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 3 j)=sharedDiskP529Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP529Value3_0
  · exact sharedDiskP529Value3_1
  · exact sharedDiskP529Value3_2
  · exact sharedDiskP529Value3_3
  · exact sharedDiskP529Value3_4
  · exact sharedDiskP529Value3_5
  · exact sharedDiskP529Value3_6
  · exact sharedDiskP529Value3_7
private theorem sharedDiskP529Value4_0 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP529Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value4_1 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP529Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value4_2 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP529Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value4_3 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP529Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value4_4 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP529Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value4_5 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP529Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value4_6 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP529Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value4_7 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP529Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP529Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 4 j)=sharedDiskP529Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP529Value4_0
  · exact sharedDiskP529Value4_1
  · exact sharedDiskP529Value4_2
  · exact sharedDiskP529Value4_3
  · exact sharedDiskP529Value4_4
  · exact sharedDiskP529Value4_5
  · exact sharedDiskP529Value4_6
  · exact sharedDiskP529Value4_7
private theorem sharedDiskP529Value5_0 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP529Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value5_1 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP529Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value5_2 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP529Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value5_3 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP529Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value5_4 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP529Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value5_5 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP529Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value5_6 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP529Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value5_7 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP529Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP529Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 5 j)=sharedDiskP529Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP529Value5_0
  · exact sharedDiskP529Value5_1
  · exact sharedDiskP529Value5_2
  · exact sharedDiskP529Value5_3
  · exact sharedDiskP529Value5_4
  · exact sharedDiskP529Value5_5
  · exact sharedDiskP529Value5_6
  · exact sharedDiskP529Value5_7
private theorem sharedDiskP529Value6_0 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP529Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value6_1 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP529Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value6_2 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP529Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value6_3 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP529Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value6_4 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP529Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value6_5 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP529Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value6_6 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP529Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value6_7 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP529Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP529Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 6 j)=sharedDiskP529Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP529Value6_0
  · exact sharedDiskP529Value6_1
  · exact sharedDiskP529Value6_2
  · exact sharedDiskP529Value6_3
  · exact sharedDiskP529Value6_4
  · exact sharedDiskP529Value6_5
  · exact sharedDiskP529Value6_6
  · exact sharedDiskP529Value6_7
private theorem sharedDiskP529Value7_0 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP529Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value7_1 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP529Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value7_2 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP529Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value7_3 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP529Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value7_4 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP529Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value7_5 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP529Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value7_6 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP529Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value7_7 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP529Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP529Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 7 j)=sharedDiskP529Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP529Value7_0
  · exact sharedDiskP529Value7_1
  · exact sharedDiskP529Value7_2
  · exact sharedDiskP529Value7_3
  · exact sharedDiskP529Value7_4
  · exact sharedDiskP529Value7_5
  · exact sharedDiskP529Value7_6
  · exact sharedDiskP529Value7_7
private theorem sharedDiskP529Value8_0 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP529Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value8_1 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP529Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value8_2 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP529Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value8_3 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP529Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value8_4 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP529Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value8_5 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP529Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value8_6 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP529Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP529Value8_7 : truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP529Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP529Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points 8 j)=sharedDiskP529Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP529Value8_0
  · exact sharedDiskP529Value8_1
  · exact sharedDiskP529Value8_2
  · exact sharedDiskP529Value8_3
  · exact sharedDiskP529Value8_4
  · exact sharedDiskP529Value8_5
  · exact sharedDiskP529Value8_6
  · exact sharedDiskP529Value8_7
theorem sharedDiskP529Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP529Params (sharedChord521Gauss8Points i j)=sharedDiskP529Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP529Values0_eq
  · exact sharedDiskP529Values1_eq
  · exact sharedDiskP529Values2_eq
  · exact sharedDiskP529Values3_eq
  · exact sharedDiskP529Values4_eq
  · exact sharedDiskP529Values5_eq
  · exact sharedDiskP529Values6_eq
  · exact sharedDiskP529Values7_eq
  · exact sharedDiskP529Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP529Box : HorizontalRectangle := ⟨(319/400),(4/5),(943815059771497/1649267441664000),(947036285243497/1649267441664000),(406185249374390223898762356541269/1298074214633706907132624082305024),(1450823093741910725995285912307541/1298074214633706907132624082305024),(-4477523168963767388100439844458633/1298074214633706907132624082305024),(-3406579139864910422059701838942345/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP529Grid : CGrid := momentChordGrid sharedDiskP529Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP529Columns : containedInReported sharedDiskP529Grid.re sharedDiskP529Box.reLo sharedDiskP529Box.reHi=true ∧ containedInReported sharedDiskP529Grid.im sharedDiskP529Box.imLo sharedDiskP529Box.imHi=true := by
  rw [sharedDiskP529Grid,momentChordGrid_eq_tabulated sharedDiskP529Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP529Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP529Values_eq]
  decide +kernel
theorem sharedDiskP529Sound : sharedDiskP529Box.Sound := by
  intro t a tl tu al au
  change (((319/400):ℚ):ℝ)≤t at tl
  change t≤(((4/5):ℚ):ℝ) at tu
  change (((943815059771497/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((947036285243497/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP529Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(319/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((4/5):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(943815059771497/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((947036285243497/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP529Columns.1 sharedDiskP529Columns.2
def sharedDiskP529Rows : List SignRow := [positive_529.toSignRow]
theorem sharedDiskP529Rows_actual : ∀ r∈sharedDiskP529Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP529Rows.all (sharedDiskP529Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP529Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP530Params : ChordParams := ⟨⟨(-24112497901100355924096),(-23819311874109026650693),true⟩,⟨2011722510575605335212317,2027281488327492819129564,true⟩,⟨126438334414160764793943,128308068823433370686104,true⟩,⟨226005548213570211201348,228933057006573695124908,true⟩,⟨332749573845972418653215,334870800821775188903603,true⟩,⟨1161643880563822812206402,1162207677486924022064824,true⟩,⟨(-2281989438461610150729862),(-2273776873063454797929223),true⟩,⟨⟨1145167660735917244548631,1173593593434438378558930,true⟩,⟨(-11042651),11042651,true⟩⟩⟩
theorem sharedDiskP530Params_ok : chordParams (Grid.ofRats (4/5) (321/400)) (Grid.ofRats (314995680930681/549755813888000) (316069422754681/549755813888000))=sharedDiskP530Params := by decide +kernel
def sharedDiskP530Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3182563003563933334039104),(-2668064377095245267516133),true⟩,⟨(-344022413135654661117901),68233888466407407253620,true⟩⟩
  | 0,1 => ⟨⟨(-2803213015217105442989815),(-2333175560354028685042464),true⟩,⟨(-410358352626517730363134),(-21367425788789136427843),true⟩⟩
  | 0,2 => ⟨⟨(-2530794987629348241109965),(-2095651142275662917535862),true⟩,⟨(-465980300501665314796652),(-98706165006251734895495),true⟩⟩
  | 0,3 => ⟨⟨(-2378382157138764197809069),(-1963264288614415172127811),true⟩,⟨(-499806582247652910220512),(-145448468076669373713765),true⟩⟩
  | 0,4 => ⟨⟨(-3635034264962589300377685),(-3074387168883943087043130),true⟩,⟨(-283669873345199081016006),144410119303677841741325,true⟩⟩
  | 0,5 => ⟨⟨(-4098837936886224576204959),(-3498856690767336810663337),true⟩,⟨(-244720913958366312253148),188366047547179352862725,true⟩⟩
  | 0,6 => ⟨⟨(-4492836125605888548914991),(-3865897144135175055009319),true⟩,⟨(-230906800291867337288092),194924822385607829189877,true⟩⟩
  | 0,7 => ⟨⟨(-4740981694996900288368451),(-4099601376189998419958394),true⟩,⟨(-236378283873987108082270),183611000064240798421579,true⟩⟩
  | 1,0 => ⟨⟨(-1469285077435617823572635),(-1181390034361478872170801),true⟩,⟨(-726556307236039513974259),(-465037654518952494192404),true⟩⟩
  | 1,1 => ⟨⟨(-1272374068314559285698008),(-1012366661302505775979176),true⟩,⟨(-776319951847942680845253),(-536824352191444873239370),true⟩⟩
  | 1,2 => ⟨⟨(-1129665181046525145257444),(-889499110602286828980144),true⟩,⟨(-810919142779883732227766),(-587295289939798927982531),true⟩⟩
  | 1,3 => ⟨⟨(-1048588262203293127908891),(-819493354429891014114550),true⟩,⟨(-829755312228916578205787),(-615047544103097936784148),true⟩⟩
  | 1,4 => ⟨⟨(-1704818747699268500649228),(-1383257598952378171691924),true⟩,⟨(-665775506009386996877589),(-378253207407842265429833),true⟩⟩
  | 1,5 => ⟨⟨(-1951057644343745428056270),(-1594527042880529860116172),true⟩,⟨(-602814004866180760626960),(-289191085162434805090345),true⟩⟩
  | 1,6 => ⟨⟨(-2167144021718967681157272),(-1780548913842021840413558),true⟩,⟨(-549421925969394117545590),(-214341037008912283301336),true⟩⟩
  | 1,7 => ⟨⟨(-2307437317854330725429416),(-1901788210177373585381645),true⟩,⟨(-516142791171396782174644),(-168051678173854508352339),true⟩⟩
  | 2,0 => ⟨⟨(-154468126972387184869692),(-16153992343537296604540),true⟩,⟨(-970081079482032734164394),(-825993161878047156974673),true⟩⟩
  | 2,1 => ⟨⟨35770869032658407065495,163417718691282056212384,true⟩,⟨(-975582945791327242084035),(-840518801090497196962287),true⟩⟩
  | 2,2 => ⟨⟨174333005905952814719969,296011672874588672526726,true⟩,⟨(-973592667960181489014072),(-844247755956142414123569),true⟩⟩
  | 2,3 => ⟨⟨253722673452740781754043,373240141297389707072622,true⟩,⟨(-970379221057870881722516),(-843473325428229364115589),true⟩⟩
  | 2,4 => ⟨⟨(-382143231289227750317009),(-227208549043642125033146),true⟩,⟨(-950462649977849847012577),(-793722591431577089994494),true⟩⟩
  | 2,5 => ⟨⟨(-623596843280988974447921),(-447378081673229280757654),true⟩,⟨(-915021548849254349757296),(-742668989086112147998156),true⟩⟩
  | 2,6 => ⟨⟨(-844196103347713920100879),(-642165234602431504203018),true⟩,⟨(-873630800593548078982365),(-680869276777642796969864),true⟩⟩
  | 2,7 => ⟨⟨(-991743655399011024915859),(-770306181478685965742909),true⟩,⟨(-842522858478393372791653),(-634004031031092056051453),true⟩⟩
  | 3,0 => ⟨⟨1184402752449562010285795,1313042080834896567044921,true⟩,⟨(-902493720355975974725618),(-777422044892590157091453),true⟩⟩
  | 3,1 => ⟨⟨1405846733727180544185169,1540965090056317473268952,true⟩,⟨(-910507283506471964275427),(-781275059078029805049943),true⟩⟩
  | 3,2 => ⟨⟨1575843172592542382960618,1717326733745531895081096,true⟩,⟨(-935897727196853189920477),(-801830512347821787934411),true⟩⟩
  | 3,3 => ⟨⟨1677262600209401225108884,1823225292357520476648934,true⟩,⟨(-961465958349670190256206),(-823711064124584660640843),true⟩⟩
  | 3,4 => ⟨⟨932284955905376855210169,1055623503154683464204351,true⟩,⟨(-915235137748291362502973),(-792502272527765502830755),true⟩⟩
  | 3,5 => ⟨⟨676652930608531086036385,796608808341295726329660,true⟩,⟨(-938472047670013801741094),(-815949022175460857440357),true⟩⟩
  | 3,6 => ⟨⟨454497556832947047925245,573122453404050386127217,true⟩,⟨(-958044325694221600061470),(-834119317098462500617133),true⟩⟩
  | 3,7 => ⟨⟨309596754100164779308956,428212567941955992323178,true⟩,⟨(-967393798581261019173801),(-841779995023255022131220),true⟩⟩
  | 4,0 => ⟨⟨2431210713562141709379280,2661734009355707754055372,true⟩,⟨(-1593055937102429169940529),(-1371352896563278094768500),true⟩⟩
  | 4,1 => ⟨⟨2624364239615501806285482,2899059442997903354881160,true⟩,⟨(-2020683540113551951476918),(-1751405988223070028926322),true⟩⟩
  | 4,2 => ⟨⟨2735034358790331645766854,3056216176023910030447220,true⟩,⟨(-2505862657452395689434312),(-2184601424262042410458413),true⟩⟩
  | 4,3 => ⟨⟨2762115553884046983063359,3117701897200187025370979,true⟩,⟨(-2880953522355462914096329),(-2520095117515327709994717),true⟩⟩
  | 4,4 => ⟨⟨2204726656765274819095390,2400589532131329761133454,true⟩,⟨(-1292859489755171127919042),(-1106979136186690413747152),true⟩⟩
  | 4,5 => ⟨⟨1992570249623971942741078,2164298925182882097690713,true⟩,⟨(-1112753008294171952665531),(-950804948228778151878612),true⟩⟩
  | 4,6 => ⟨⟨1826129377864648462710726,1982765443935278729018664,true⟩,⟨(-1018367083519839877019541),(-870828823327861186598378),true⟩⟩
  | 4,7 => ⟨⟨1726085957656400165635373,1874966138879287249322012,true⟩,⟨(-977387172432684429586801),(-837041783307101359178257),true⟩⟩
  | 5,0 => ⟨⟨2623246698164079309228931,3067725759633888641536527,true⟩,⟨(-3890634998739056951621524),(-3423373540635938790430672),true⟩⟩
  | 5,1 => ⟨⟨2519467221907157194857719,2990850781638951467402781,true⟩,⟨(-4203731958151615165608681),(-3703127283874564160302430),true⟩⟩
  | 5,2 => ⟨⟨2408628175760805201179713,2902510026658054820959485,true⟩,⟨(-4467118185311034135181004),(-3938218414826709015526792),true⟩⟩
  | 5,3 => ⟨⟨2327631809934074833486442,2835553050583028577021741,true⟩,⟨(-4631973004128892110987321),(-4085221946797558031455027),true⟩⟩
  | 5,4 => ⟨⟨2697540401529642233164008,3115096770986509178511957,true⟩,⟨(-3580136210379168619477932),(-3145710740002547264470492),true⟩⟩
  | 5,5 => ⟨⟨2738955581286397307978144,3133218762786003535517395,true⟩,⟨(-3314421401376251123421512),(-2907979413292467673617290),true⟩⟩
  | 5,6 => ⟨⟨2756270629416410566709704,3133287282696997434768426,true⟩,⟨(-3119806022116876027275720),(-2733827406425898844753511),true⟩⟩
  | 5,7 => ⟨⟨2761127310798681057522853,3128239599281063559320044,true⟩,⟨(-3008977056075856160362867),(-2634650804245979571573067),true⟩⟩
  | 6,0 => ⟨⟨1277057093837449959929730,1895955193578794430380461,true⟩,⟨(-5931047479885800848746344),(-5237330771698182031523335),true⟩⟩
  | 6,1 => ⟨⟨796435981996784224562019,1455653465763588729963247,true⟩,⟨(-6276797124612912536880959),(-5535114257099281003968631),true⟩⟩
  | 6,2 => ⟨⟨348844266835322012469870,1048872616644609693085365,true⟩,⟨(-6521328554837673968411416),(-5737347288052071885576376),true⟩⟩
  | 6,3 => ⟨⟨49989599538032584633689,776263369589086960095743,true⟩,⟨(-6650012162507600182831083),(-5840375530503862097589281),true⟩⟩
  | 6,4 => ⟨⟨1687440744245788069470043,2272786651568218165867047,true⟩,⟨(-5541602731754245091355453),(-4893521682130139837400057),true⟩⟩
  | 6,5 => ⟨⟨1991554783322171207523794,2545421974460463990636934,true⟩,⟨(-5172448361072731644530375),(-4566183034719044650916218),true⟩⟩
  | 6,6 => ⟨⟨2185244432233607867296021,2714583150025748340774071,true⟩,⟨(-4883878240224766596156428),(-4309598202368118151408953),true⟩⟩
  | 6,7 => ⟨⟨2284127172213783618632788,2798977465928670589625389,true⟩,⟨(-4713431337843386496356499),(-4157813662420729278903600),true⟩⟩
  | 7,0 => ⟨⟨(-2755468679465001745416989),(-1828489541239469647545152),true⟩,⟨(-6777079344794575030823327),(-5829947490263983690270932),true⟩⟩
  | 7,1 => ⟨⟨(-3605716163479573053186993),(-2638400178904929009343144),true⟩,⟨(-6422496909021005354081497),(-5472394014770768151920446),true⟩⟩
  | 7,2 => ⟨⟨(-4236557429261779823585039),(-3248670887539295710880979),true⟩,⟨(-5992780375014873472770329),(-5057676051242433921587348),true⟩⟩
  | 7,3 => ⟨⟨(-4583602821392986970580989),(-3589430504508606907493944),true⟩,⟨(-5670607376735090771915425),(-4752815306520877890723287),true⟩⟩
  | 7,4 => ⟨⟨(-1838561362583500140337550),(-966984915953474826975813),true⟩,⟨(-6939908447428654741706943),(-6017979144141375058959491),true⟩⟩
  | 7,5 => ⟨⟨(-1027042461843555008671932),(-213419082364212235783310),true⟩,⟨(-6918591685916320167148073),(-6035078449542541059449662),true⟩⟩
  | 7,6 => ⟨⟨(-434601806384166494589563),332577698528190319980960,true⟩,⟨(-6806398185844630517507476),(-5960157606288216967345469),true⟩⟩
  | 7,7 => ⟨⟨(-103159983919606789322572),636318906177541724371405,true⟩,⟨(-6706111005857552529921241),(-5884271326113100162798105),true⟩⟩
  | 8,0 => ⟨⟨(-5698079603262329245323150),(-4843903587439197865842898),true⟩,⟨(-2261251487901520911838924),(-1660955881628571727134198),true⟩⟩
  | 8,1 => ⟨⟨(-5449022046551005842627902),(-4688729059138780203580022),true⟩,⟨(-1274208897295408209286551),(-795201314259493483176628),true⟩⟩
  | 8,2 => ⟨⟨(-5104135080816474101406477),(-4429924216478630205948873),true⟩,⟨(-582929491399799509648993),(-199819265283053312932455),true⟩⟩
  | 8,3 => ⟨⟨(-4847648094471816053138487),(-4228431795959936665993028),true⟩,⟨(-217811482517468224655788),116721462561555466396734,true⟩⟩
  | 8,4 => ⟨⟨(-5692092283710597433373726),(-4759708139099830744793770),true⟩,⟨(-3380797822935915436042980),(-2656147412397228984655434),true⟩⟩
  | 8,5 => ⟨⟨(-5418489051353798584579271),(-4440975176175036825560289),true⟩,⟨(-4389909267141531459423016),(-3568563896763742319090703),true⟩⟩
  | 8,6 => ⟨⟨(-5033511676493680245553403),(-4039896538225123136076918),true⟩,⟨(-5111170631248859235210002),(-4231074815549205765057742),true⟩⟩
  | 8,7 => ⟨⟨(-4740110106285827411826507),(-3744760053939074175612848),true⟩,⟨(-5497988714459233623652177),(-4590931020538786652193282),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP530Value0_0 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP530Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value0_1 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP530Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value0_2 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP530Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value0_3 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP530Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value0_4 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP530Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value0_5 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP530Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value0_6 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP530Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value0_7 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP530Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP530Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 0 j)=sharedDiskP530Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP530Value0_0
  · exact sharedDiskP530Value0_1
  · exact sharedDiskP530Value0_2
  · exact sharedDiskP530Value0_3
  · exact sharedDiskP530Value0_4
  · exact sharedDiskP530Value0_5
  · exact sharedDiskP530Value0_6
  · exact sharedDiskP530Value0_7
private theorem sharedDiskP530Value1_0 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP530Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value1_1 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP530Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value1_2 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP530Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value1_3 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP530Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value1_4 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP530Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value1_5 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP530Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value1_6 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP530Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value1_7 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP530Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP530Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 1 j)=sharedDiskP530Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP530Value1_0
  · exact sharedDiskP530Value1_1
  · exact sharedDiskP530Value1_2
  · exact sharedDiskP530Value1_3
  · exact sharedDiskP530Value1_4
  · exact sharedDiskP530Value1_5
  · exact sharedDiskP530Value1_6
  · exact sharedDiskP530Value1_7
private theorem sharedDiskP530Value2_0 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP530Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value2_1 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP530Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value2_2 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP530Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value2_3 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP530Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value2_4 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP530Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value2_5 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP530Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value2_6 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP530Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value2_7 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP530Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP530Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 2 j)=sharedDiskP530Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP530Value2_0
  · exact sharedDiskP530Value2_1
  · exact sharedDiskP530Value2_2
  · exact sharedDiskP530Value2_3
  · exact sharedDiskP530Value2_4
  · exact sharedDiskP530Value2_5
  · exact sharedDiskP530Value2_6
  · exact sharedDiskP530Value2_7
private theorem sharedDiskP530Value3_0 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP530Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value3_1 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP530Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value3_2 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP530Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value3_3 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP530Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value3_4 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP530Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value3_5 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP530Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value3_6 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP530Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value3_7 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP530Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP530Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 3 j)=sharedDiskP530Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP530Value3_0
  · exact sharedDiskP530Value3_1
  · exact sharedDiskP530Value3_2
  · exact sharedDiskP530Value3_3
  · exact sharedDiskP530Value3_4
  · exact sharedDiskP530Value3_5
  · exact sharedDiskP530Value3_6
  · exact sharedDiskP530Value3_7
private theorem sharedDiskP530Value4_0 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP530Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value4_1 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP530Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value4_2 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP530Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value4_3 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP530Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value4_4 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP530Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value4_5 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP530Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value4_6 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP530Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value4_7 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP530Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP530Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 4 j)=sharedDiskP530Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP530Value4_0
  · exact sharedDiskP530Value4_1
  · exact sharedDiskP530Value4_2
  · exact sharedDiskP530Value4_3
  · exact sharedDiskP530Value4_4
  · exact sharedDiskP530Value4_5
  · exact sharedDiskP530Value4_6
  · exact sharedDiskP530Value4_7
private theorem sharedDiskP530Value5_0 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP530Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value5_1 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP530Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value5_2 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP530Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value5_3 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP530Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value5_4 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP530Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value5_5 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP530Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value5_6 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP530Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value5_7 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP530Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP530Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 5 j)=sharedDiskP530Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP530Value5_0
  · exact sharedDiskP530Value5_1
  · exact sharedDiskP530Value5_2
  · exact sharedDiskP530Value5_3
  · exact sharedDiskP530Value5_4
  · exact sharedDiskP530Value5_5
  · exact sharedDiskP530Value5_6
  · exact sharedDiskP530Value5_7
private theorem sharedDiskP530Value6_0 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP530Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value6_1 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP530Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value6_2 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP530Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value6_3 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP530Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value6_4 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP530Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value6_5 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP530Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value6_6 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP530Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value6_7 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP530Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP530Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 6 j)=sharedDiskP530Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP530Value6_0
  · exact sharedDiskP530Value6_1
  · exact sharedDiskP530Value6_2
  · exact sharedDiskP530Value6_3
  · exact sharedDiskP530Value6_4
  · exact sharedDiskP530Value6_5
  · exact sharedDiskP530Value6_6
  · exact sharedDiskP530Value6_7
private theorem sharedDiskP530Value7_0 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP530Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value7_1 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP530Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value7_2 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP530Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value7_3 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP530Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value7_4 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP530Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value7_5 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP530Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value7_6 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP530Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value7_7 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP530Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP530Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 7 j)=sharedDiskP530Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP530Value7_0
  · exact sharedDiskP530Value7_1
  · exact sharedDiskP530Value7_2
  · exact sharedDiskP530Value7_3
  · exact sharedDiskP530Value7_4
  · exact sharedDiskP530Value7_5
  · exact sharedDiskP530Value7_6
  · exact sharedDiskP530Value7_7
private theorem sharedDiskP530Value8_0 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP530Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value8_1 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP530Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value8_2 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP530Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value8_3 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP530Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value8_4 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP530Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value8_5 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP530Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value8_6 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP530Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP530Value8_7 : truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP530Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP530Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points 8 j)=sharedDiskP530Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP530Value8_0
  · exact sharedDiskP530Value8_1
  · exact sharedDiskP530Value8_2
  · exact sharedDiskP530Value8_3
  · exact sharedDiskP530Value8_4
  · exact sharedDiskP530Value8_5
  · exact sharedDiskP530Value8_6
  · exact sharedDiskP530Value8_7
theorem sharedDiskP530Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP530Params (sharedChord521Gauss8Points i j)=sharedDiskP530Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP530Values0_eq
  · exact sharedDiskP530Values1_eq
  · exact sharedDiskP530Values2_eq
  · exact sharedDiskP530Values3_eq
  · exact sharedDiskP530Values4_eq
  · exact sharedDiskP530Values5_eq
  · exact sharedDiskP530Values6_eq
  · exact sharedDiskP530Values7_eq
  · exact sharedDiskP530Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP530Box : HorizontalRectangle := ⟨(4/5),(321/400),(314995680930681/549755813888000),(316069422754681/549755813888000),(751137003269403515676659954369687/2596148429267413814265248164610048),(2818438596233631510402718221354135/2596148429267413814265248164610048),(-1118503126986531433177957659418565/324518553658426726783156020576256),(-853484706676364058005273579462597/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP530Grid : CGrid := momentChordGrid sharedDiskP530Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP530Columns : containedInReported sharedDiskP530Grid.re sharedDiskP530Box.reLo sharedDiskP530Box.reHi=true ∧ containedInReported sharedDiskP530Grid.im sharedDiskP530Box.imLo sharedDiskP530Box.imHi=true := by
  rw [sharedDiskP530Grid,momentChordGrid_eq_tabulated sharedDiskP530Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP530Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP530Values_eq]
  decide +kernel
theorem sharedDiskP530Sound : sharedDiskP530Box.Sound := by
  intro t a tl tu al au
  change (((4/5):ℚ):ℝ)≤t at tl
  change t≤(((321/400):ℚ):ℝ) at tu
  change (((314995680930681/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((316069422754681/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP530Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(4/5))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((321/400):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(314995680930681/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((316069422754681/549755813888000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP530Columns.1 sharedDiskP530Columns.2
def sharedDiskP530Rows : List SignRow := [positive_530.toSignRow]
theorem sharedDiskP530Rows_actual : ∀ r∈sharedDiskP530Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP530Rows.all (sharedDiskP530Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP530Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP527Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP528Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP529Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP530Rows_actual
