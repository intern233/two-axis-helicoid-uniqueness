import TwoAxisHelicoid.PdfSharedChord469Gauss8
import TwoAxisHelicoid.PdfSharedChord469Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP469Params : ChordParams := ⟨⟨(-3792772575279748596428),(-3045001778040279689665),true⟩,⟨3347378347920648673937917,3496532072468663274695087,true⟩,⟨53939839748344227052217,61511412810385128327838,true⟩,⟨67035608637071013071376,75838116286278945524466,true⟩,⟨120965970705130544744534,135087670366322696683125,true⟩,⟨1201363998226367768015682,1202851116816066216313190,true⟩,⟨(-3598922125668220793443082),(-3462565423041484746749775),true⟩,⟨⟨1152810764143541094910254,1253609083762335675761271,true⟩,⟨(-46),46,true⟩⟩⟩
theorem sharedDiskP469Params_ok : chordParams (Grid.ofRats (21/40) (109/200)) (Grid.ofRats (3408482035145/6597069766656) (3428211200309/6597069766656))=sharedDiskP469Params := by decide +kernel
def sharedDiskP469Values (i : Fin 15) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-11318158934253356390576983),(-2070288268671506848336882),true⟩,⟨(-4042485480401698931315221),4974825601057574345697363,true⟩⟩
  | 0,1 => ⟨⟨(-10666521445724163184185827),(-1829576369461916673859809),true⟩,⟨(-4064564908461715060095485),4671024069764581046069339,true⟩⟩
  | 0,2 => ⟨⟨(-10143364659185427434224133),(-1662521121721728162416023),true⟩,⟨(-4063436899732776780697220),4380682376950880779756543,true⟩⟩
  | 0,3 => ⟨⟨(-9826846252121438937923027),(-1546131337892905862593756),true⟩,⟨(-4055651644348086620926052),4189526263284422034178925,true⟩⟩
  | 0,4 => ⟨⟨(-11997585670992425041888695),(-2384642846225069101452701),true⟩,⟨(-3986832580333592026103004),5199045852120284217562274,true⟩⟩
  | 0,5 => ⟨⟨(-12605583402733045572471041),(-2736073160506054521509167),true⟩,⟨(-3904181311925078134147738),5291571145857363942794881,true⟩⟩
  | 0,6 => ⟨⟨(-13066561418885518050886707),(-3056589486715452781080241),true⟩,⟨(-3818520083178093690990331),5273830586241857657874009,true⟩⟩
  | 0,7 => ⟨⟨(-13335168101760606517228221),(-3268014943843134422942368),true⟩,⟨(-3759020980947753145763827),5221530970554713292486441,true⟩⟩
  | 1,0 => ⟨⟨(-7539295291373913398329571),(-870029966237488229574485),true⟩,⟨(-3879980052285745305229042),2614285214086023437367722,true⟩⟩
  | 1,1 => ⟨⟨(-6949961859106212178573896),(-727652951632814782584966),true⟩,⟨(-3809907456941496807318559),2186463188513707905822586,true⟩⟩
  | 1,2 => ⟨⟨(-6504255028845627940800992),(-625014066351428132890459),true⟩,⟨(-3752197501826189705326868),1864274078998921215191672,true⟩⟩
  | 1,3 => ⟨⟨(-6244947667608960386963362),(-566786390559069056441132),true⟩,⟨(-3716994119311139080009179),1678318759545350569292966,true⟩⟩
  | 1,4 => ⟨⟨(-8201010613352056068780018),(-1042050432620922773578493),true⟩,⟨(-3948542350952084005482489),3091014641709628844938844,true⟩⟩
  | 1,5 => ⟨⟨(-8840408721484868446243395),(-1224229736756208054625430),true⟩,⟨(-4002445130983282822927298),3540284413929641622513184,true⟩⟩
  | 1,6 => ⟨⟨(-9358070895024468559282809),(-1386117580071246823369177),true⟩,⟨(-4035426745044443438664781),3889555376531234683864505,true⟩⟩
  | 1,7 => ⟨⟨(-9673367106297955135293047),(-1492201850793948075884795),true⟩,⟨(-4050122032584933961313048),4093333535562231456032940,true⟩⟩
  | 2,0 => ⟨⟨(-4546947936635060761573152),(-193418720496394790838959),true⟩,⟨(-3464567773529933489520687),647235023315843411973090,true⟩⟩
  | 2,1 => ⟨⟨(-4143806844546652618000971),(-102267145461332307037272),true⟩,⟨(-3399732421827558681129947),425202004541816286419242,true⟩⟩
  | 2,2 => ⟨⟨(-3844518103996275135340999),(-32617221942436347509198),true⟩,⟨(-3350404556332564149847518),264679334106857465583108,true⟩⟩
  | 2,3 => ⟨⟨(-3672101040934291570898187),8832010057414947505881,true⟩,⟨(-3321499271137164589468674),174132212167195152763577,true⟩⟩
  | 2,4 => ⟨⟨(-5012819544146233129291861),(-296324007068731812125495),true⟩,⟨(-3537234767473169794758899),910529083598931533279777,true⟩⟩
  | 2,5 => ⟨⟨(-5480036613212781763104705),(-398471691297614562093837),true⟩,⟨(-3607574908575848945810895),1180005117311130359723311,true⟩⟩
  | 2,6 => ⟨⟨(-5873567035265145009935902),(-484751540621527798058819),true⟩,⟨(-3664709772741669431958419),1414868275803602632826033,true⟩⟩
  | 2,7 => ⟨⟨(-6121766772901640431094702),(-539424924132792199243901),true⟩,⟨(-3699886443004771164042089),1590517192497608740261075,true⟩⟩
  | 3,0 => ⟨⟨(-2595808735819140483054981),312441275884830534954200,true⟩,⟨(-3123451309197917956435978),(-275703284351816201203909),true⟩⟩
  | 3,1 => ⟨⟨(-2343011435313321917208703),393846349011621360838444,true⟩,⟨(-3072688736613623660136993),(-361016942066214080856988),true⟩⟩
  | 3,2 => ⟨⟨(-2153371339969953024195280),457579393389777721359268,true⟩,⟨(-3033536498618431443368964),(-422071298236274627646388),true⟩⟩
  | 3,3 => ⟨⟨(-2043190672870135894182628),495736150420239392810842,true⟩,⟨(-3010312029235779844778541),(-456290484845587013482182),true⟩⟩
  | 3,4 => ⟨⟨(-2885258795394315883581325),223715366490607864280703,true⟩,⟨(-3179871732071678432403011),(-173076656911839170574702),true⟩⟩
  | 3,5 => ⟨⟨(-3173960165348230281867645),139372220549194920347251,true⟩,⟨(-3234637786054434434250739),(-66099485488072947355234),true⟩⟩
  | 3,6 => ⟨⟨(-3426810412601974181150401),71179977411522428199689,true⟩,⟨(-3279715694365522367771410),48032489956402544297911,true⟩⟩
  | 3,7 => ⟨⟨(-3590552334781856880099507),29345544383474487016264,true⟩,⟨(-3307696818381934170590766),131841372671487867869886,true⟩⟩
  | 4,0 => ⟨⟨150022262653790239739291,1724899659017657606512153,true⟩,⟨(-2412270870966638751384796),(-706679888414094638956479),true⟩⟩
  | 4,1 => ⟨⟨503476754822806244552027,2029546859640933592929927,true⟩,⟨(-2283142035831985611199425),(-675784347019563503004417),true⟩⟩
  | 4,2 => ⟨⟨749879379613010731028108,2254943648680926054548138,true⟩,⟨(-2183004457996809855697611),(-638342237288764639677517),true⟩⟩
  | 4,3 => ⟨⟨888845937807814076327751,2384129363037860556701110,true⟩,⟨(-2122356014023165575655880),(-611874927235856876553357),true⟩⟩
  | 4,4 => ⟨⟨(-376065863121546021144315),1373059370580596377431709,true⟩,⟨(-2588149306057953580508325),(-709099190936844127366407),true⟩⟩
  | 4,5 => ⟨⟨(-962428751107447565756765),1021382552535032104455617,true⟩,⟨(-2755627043918693239368389),(-667921852333523187965128),true⟩⟩
  | 4,6 => ⟨⟨(-1514897465548424967576211),725754435217687156344853,true⟩,⟨(-2893115253631553024295032),(-589450196512254688244382),true⟩⟩
  | 4,7 => ⟨⟨(-1913551896604227127133705),541748485578736224867390,true⟩,⟨(-2982492864284470905824508),(-495302943592723309873444),true⟩⟩
  | 5,0 => ⟨⟨2314161147414915638178459,3732629835835883489178815,true⟩,⟨(-1315333408722905125929488),(-146152453707058166243678),true⟩⟩
  | 5,1 => ⟨⟨2560549063566193277602514,3953104269902987993366512,true⟩,⟨(-1131527989879863575161462),(-31643570369620857608126),true⟩⟩
  | 5,2 => ⟨⟨2718545100211866872291392,4086915980433754129473349,true⟩,⟨(-1001156533567830530370888),50270969230174686356203,true⟩⟩
  | 5,3 => ⟨⟨2799718761661137456029452,4152026253072513001364119,true⟩,⟨(-928766418201414493932847),95627892740419320485524,true⟩⟩
  | 5,4 => ⟨⟨1982331875477987459276140,3423276867701237976768698,true⟩,⟨(-1536839836605939435557237),(-283992357066131559522591),true⟩⟩
  | 5,5 => ⟨⟨1598802576086438854931597,3058012602797484527160842,true⟩,⟨(-1765004185493827576507733),(-421625784921202466390812),true⟩⟩
  | 5,6 => ⟨⟨1235015355116129670584321,2710720550176383835138139,true⟩,⟨(-1958146706617869013472682),(-530142238180553534705478),true⟩⟩
  | 5,7 => ⟨⟨985776360075345077399295,2474970386484860617690177,true⟩,⟨(-2078269150171587373692100),(-591216524455870519878242),true⟩⟩
  | 6,0 => ⟨⟨3187034721797685536858756,4238026164343841070400500,true⟩,⟨(-293598300123192383160018),421918893603130668486057,true⟩⟩
  | 6,1 => ⟨⟨3143158090264269512412879,4108262395425534917702068,true⟩,⟨(-218013060886753009127934),434763748872742531649419,true⟩⟩
  | 6,2 => ⟨⟨3089963668083389145928676,3992354576549836499875493,true⟩,⟨(-180133281763130055691774),430281462186702819435562,true⟩⟩
  | 6,3 => ⟨⟨3053734641882489710871580,3921182363291926593499474,true⟩,⟨(-165453409829429126865654),422555400421466369691179,true⟩⟩
  | 6,4 => ⟨⟨3184041273316619542680225,4331807350325408046505031,true⟩,⟨(-416865703081169591877033),377597332814100812985863,true⟩⟩
  | 6,5 => ⟨⟨3107391299175551971307983,4344720055664376622623469,true⟩,⟨(-581398475732755008417558),298065693257870292788895,true⟩⟩
  | 6,6 => ⟨⟨2973769043251796809219302,4277404158939671613717682,true⟩,⟨(-753829905487810345258259),201537577809451792235217,true⟩⟩
  | 6,7 => ⟨⟨2852656763958842928353551,4192628998624804516931266,true⟩,⟨(-878924897271556640683402),126403162140882642433762,true⟩⟩
  | 7,0 => ⟨⟨2726166815075442036579776,3669863776904311086689954,true⟩,⟨(-298707973793778001572473),341092051760451109681074,true⟩⟩
  | 7,1 => ⟨⟨2694133486607500000242921,3706726672158677653405634,true⟩,⟨(-411088913074553592273060),288138482000149602798968,true⟩⟩
  | 7,2 => ⟨⟨2702958415099169063887520,3800167794184869504692561,true⟩,⟨(-545863913914028108790082),229217548639012192991758,true⟩⟩
  | 7,3 => ⟨⟨2726783936937285660049496,3894437407821381463756007,true⟩,⟨(-657574825690342850559400),182219360595808762700969,true⟩⟩
  | 7,4 => ⟨⟨2799867626263015321563198,3699049690923996816885517,true⟩,⟨(-223122894152516045350011),380860222017464541045861,true⟩⟩
  | 7,5 => ⟨⟨2893670034086270049589001,3768733102670673851776633,true⟩,⟨(-181818174687817439113644),405628826309261657130712,true⟩⟩
  | 7,6 => ⟨⟨2978296286223504765966601,3842322526059323171912906,true⟩,⟨(-165651863923006288067242),416973661528380854551737,true⟩⟩
  | 7,7 => ⟨⟨3031311320715423589712333,3891252606429690089893242,true⟩,⟨(-162672883534811578973807),419892468794849652249669,true⟩⟩
  | 8,0 => ⟨⟨2990246559210062908806908,4716621109311762136066626,true⟩,⟨(-1576681069737897430119993),(-183112334004852310201757),true⟩⟩
  | 8,1 => ⟨⟨3105457027760479413520203,5148089916784145370967331,true⟩,⟨(-2126843986762255299887946),(-395620221437640121309526),true⟩⟩
  | 8,2 => ⟨⟨3189716063127946405524780,5590060478481784888017233,true⟩,⟨(-2769556496480851948891399),(-642639151717250699408217),true⟩⟩
  | 8,3 => ⟨⟨3222554276361006072731635,5906235769176132446553015,true⟩,⟨(-3290717321223172178696684),(-841466839636565042625156),true⟩⟩
  | 8,4 => ⟨⟨2883152079320680648578577,4376250968117108491766146,true⟩,⟨(-1184279528837353538267113),(-31101250622355827094002),true⟩⟩
  | 8,5 => ⟨⟨2806067789068835037504073,4144451009251932898330396,true⟩,⟨(-931028266049717353896074),70108029199739541075373,true⟩⟩
  | 8,6 => ⟨⟨2760634630829864722059516,4005659113347826258625362,true⟩,⟨(-780833937749338045723266),131351052714932486436483,true⟩⟩
  | 8,7 => ⟨⟨2739451951481716213389629,3937565164415583493550952,true⟩,⟨(-705995015107757601966850),162144704147585171598703,true⟩⟩
  | 9,0 => ⟨⟨3162122571372790396098480,6668805408613091072129204,true⟩,⟨(-4846548423738882372400874),(-1424112510382165205929571),true⟩⟩
  | 9,1 => ⟨⟨3092536542253082113821426,6880506976811246620100089,true⟩,⟨(-5388275472639485238253244),(-1622451196806290331316790),true⟩⟩
  | 9,2 => ⟨⟨3011317555288678307691159,7048912671361760457354012,true⟩,⟨(-5871893258784190988790357),(-1797321592253654593101056),true⟩⟩
  | 9,3 => ⟨⟨2948572677896752984052199,7149441188531569416430924,true⟩,⟨(-6189387735978868145715632),(-1910953130179818232245279),true⟩⟩
  | 9,4 => ⟨⟨3205597842885988161206196,6447223996219493607961675,true⟩,⟨(-4340025853517872334578120),(-1236437494945116501751452),true⟩⟩
  | 9,5 => ⟨⟨3224588051498866910985519,6248588583492535580590690,true⟩,⟨(-3927663175400425231846598),(-1082160862275564351858548),true⟩⟩
  | 9,6 => ⟨⟨3228574718933235957275297,6097760591408957602149049,true⟩,⟨(-3636597702794909911195223),(-972513218261729590931700),true⟩⟩
  | 9,7 => ⟨⟨3227250398552112668400441,6009791059630642518159028,true⟩,⟨(-3474628197955020503667224),(-911244024194522082333905),true⟩⟩
  | 10,0 => ⟨⟨1962341409234047349328958,7749381394470347053467367,true⟩,⟨(-9295033222709850744721793),(-2968435849926448697773187),true⟩⟩
  | 10,1 => ⟨⟨1436966652850762044120320,7800587233800300871018896,true⟩,⟨(-10421581583916810869274883),(-3324796885871778906967085),true⟩⟩
  | 10,2 => ⟨⟨906311385265415802546334,7769719485397304254105726,true⟩,⟨(-11391460610755036986177676),(-3617991262049693612256473),true⟩⟩
  | 10,3 => ⟨⟨499524678247493385266444,7711282582738087644021595,true⟩,⟨(-12020327332217964514113595),(-3796136001254990826198317),true⟩⟩
  | 10,4 => ⟨⟨2380639706631587629090978,7617207245506106803484860,true⟩,⟨(-8215817276414586407353469),(-2612718860644558094020610),true⟩⟩
  | 10,5 => ⟨⟨2664607482557962649660154,7448114910391102095535226,true⟩,⟨(-7327627979874450621670252),(-2310310773784747589318119),true⟩⟩
  | 10,6 => ⟨⟨2832536120059080988360270,7295023756155021215285875,true⟩,⟨(-6699643451518907607364393),(-2091561545957438854411270),true⟩⟩
  | 10,7 => ⟨⟨2913851492043234218388928,7197625023769032724249816,true⟩,⟨(-6350899653573724015301549),(-1968392992647752245327558),true⟩⟩
  | 11,0 => ⟨⟨(-2085481449520991576245677),7094611736770253727942644,true⟩,⟨(-14778394437769565462002499),(-4437328783400628553257583),true⟩⟩
  | 11,1 => ⟨⟨(-3003014625366066546226457),6789973947123236979117351,true⟩,⟨(-15536862830654087069929063),(-4578846986795276729295283),true⟩⟩
  | 11,2 => ⟨⟨(-3799252403323118073785890),6497652292800662879251587,true⟩,⟨(-16123685409873072771246575),(-4673789725353091921144186),true⟩⟩
  | 11,3 => ⟨⟨(-4309351296071654150089641),6297969507300297428946363,true⟩,⟨(-16467323491743586946243457),(-4722110540265409478637193),true⟩⟩
  | 11,4 => ⟨⟨(-1206791314826409400316022),7349178526623514869284514,true⟩,⟨(-13959426269883203155748032),(-4265326187980386262159834),true⟩⟩
  | 11,5 => ⟨⟨(-480797824297960231669776),7526966067482450205456214,true⟩,⟨(-13203798973069721110763518),(-4091890809469499336940119),true⟩⟩
  | 11,6 => ⟨⟨33226039254783007265633,7631851484984286319596161,true⟩,⟨(-12616907571948999251172913),(-3948656751323974118588254),true⟩⟩
  | 11,7 => ⟨⟨309150368999219263490644,7681312673981211686537576,true⟩,⟨(-12269548172851870678146944),(-3860664754830228224565553),true⟩⟩
  | 12,0 => ⟨⟨(-8755808145981082369386774),4198769382745232901646842,true⟩,⟨(-18493999683071381383407214),(-4777572508447853114842769),true⟩⟩
  | 12,1 => ⟨⟨(-10141629220856068426540607),3417649244773101848365550,true⟩,⟨(-18772941119640825316778113),(-4665658125362068252584401),true⟩⟩
  | 12,2 => ⟨⟨(-11264253991864730369008614),2744517002832283724786808,true⟩,⟨(-18861943514376528372583521),(-4528132017993204548389644),true⟩⟩
  | 12,3 => ⟨⟨(-12006115876588718870226167),2341746896434242229318169,true⟩,⟨(-18853267165837978482983454),(-4328196467899081785000312),true⟩⟩
  | 12,4 => ⟨⟨(-7320026685732243360398438),4943843880720287341025220,true⟩,⟨(-18024717348136836213418500),(-4828403887259511861895768),true⟩⟩
  | 12,5 => ⟨⟨(-6052521743259777086648459),5548954900869329824701484,true⟩,⟨(-17464288667939940226777769),(-4819467966506797211037423),true⟩⟩
  | 12,6 => ⟨⟨(-5107443367334533929164906),5967422269897392264368655,true⟩,⟨(-16957025789983517167638028),(-4779316145555460389437889),true⟩⟩
  | 12,7 => ⟨⟨(-4564888388840752323218123),6194487356084393360866117,true⟩,⟨(-16630380665411256957367371),(-4742821369578849502209719),true⟩⟩
  | 13,0 => ⟨⟨(-16845669084994184669888092),(-245527290379823915013752),true⟩,⟨(-16931717673927442220336714),(-1977745623702909245314649),true⟩⟩
  | 13,1 => ⟨⟨(-17727084360972881845562962),(-920739521047280956965591),true⟩,⟨(-15763909723955712891698148),(-1178529334388057454108059),true⟩⟩
  | 13,2 => ⟨⟨(-18199557752236613518019519),(-1420619641712846180626220),true⟩,⟨(-14655764779787460035745695),(-535917608692977266956012),true⟩⟩
  | 13,3 => ⟨⟨(-18377032782052650199001338),(-1702139279901760333480762),true⟩,⟨(-13917534766107673314162320),(-152220973086322534744820),true⟩⟩
  | 13,4 => ⟨⟨(-15609953764551471821467742),530018317805858473179347,true⟩,⟨(-17876734920608057752126659),(-2787000089274714012735391),true⟩⟩
  | 13,5 => ⟨⟨(-14256605209076597829613934),1267950808361467703317478,true⟩,⟨(-18466543634538988020784156),(-3469974780817711526734028),true⟩⟩
  | 13,6 => ⟨⟨(-13091609770847226142215953),1842493336015828598108779,true⟩,⟨(-18741596359496936494760458),(-3949673453982039883873568),true⟩⟩
  | 13,7 => ⟨⟨(-12363712075581354652138179),2180616780688210997527008,true⟩,⟨(-18830165091138691845962976),(-4210034301026082940532657),true⟩⟩
  | 14,0 => ⟨⟨(-17046334310481290314811985),(-3131885774716630269227585),true⟩,⟨(-7473758393023693710458550),3460574437237830959763534,true⟩⟩
  | 14,1 => ⟨⟨(-15866038266181943635785678),(-3287529786012629585188559),true⟩,⟨(-5665248343538247264193836),4283567993891896183115139,true⟩⟩
  | 14,2 => ⟨⟨(-14758835993920929935893819),(-3258955696644687031199217),true⟩,⟨(-4325348419486787033002206),4769132803948932516959885,true⟩⟩
  | 14,3 => ⟨⟨(-14077866998084807555167466),(-3173800949287996295045702),true⟩,⟨(-3570474212333689184224110),4989755760034209350087815,true⟩⟩
  | 14,4 => ⟨⟨(-17960088876537278924306645),(-2843391928572898099068468),true⟩,⟨(-9483229118215958700415275),2340160362477380439316621,true⟩⟩
  | 14,5 => ⟨⟨(-18423036166713770399434967),(-2461620610317746643396357),true⟩,⟨(-11337955232664109032791673),1258642505980677966939442,true⟩⟩
  | 14,6 => ⟨⟨(-18502654680368547220485843),(-2086719378165956364009759),true⟩,⟨(-12740853890779920297910570),495148698677281328339958,true⟩⟩
  | 14,7 => ⟨⟨(-18432501914157965136235711),(-1832470596377279919577759),true⟩,⟨(-13542400100926411684179269),32649027923679274624882,true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP469Value0_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 0 (0:Fin 8))=sharedDiskP469Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value0_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 0 (1:Fin 8))=sharedDiskP469Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value0_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 0 (2:Fin 8))=sharedDiskP469Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value0_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 0 (3:Fin 8))=sharedDiskP469Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value0_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 0 (4:Fin 8))=sharedDiskP469Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value0_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 0 (5:Fin 8))=sharedDiskP469Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value0_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 0 (6:Fin 8))=sharedDiskP469Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value0_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 0 (7:Fin 8))=sharedDiskP469Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 0 j)=sharedDiskP469Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value0_0
  · exact sharedDiskP469Value0_1
  · exact sharedDiskP469Value0_2
  · exact sharedDiskP469Value0_3
  · exact sharedDiskP469Value0_4
  · exact sharedDiskP469Value0_5
  · exact sharedDiskP469Value0_6
  · exact sharedDiskP469Value0_7
private theorem sharedDiskP469Value1_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 1 (0:Fin 8))=sharedDiskP469Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value1_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 1 (1:Fin 8))=sharedDiskP469Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value1_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 1 (2:Fin 8))=sharedDiskP469Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value1_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 1 (3:Fin 8))=sharedDiskP469Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value1_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 1 (4:Fin 8))=sharedDiskP469Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value1_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 1 (5:Fin 8))=sharedDiskP469Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value1_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 1 (6:Fin 8))=sharedDiskP469Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value1_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 1 (7:Fin 8))=sharedDiskP469Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 1 j)=sharedDiskP469Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value1_0
  · exact sharedDiskP469Value1_1
  · exact sharedDiskP469Value1_2
  · exact sharedDiskP469Value1_3
  · exact sharedDiskP469Value1_4
  · exact sharedDiskP469Value1_5
  · exact sharedDiskP469Value1_6
  · exact sharedDiskP469Value1_7
private theorem sharedDiskP469Value2_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 2 (0:Fin 8))=sharedDiskP469Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value2_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 2 (1:Fin 8))=sharedDiskP469Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value2_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 2 (2:Fin 8))=sharedDiskP469Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value2_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 2 (3:Fin 8))=sharedDiskP469Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value2_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 2 (4:Fin 8))=sharedDiskP469Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value2_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 2 (5:Fin 8))=sharedDiskP469Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value2_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 2 (6:Fin 8))=sharedDiskP469Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value2_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 2 (7:Fin 8))=sharedDiskP469Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 2 j)=sharedDiskP469Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value2_0
  · exact sharedDiskP469Value2_1
  · exact sharedDiskP469Value2_2
  · exact sharedDiskP469Value2_3
  · exact sharedDiskP469Value2_4
  · exact sharedDiskP469Value2_5
  · exact sharedDiskP469Value2_6
  · exact sharedDiskP469Value2_7
private theorem sharedDiskP469Value3_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 3 (0:Fin 8))=sharedDiskP469Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value3_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 3 (1:Fin 8))=sharedDiskP469Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value3_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 3 (2:Fin 8))=sharedDiskP469Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value3_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 3 (3:Fin 8))=sharedDiskP469Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value3_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 3 (4:Fin 8))=sharedDiskP469Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value3_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 3 (5:Fin 8))=sharedDiskP469Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value3_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 3 (6:Fin 8))=sharedDiskP469Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value3_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 3 (7:Fin 8))=sharedDiskP469Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 3 j)=sharedDiskP469Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value3_0
  · exact sharedDiskP469Value3_1
  · exact sharedDiskP469Value3_2
  · exact sharedDiskP469Value3_3
  · exact sharedDiskP469Value3_4
  · exact sharedDiskP469Value3_5
  · exact sharedDiskP469Value3_6
  · exact sharedDiskP469Value3_7
private theorem sharedDiskP469Value4_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 4 (0:Fin 8))=sharedDiskP469Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value4_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 4 (1:Fin 8))=sharedDiskP469Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value4_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 4 (2:Fin 8))=sharedDiskP469Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value4_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 4 (3:Fin 8))=sharedDiskP469Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value4_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 4 (4:Fin 8))=sharedDiskP469Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value4_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 4 (5:Fin 8))=sharedDiskP469Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value4_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 4 (6:Fin 8))=sharedDiskP469Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value4_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 4 (7:Fin 8))=sharedDiskP469Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 4 j)=sharedDiskP469Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value4_0
  · exact sharedDiskP469Value4_1
  · exact sharedDiskP469Value4_2
  · exact sharedDiskP469Value4_3
  · exact sharedDiskP469Value4_4
  · exact sharedDiskP469Value4_5
  · exact sharedDiskP469Value4_6
  · exact sharedDiskP469Value4_7
private theorem sharedDiskP469Value5_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 5 (0:Fin 8))=sharedDiskP469Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value5_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 5 (1:Fin 8))=sharedDiskP469Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value5_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 5 (2:Fin 8))=sharedDiskP469Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value5_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 5 (3:Fin 8))=sharedDiskP469Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value5_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 5 (4:Fin 8))=sharedDiskP469Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value5_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 5 (5:Fin 8))=sharedDiskP469Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value5_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 5 (6:Fin 8))=sharedDiskP469Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value5_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 5 (7:Fin 8))=sharedDiskP469Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 5 j)=sharedDiskP469Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value5_0
  · exact sharedDiskP469Value5_1
  · exact sharedDiskP469Value5_2
  · exact sharedDiskP469Value5_3
  · exact sharedDiskP469Value5_4
  · exact sharedDiskP469Value5_5
  · exact sharedDiskP469Value5_6
  · exact sharedDiskP469Value5_7
private theorem sharedDiskP469Value6_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 6 (0:Fin 8))=sharedDiskP469Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value6_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 6 (1:Fin 8))=sharedDiskP469Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value6_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 6 (2:Fin 8))=sharedDiskP469Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value6_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 6 (3:Fin 8))=sharedDiskP469Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value6_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 6 (4:Fin 8))=sharedDiskP469Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value6_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 6 (5:Fin 8))=sharedDiskP469Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value6_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 6 (6:Fin 8))=sharedDiskP469Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value6_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 6 (7:Fin 8))=sharedDiskP469Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 6 j)=sharedDiskP469Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value6_0
  · exact sharedDiskP469Value6_1
  · exact sharedDiskP469Value6_2
  · exact sharedDiskP469Value6_3
  · exact sharedDiskP469Value6_4
  · exact sharedDiskP469Value6_5
  · exact sharedDiskP469Value6_6
  · exact sharedDiskP469Value6_7
private theorem sharedDiskP469Value7_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 7 (0:Fin 8))=sharedDiskP469Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value7_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 7 (1:Fin 8))=sharedDiskP469Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value7_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 7 (2:Fin 8))=sharedDiskP469Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value7_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 7 (3:Fin 8))=sharedDiskP469Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value7_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 7 (4:Fin 8))=sharedDiskP469Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value7_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 7 (5:Fin 8))=sharedDiskP469Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value7_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 7 (6:Fin 8))=sharedDiskP469Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value7_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 7 (7:Fin 8))=sharedDiskP469Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 7 j)=sharedDiskP469Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value7_0
  · exact sharedDiskP469Value7_1
  · exact sharedDiskP469Value7_2
  · exact sharedDiskP469Value7_3
  · exact sharedDiskP469Value7_4
  · exact sharedDiskP469Value7_5
  · exact sharedDiskP469Value7_6
  · exact sharedDiskP469Value7_7
private theorem sharedDiskP469Value8_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 8 (0:Fin 8))=sharedDiskP469Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value8_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 8 (1:Fin 8))=sharedDiskP469Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value8_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 8 (2:Fin 8))=sharedDiskP469Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value8_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 8 (3:Fin 8))=sharedDiskP469Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value8_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 8 (4:Fin 8))=sharedDiskP469Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value8_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 8 (5:Fin 8))=sharedDiskP469Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value8_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 8 (6:Fin 8))=sharedDiskP469Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value8_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 8 (7:Fin 8))=sharedDiskP469Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 8 j)=sharedDiskP469Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value8_0
  · exact sharedDiskP469Value8_1
  · exact sharedDiskP469Value8_2
  · exact sharedDiskP469Value8_3
  · exact sharedDiskP469Value8_4
  · exact sharedDiskP469Value8_5
  · exact sharedDiskP469Value8_6
  · exact sharedDiskP469Value8_7
private theorem sharedDiskP469Value9_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 9 (0:Fin 8))=sharedDiskP469Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value9_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 9 (1:Fin 8))=sharedDiskP469Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value9_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 9 (2:Fin 8))=sharedDiskP469Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value9_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 9 (3:Fin 8))=sharedDiskP469Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value9_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 9 (4:Fin 8))=sharedDiskP469Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value9_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 9 (5:Fin 8))=sharedDiskP469Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value9_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 9 (6:Fin 8))=sharedDiskP469Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value9_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 9 (7:Fin 8))=sharedDiskP469Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 9 j)=sharedDiskP469Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value9_0
  · exact sharedDiskP469Value9_1
  · exact sharedDiskP469Value9_2
  · exact sharedDiskP469Value9_3
  · exact sharedDiskP469Value9_4
  · exact sharedDiskP469Value9_5
  · exact sharedDiskP469Value9_6
  · exact sharedDiskP469Value9_7
private theorem sharedDiskP469Value10_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 10 (0:Fin 8))=sharedDiskP469Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value10_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 10 (1:Fin 8))=sharedDiskP469Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value10_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 10 (2:Fin 8))=sharedDiskP469Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value10_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 10 (3:Fin 8))=sharedDiskP469Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value10_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 10 (4:Fin 8))=sharedDiskP469Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value10_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 10 (5:Fin 8))=sharedDiskP469Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value10_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 10 (6:Fin 8))=sharedDiskP469Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value10_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 10 (7:Fin 8))=sharedDiskP469Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 10 j)=sharedDiskP469Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value10_0
  · exact sharedDiskP469Value10_1
  · exact sharedDiskP469Value10_2
  · exact sharedDiskP469Value10_3
  · exact sharedDiskP469Value10_4
  · exact sharedDiskP469Value10_5
  · exact sharedDiskP469Value10_6
  · exact sharedDiskP469Value10_7
private theorem sharedDiskP469Value11_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 11 (0:Fin 8))=sharedDiskP469Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value11_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 11 (1:Fin 8))=sharedDiskP469Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value11_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 11 (2:Fin 8))=sharedDiskP469Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value11_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 11 (3:Fin 8))=sharedDiskP469Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value11_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 11 (4:Fin 8))=sharedDiskP469Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value11_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 11 (5:Fin 8))=sharedDiskP469Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value11_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 11 (6:Fin 8))=sharedDiskP469Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value11_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 11 (7:Fin 8))=sharedDiskP469Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 11 j)=sharedDiskP469Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value11_0
  · exact sharedDiskP469Value11_1
  · exact sharedDiskP469Value11_2
  · exact sharedDiskP469Value11_3
  · exact sharedDiskP469Value11_4
  · exact sharedDiskP469Value11_5
  · exact sharedDiskP469Value11_6
  · exact sharedDiskP469Value11_7
private theorem sharedDiskP469Value12_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 12 (0:Fin 8))=sharedDiskP469Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value12_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 12 (1:Fin 8))=sharedDiskP469Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value12_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 12 (2:Fin 8))=sharedDiskP469Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value12_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 12 (3:Fin 8))=sharedDiskP469Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value12_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 12 (4:Fin 8))=sharedDiskP469Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value12_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 12 (5:Fin 8))=sharedDiskP469Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value12_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 12 (6:Fin 8))=sharedDiskP469Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value12_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 12 (7:Fin 8))=sharedDiskP469Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 12 j)=sharedDiskP469Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value12_0
  · exact sharedDiskP469Value12_1
  · exact sharedDiskP469Value12_2
  · exact sharedDiskP469Value12_3
  · exact sharedDiskP469Value12_4
  · exact sharedDiskP469Value12_5
  · exact sharedDiskP469Value12_6
  · exact sharedDiskP469Value12_7
private theorem sharedDiskP469Value13_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 13 (0:Fin 8))=sharedDiskP469Values 13 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value13_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 13 (1:Fin 8))=sharedDiskP469Values 13 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value13_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 13 (2:Fin 8))=sharedDiskP469Values 13 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value13_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 13 (3:Fin 8))=sharedDiskP469Values 13 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value13_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 13 (4:Fin 8))=sharedDiskP469Values 13 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value13_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 13 (5:Fin 8))=sharedDiskP469Values 13 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value13_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 13 (6:Fin 8))=sharedDiskP469Values 13 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value13_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 13 (7:Fin 8))=sharedDiskP469Values 13 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values13_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 13 j)=sharedDiskP469Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value13_0
  · exact sharedDiskP469Value13_1
  · exact sharedDiskP469Value13_2
  · exact sharedDiskP469Value13_3
  · exact sharedDiskP469Value13_4
  · exact sharedDiskP469Value13_5
  · exact sharedDiskP469Value13_6
  · exact sharedDiskP469Value13_7
private theorem sharedDiskP469Value14_0 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 14 (0:Fin 8))=sharedDiskP469Values 14 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value14_1 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 14 (1:Fin 8))=sharedDiskP469Values 14 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value14_2 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 14 (2:Fin 8))=sharedDiskP469Values 14 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value14_3 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 14 (3:Fin 8))=sharedDiskP469Values 14 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value14_4 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 14 (4:Fin 8))=sharedDiskP469Values 14 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value14_5 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 14 (5:Fin 8))=sharedDiskP469Values 14 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value14_6 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 14 (6:Fin 8))=sharedDiskP469Values 14 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP469Value14_7 : truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 14 (7:Fin 8))=sharedDiskP469Values 14 (7:Fin 8) := by decide +kernel
theorem sharedDiskP469Values14_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points 14 j)=sharedDiskP469Values 14 j := by
  intro j
  fin_cases j
  · exact sharedDiskP469Value14_0
  · exact sharedDiskP469Value14_1
  · exact sharedDiskP469Value14_2
  · exact sharedDiskP469Value14_3
  · exact sharedDiskP469Value14_4
  · exact sharedDiskP469Value14_5
  · exact sharedDiskP469Value14_6
  · exact sharedDiskP469Value14_7
theorem sharedDiskP469Values_eq : ∀ (i : Fin 15) (j : Fin 8), truncatedChordCell 1 sharedDiskP469Params (sharedChord469Gauss8Points i j)=sharedDiskP469Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP469Values0_eq
  · exact sharedDiskP469Values1_eq
  · exact sharedDiskP469Values2_eq
  · exact sharedDiskP469Values3_eq
  · exact sharedDiskP469Values4_eq
  · exact sharedDiskP469Values5_eq
  · exact sharedDiskP469Values6_eq
  · exact sharedDiskP469Values7_eq
  · exact sharedDiskP469Values8_eq
  · exact sharedDiskP469Values9_eq
  · exact sharedDiskP469Values10_eq
  · exact sharedDiskP469Values11_eq
  · exact sharedDiskP469Values12_eq
  · exact sharedDiskP469Values13_eq
  · exact sharedDiskP469Values14_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP469Box : HorizontalRectangle := ⟨(21/40),(109/200),(3408482035145/6597069766656),(3428211200309/6597069766656),(569242277127445678605696498281173/324518553658426726783156020576256),(997816337683582219131015825500487/162259276829213363391578010288128),(-2680319989271812006639207848318513/649037107316853453566312041152512),(1371525691641307774521119614281533/2596148429267413814265248164610048),true,[]⟩
noncomputable def sharedDiskP469Grid : CGrid := momentChordGrid sharedDiskP469Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984)
theorem sharedDiskP469Columns : containedInReported sharedDiskP469Grid.re sharedDiskP469Box.reLo sharedDiskP469Box.reHi=true ∧ containedInReported sharedDiskP469Grid.im sharedDiskP469Box.imLo sharedDiskP469Box.imHi=true := by
  rw [sharedDiskP469Grid,momentChordGrid_eq_tabulated sharedDiskP469Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984) sharedChord469Gauss8Points sharedChord469Gauss8Weights sharedDiskP469Values sharedChord469Gauss8Points_eq sharedChord469Gauss8Weights_eq sharedDiskP469Values_eq]
  decide +kernel
theorem sharedDiskP469Sound : sharedDiskP469Box.Sound := by
  intro t a tl tu al au
  change (((21/40):ℚ):ℝ)≤t at tl
  change t≤(((109/200):ℚ):ℝ) at tu
  change (((3408482035145/6597069766656):ℚ):ℝ)≤a at al
  change a≤(((3428211200309/6597069766656):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP469Params_ok] at ps
  have band := sharedChord469ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((21/40):ℚ)≤(21/40))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((109/200):ℚ)≤(63/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3408482035145/6597069766656):ℚ)≤(3408482035145/6597069766656))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3428211200309/6597069766656):ℚ)≤(885480886574489/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord469Bd (by decide +kernel) (by decide +kernel) sharedChord469M (by decide +kernel) (sharedChord469Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP469Columns.1 sharedDiskP469Columns.2
def sharedDiskP469Rows : List SignRow := [positive_469.toSignRow, positive_470.toSignRow, positive_471.toSignRow, positive_472.toSignRow]
theorem sharedDiskP469Rows_actual : ∀ r∈sharedDiskP469Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP469Rows.all (sharedDiskP469Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP469Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP473Params : ChordParams := ⟨⟨(-4426019336711592472624),(-3792772575279748596323),true⟩,⟨3239884019107943134179568,3349308739223974656749584,true⟩,⟨59550647613604593525083,65613042327800713524213,true⟩,⟨75717115958802061630111,82890316374389607103643,true⟩,⟨134933915751422924318088,145839811070886765687886,true⟩,⟨1200106071075922191450508,1201363998226367768015892,true⟩,⟨(-3462565423041484746761412),(-3366289657518417328585665),true⟩,⟨⟨1160307272663472688912784,1241751996539768828494233,true⟩,⟨(-46),46,true⟩⟩⟩
theorem sharedDiskP473Params_ok : chordParams (Grid.ofRats (109/200) (14/25)) (Grid.ofRats (3426383759135/6597069766656) (3445557210181/6597069766656))=sharedDiskP473Params := by decide +kernel
def sharedDiskP473Values (i : Fin 15) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-9291819123288752100470631),(-2775145313175427415329644),true⟩,⟨(-2802596736639041811394524),3255406295642696731817084,true⟩⟩
  | 0,1 => ⟨⟨(-8771011035734918647551829),(-2509600279364891010017281),true⟩,⟨(-2831756846133200622886781),3072969050249456106588885,true⟩⟩
  | 0,2 => ⟨⟨(-8360255976742617029333981),(-2296789586399524737844046),true⟩,⟨(-2846472610460246311122846),2896673140371198408556358,true⟩⟩
  | 0,3 => ⟨⟨(-8114187140353683112725173),(-2176696479421154697260048),true⟩,⟨(-2852003494237524230222035),2779499453235688265309563,true⟩⟩
  | 0,4 => ⟨⟨(-9849232746018728326911542),(-3099863508570236080161414),true⟩,⟨(-2757663531134112198884675),3388884821037731995002350,true⟩⟩
  | 0,5 => ⟨⟨(-10364134304097811339463976),(-3444583735512226366399401),true⟩,⟨(-2703382584405932688847617),3443921297605975549974870,true⟩⟩
  | 0,6 => ⟨⟨(-10766855296098179497903058),(-3747335860293099956052297),true⟩,⟨(-2652783057786719468461292),3433901563855242538020352,true⟩⟩
  | 0,7 => ⟨⟨(-11007066965236882304593381),(-3942597312359332585116973),true⟩,⟨(-2619532217450918276961602),3403375045879724027778318,true⟩⟩
  | 1,0 => ⟨⟨(-6362373363685939689279573),(-1447990219315868841220048),true⟩,⟨(-2831532070561320032825773),1775658993029445719521808,true⟩⟩
  | 1,1 => ⟨⟨(-5911840435696123519478915),(-1287409370936808132830966),true⟩,⟨(-2812603997268211280240576),1489391635248744320005182,true⟩⟩
  | 1,2 => ⟨⟨(-5569686100401450310434547),(-1170387497532696449791187),true⟩,⟨(-2795367200631325450480112),1269283902687348017553457,true⟩⟩
  | 1,3 => ⟨⟨(-5370065395734123961279455),(-1103582386520090854483891),true⟩,⟨(-2784365679537272007149373),1149307371465618470731226,true⟩⟩
  | 1,4 => ⟨⟨(-6867086822586238022247319),(-1638783662457546782912511),true⟩,⟨(-2846897064711381205200597),2087280761678225962426674,true⟩⟩
  | 1,5 => ⟨⟨(-7355331253997573988735314),(-1836754747906872311546747),true⟩,⟨(-2854975291542676319164644),2374479626316452787185544,true⟩⟩
  | 1,6 => ⟨⟨(-7752334246769669562488033),(-2009218764418812066682790),true⟩,⟨(-2855954624562970104169685),2593763955905095601131770,true⟩⟩
  | 1,7 => ⟨⟨(-7995410925318432156650921),(-2120568504881126233568131),true⟩,⟨(-2853835208727314982796848),2720191242591522115039946,true⟩⟩
  | 2,0 => ⟨⟨(-4040532268017193069741650),(-674554938687833859760616),true⟩,⟨(-2695763273410002681730912),422754263303688105680951,true⟩⟩
  | 2,1 => ⟨⟨(-3717909455123829499094210),(-571160166577670399343128),true⟩,⟨(-2670542887636081437677115),250197287336172908046759,true⟩⟩
  | 2,2 => ⟨⟨(-3476429968665269027145236),(-492882067103894223053723),true⟩,⟨(-2650714630229804411764261),123331608217467254109682,true⟩⟩
  | 2,3 => ⟨⟨(-3336524110778153059727285),(-447010479261644564284165),true⟩,⟨(-2638830790657246715424267),50941475956611190308591,true⟩⟩
  | 2,4 => ⟨⟨(-4409821077320033392942759),(-792272014606918117120124),true⟩,⟨(-2722908358646426851111121),623286270581019923668172,true⟩⟩
  | 2,5 => ⟨⟨(-4776734997639492577713241),(-909726591613383868325473),true⟩,⟨(-2748024336424540675326453),824268881598972701804296,true⟩⟩
  | 2,6 => ⟨⟨(-5083323680478929705136604),(-1009074779493219009307947),true⟩,⟨(-2767501675692274724554273),992497699123872626227965,true⟩⟩
  | 2,7 => ⟨⟨(-5275130666232503080666926),(-1072090061375337623702687),true⟩,⟨(-2778934336307843092337097),1097489589683913676626633,true⟩⟩
  | 3,0 => ⟨⟨(-2448144953808432479540440),(-129048843128203861234395),true⟩,⟨(-2551588507031598293028678),(-323499166081914744819570),true⟩⟩
  | 3,1 => ⟨⟨(-2234081069068043127887681),(-46144494018134669281424),true⟩,⟨(-2527392628855725087690667),(-402172581470988620581335),true⟩⟩
  | 3,2 => ⟨⟨(-2072778703534086289148178),18646669650207669241976,true⟩,⟨(-2508160111208733652846223),(-459083051569962386906786),true⟩⟩
  | 3,3 => ⟨⟨(-1978787469327217479420990),57968909068867983240600,true⟩,⟨(-2496508714213500844486785),(-491218705987405606473009),true⟩⟩
  | 3,4 => ⟨⟨(-2691863596800216720505121),(-220509828488910819124892),true⟩,⟨(-2577551307451919062094851),(-230064689943397609532222),true⟩⟩
  | 3,5 => ⟨⟨(-2933458269221284907736779),(-308565703150802911074663),true⟩,⟨(-2601876689715128570354319),(-133956301895918209039491),true⟩⟩
  | 3,6 => ⟨⟨(-3136462718397079540988245),(-380563902336600581059655),true⟩,⟨(-2621293437358654079763609),(-49502253212051696136017),true⟩⟩
  | 3,7 => ⟨⟨(-3270146527576944100490957),(-425084473068214522954352),true⟩,⟨(-2633085262512245483391583),16918432122311565574061,true⟩⟩
  | 4,0 => ⟨⟨(-42811176682441773721701),1162797453670547715326180,true⟩,⟨(-2131829530911812761674003),(-824302440218427310049028),true⟩⟩
  | 4,1 => ⟨⟨318653825715155508297451,1447132704338288806759206,true⟩,⟨(-2023373638761687875624570),(-808560395641624754798087),true⟩⟩
  | 4,2 => ⟨⟨551065884715272291710558,1657661225052122643267455,true⟩,⟨(-1948150603489066120478095),(-781905976876685599626171),true⟩⟩
  | 4,3 => ⟨⟨682452929335942439928600,1778588882943533552293414,true⟩,⟨(-1901309435838020292689538),(-761367524031938295651553),true⟩⟩
  | 4,4 => ⟨⟨(-516120773587099653958629),833273136544960758542771,true⟩,⟨(-2250700980042949613698790),(-809234240047945474258519),true⟩⟩
  | 4,5 => ⟨⟨(-1034095733862838268152611),500631679693564804428725,true⟩,⟨(-2355111587677150554924506),(-752130568565296762913133),true⟩⟩
  | 4,6 => ⟨⟨(-1525479954472185684933976),256834927301910097387757,true⟩,⟨(-2434851160253731237096488),(-634200851797178463284884),true⟩⟩
  | 4,7 => ⟨⟨(-1867945930202629969355671),105143308061029359895675,true⟩,⟨(-2482308794290994607115625),(-528079242711014562106133),true⟩⟩
  | 5,0 => ⟨⟨2057703917974171689406593,3081630468534794554343646,true⟩,⟨(-1222756647033129088600248),(-337612495175479428721127),true⟩⟩
  | 5,1 => ⟨⟨2305948332066461956582613,3312411219189849664316342,true⟩,⟨(-1058796317443269425793293),(-223809605983674864226040),true⟩⟩
  | 5,2 => ⟨⟨2468886652548301157410175,3459728144120780043183739,true⟩,⟨(-940970716837732908390255),(-142201204091143251877317),true⟩⟩
  | 5,3 => ⟨⟨2554280061684829158935571,3534895263194112015602065,true⟩,⟨(-875032129144717507061208),(-96865171917181811156021),true⟩⟩
  | 5,4 => ⟨⟨1730587726410146910287816,2771387645283745021689144,true⟩,⟨(-1416585186813496297294937),(-470270125645403371170751),true⟩⟩
  | 5,5 => ⟨⟨1359102537927709380346064,2416485994529521053977401,true⟩,⟨(-1611096686484464542756626),(-597693603978192995751776),true⟩⟩
  | 5,6 => ⟨⟨1011041227955598712294721,2085852752859845987590416,true⟩,⟨(-1770592732299832614677299),(-693546480257576188541326),true⟩⟩
  | 5,7 => ⟨⟨774256701891752860079410,1863797835495622154344167,true⟩,⟨(-1866735947341336081878726),(-744744562555088089086319),true⟩⟩
  | 6,0 => ⟨⟨3056650871770889405424151,3846155467842063794771858,true⟩,⟨(-282144883357230165041083),275841217857108814477619,true⟩⟩
  | 6,1 => ⟨⟨3050525672183285636279409,3784937769447162545905491,true⟩,⟨(-210515219902119813507718),303972770427100204076042,true⟩⟩
  | 6,2 => ⟨⟨3026498461986277737739601,3720713198786046657413151,true⟩,⟨(-175176308860466055263640),310262052101089219493068,true⟩⟩
  | 6,3 => ⟨⟨3007409692027547249971451,3679338816372213372955126,true⟩,⟨(-161995176702535601001176),308288077167310758978928,true⟩⟩
  | 6,4 => ⟨⟨3013266156758656225834518,3864570741826106138776350,true⟩,⟨(-399015353715982577467247),214100559355827348685850,true⟩⟩
  | 6,5 => ⟨⟨2901313583454022669534129,3809394981197195993629379,true⟩,⟨(-553805619544810597824321),118983820099930490426377,true⟩⟩
  | 6,6 => ⟨⟨2743639577632847321521587,3693524108676944617973988,true⟩,⟨(-714235994521746331020132),12127472023585172232174,true⟩⟩
  | 6,7 => ⟨⟨2610800392290548970474884,3583604064955582240523632,true⟩,⟨(-829425778880117597851821),(-65728411220096105323593),true⟩⟩
  | 7,0 => ⟨⟨2824473161533477974408821,3579503223038380544980617,true⟩,⟨(-301384796817507284045750),228774650089609053887173,true⟩⟩
  | 7,1 => ⟨⟨2831770009420240981713542,3651338898336676812079009,true⟩,⟨(-423338060756608401173251),163184785309357172001274,true⟩⟩
  | 7,2 => ⟨⟨2873442977731043980145037,3770501019087275010749516,true⟩,⟨(-571089196631026847866334),85849498299570905277690,true⟩⟩
  | 7,3 => ⟨⟨2918263453192251556761478,3879114946187090646199894,true⟩,⟨(-694166569002302512718593),22267911974118276014643,true⟩⟩
  | 7,4 => ⟨⟨2856583410343607678470216,3568130902768865929010754,true⟩,⟨(-220732095044921941960316),273824757752413408495215,true⟩⟩
  | 7,5 => ⟨⟨2910532066634762160253504,3596777628849277491444561,true⟩,⟨(-177799714863790412129468),298437221063688462239080,true⟩⟩
  | 7,6 => ⟨⟨2962108879825288660550833,3635425910562087601364959,true⟩,⟨(-161812224246431387220201),307145936364345373838625,true⟩⟩
  | 7,7 => ⟨⟨2994396738913083160567380,3662215760056966821553973,true⟩,⟨(-159412216002550751585237),307634201773694901269019,true⟩⟩
  | 8,0 => ⟨⟨3268826160507512418390194,4727118269482014662162026,true⟩,⟨(-1707742901636819739800040),(-482271574133425844293010),true⟩⟩
  | 8,1 => ⟨⟨3401262745727771099023080,5137011489746132771215147,true⟩,⟨(-2307923024254317579781580),(-779627577096434268476823),true⟩⟩
  | 8,2 => ⟨⟨3488057595396591440896670,5534194579081995158772816,true⟩,⟨(-2999810539364394053369712),(-1120607151571741155603659),true⟩⟩
  | 8,3 => ⟨⟨3513085784551384485072394,5802310549451883992819001,true⟩,⟨(-3552875482181498293872033),(-1391146932342409170269310),true⟩⟩
  | 8,4 => ⟨⟨3136863626217798354794900,4388736910792675795068286,true⟩,⟨(-1275985429588000012156625),(-267918014706863508862292),true⟩⟩
  | 8,5 => ⟨⟨3035427415018677794593996,4149497248620487037094620,true⟩,⟨(-996273747001943820201110),(-128928869883999939445170),true⟩⟩
  | 8,6 => ⟨⟨2971097898145038292838516,4001574753798196579030774,true⟩,⟨(-830273237225376359113428),(-46307643490502726516483),true⟩⟩
  | 8,7 => ⟨⟨2938832983922606256049665,3927140291516941002702535,true⟩,⟨(-747608039213330091640810),(-5068950071150955110249),true⟩⟩
  | 9,0 => ⟨⟨3395509948128728649203716,6375762542708732027365684,true⟩,⟨(-5159325265230292418137326),(-2163571522770980503454275),true⟩⟩
  | 9,1 => ⟨⟨3298154737399165191053318,6509145276120855600349642,true⟩,⟨(-5702650185950452576866209),(-2419584032147838063061879),true⟩⟩
  | 9,2 => ⟨⟨3189943590113976764362319,6603274292589741713010222,true⟩,⟨(-6180609820827329216872793),(-2642367369485748696984076),true⟩⟩
  | 9,3 => ⟨⟨3108603744952059327021666,6653023702244056759902502,true⟩,⟨(-6490733710155305937806996),(-2785646065170894073348046),true⟩⟩
  | 9,4 => ⟨⟨3461889930721247681962727,6222130404718652176541382,true⟩,⟨(-4643774601156809572756154),(-1918080781197087132256951),true⟩⟩
  | 9,5 => ⟨⟨3496772899170703801457645,6074542116812056084013523,true⟩,⟨(-4218725590160943343394573),(-1713919771965761992869618),true⟩⟩
  | 9,6 => ⟨⟨3510182986800371172912391,5957166112729489604190728,true⟩,⟨(-3915844904197412263510938),(-1567524403607835248259916),true⟩⟩
  | 9,7 => ⟨⟨3513367275115728196682748,5886805002525231345539192,true⟩,⟨(-3746283056319026643147887),(-1485252600805560107134243),true⟩⟩
  | 10,0 => ⟨⟨1928152190930128717746576,6691789390038420886624186,true⟩,⟨(-9367454334510945877850863),(-4060034334625128943990399),true⟩⟩
  | 10,1 => ⟨⟨1337477849247638997006848,6518416598017447680525404,true⟩,⟨(-10337062761860658953810680),(-4462967222037187513340151),true⟩⟩
  | 10,2 => ⟨⟨750483413305463123409914,6288316290806959412995937,true⟩,⟨(-11141149765363366989079082),(-4782434787047780405606563),true⟩⟩
  | 10,3 => ⟨⟨263970616794064903662640,6101740110726908708667673,true⟩,⟨(-11673391315299158294340302),(-4970384887739407894580753),true⟩⟩
  | 10,4 => ⟨⟨2413832946217051910951601,6765826076768937309195204,true⟩,⟨(-8400705205510304717753925),(-3643746780106619779508506),true⟩⟩
  | 10,5 => ⟨⟨2754318246838679947183124,6758228966418903227518148,true⟩,⟨(-7578484610827432820503061),(-3279734520957540134082241),true⟩⟩
  | 10,6 => ⟨⟨2961594398550443147937133,6713956968294087872973766,true⟩,⟨(-6983032636140812987323609),(-3010938865669559445441545),true⟩⟩
  | 10,7 => ⟨⟨3064207105055072347459582,6674804877605587977264169,true⟩,⟨(-6647378856507838990254576),(-2857623196730414609291132),true⟩⟩
  | 11,0 => ⟨⟨(-2213605952598707626289293),4962967049653129393729147,true⟩,⟨(-13696509527467736962893120),(-5591633687357517122815362),true⟩⟩
  | 11,1 => ⟨⟨(-3046543143034497716967103),4521292801714217116950516,true⟩,⟨(-14191960081047882529679740),(-5708749226507873560689967),true⟩⟩
  | 11,2 => ⟨⟨(-3754003376378055049546182),4126746751733011686364127,true⟩,⟨(-14551422396382046312817899),(-5778023559625914530256687),true⟩⟩
  | 11,3 => ⟨⟨(-4200160604500309807749668),3869265616533354140714751,true⟩,⟨(-14750349424597929165789985),(-5808145245881220971747497),true⟩⟩
  | 11,4 => ⟨⟨(-1396646492675315156990223),5369813719209035599501181,true⟩,⟨(-13128837258777513484950166),(-5436209854029049832953604),true⟩⟩
  | 11,5 => ⟨⟨(-706002600419732588854435),5690699170918554469176446,true⟩,⟨(-12578994922100864865449842),(-5269864458184078049900573),true⟩⟩
  | 11,6 => ⟨⟨(-206303764546207100991899),5907779253576784660913632,true⟩,⟨(-12136346490247258369789096),(-5126996432102349836152127),true⟩⟩
  | 11,7 => ⟨⟨73375689610103327111975,6023891550960005933854656,true⟩,⟨(-11868337078238596051876262),(-5037163801507478800378474),true⟩⟩
  | 12,0 => ⟨⟨(-7880002166447568287630507),1609342364517736173769161,true⟩,⟨(-15585726177912710311236127),(-5615761402626955598539185),true⟩⟩
  | 12,1 => ⟨⟨(-8956226771144256117237881),974825110493801013582615,true⟩,⟨(-15535608299163406091664641),(-5363097828596294931920375),true⟩⟩
  | 12,2 => ⟨⟨(-9794649935113061863945926),454272834046503737216984,true⟩,⟨(-15382989603054472035804859),(-5109504522380831408301393),true⟩⟩
  | 12,3 => ⟨⟨(-10287571787854502083329080),135425949525172591736219,true⟩,⟨(-15238873469537341063232979),(-4933437953007601778877507),true⟩⟩
  | 12,4 => ⟨⟨(-6730613362910117486618190),2287681041396368287535293,true⟩,⟨(-15482727289877290504947515),(-5788409654167889739116757),true⟩⟩
  | 12,5 => ⟨⟨(-5685867061972568801102201),2965513342016764133696518,true⟩,⟨(-15262082765758659426635640),(-5835591660320143121372013),true⟩⟩
  | 12,6 => ⟨⟨(-4887662574298141479989974),3459826113914455506032309,true⟩,⟨(-15015812442740372657203863),(-5834639313846238683034521),true⟩⟩
  | 12,7 => ⟨⟨(-4421666267020440703400247),3739012179811905558116449,true⟩,⟨(-14841287518126951228768048),(-5819297809003494486288383),true⟩⟩
  | 13,0 => ⟨⟨(-13538433183679315151212440),(-2113952555634495648258460),true⟩,⟨(-12836396552464116943585758),(-2802815302613353638879883),true⟩⟩
  | 13,1 => ⟨⟨(-14077415670318236847038152),(-2653914587846240445159138),true⟩,⟨(-11758649636190790171883565),(-2084918864783580235846721),true⟩⟩
  | 13,2 => ⟨⟨(-14343984898089905556654706),(-3033165780328596299058706),true⟩,⟨(-10801323368990240787145538),(-1507971498833772968854109),true⟩⟩
  | 13,3 => ⟨⟨(-14431303847388249482914339),(-3237921718637837768149776),true⟩,⟨(-10186990551913519752163039),(-1162076981812017082793832),true⟩⟩
  | 13,4 => ⟨⟨(-12740262476194530884098650),(-1475959755148007430928022),true⟩,⟨(-13804901093491677529458470),(-3535860411158053804350567),true⟩⟩
  | 13,5 => ⟨⟨(-11828820833952982230097679),(-844618664841328802797337),true⟩,⟨(-14518038057083730431365572),(-4164251422264505623586171),true⟩⟩
  | 13,6 => ⟨⟨(-11018572276037479911409780),(-331156304143627067299334),true⟩,⟨(-14949702473068286658257894),(-4614069520203746646740703),true⟩⟩
  | 13,7 => ⟨⟨(-10521959685746848544291582),(-19476672623134530468878),true⟩,⟨(-15154255907172206772893778),(-4841773509446988941421107),true⟩⟩
  | 14,0 => ⟨⟨(-13337403502135640353754313),(-4094397129648854821624439),true⟩,⟨(-5229442848619312360340792),1482034278965407551264223,true⟩⟩
  | 14,1 => ⟨⟨(-12533070891105845754901769),(-4116040279466738707622258),true⟩,⟨(-3906550078104466195931017),2216636096129713103104780,true⟩⟩
  | 14,2 => ⟨⟨(-11785079610269564692176010),(-4072882205809804593332462),true⟩,⟨(-2932627968422222380568487),2691867764490674620933080,true⟩⟩
  | 14,3 => ⟨⟨(-11303090719909166568975926),(-3972382460382811629741136),true⟩,⟨(-2384358858158561583979276),2931236671667656663470047,true⟩⟩
  | 14,4 => ⟨⟨(-13979141366759961689657127),(-3967597863329867292170597),true⟩,⟨(-6721931860362811302880958),644410615830155468418759,true⟩⟩
  | 14,5 => ⟨⟨(-14334433057886344327953346),(-3748184444700517967000143),true⟩,⟨(-8133452391233437295009423),(-114233357326930012194845),true⟩⟩
  | 14,6 => ⟨⟨(-14455514442225112098895487),(-3505295203894002703814612),true⟩,⟨(-9234547821297867793948680),(-658483904712669775598595),true⟩⟩
  | 14,7 => ⟨⟨(-14453173583461557809259390),(-3330260151100779111723494),true⟩,⟨(-9880454262136870011412835),(-995847800042176819597202),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP473Value0_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 0 (0:Fin 8))=sharedDiskP473Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value0_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 0 (1:Fin 8))=sharedDiskP473Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value0_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 0 (2:Fin 8))=sharedDiskP473Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value0_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 0 (3:Fin 8))=sharedDiskP473Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value0_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 0 (4:Fin 8))=sharedDiskP473Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value0_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 0 (5:Fin 8))=sharedDiskP473Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value0_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 0 (6:Fin 8))=sharedDiskP473Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value0_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 0 (7:Fin 8))=sharedDiskP473Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 0 j)=sharedDiskP473Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value0_0
  · exact sharedDiskP473Value0_1
  · exact sharedDiskP473Value0_2
  · exact sharedDiskP473Value0_3
  · exact sharedDiskP473Value0_4
  · exact sharedDiskP473Value0_5
  · exact sharedDiskP473Value0_6
  · exact sharedDiskP473Value0_7
private theorem sharedDiskP473Value1_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 1 (0:Fin 8))=sharedDiskP473Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value1_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 1 (1:Fin 8))=sharedDiskP473Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value1_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 1 (2:Fin 8))=sharedDiskP473Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value1_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 1 (3:Fin 8))=sharedDiskP473Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value1_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 1 (4:Fin 8))=sharedDiskP473Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value1_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 1 (5:Fin 8))=sharedDiskP473Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value1_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 1 (6:Fin 8))=sharedDiskP473Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value1_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 1 (7:Fin 8))=sharedDiskP473Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 1 j)=sharedDiskP473Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value1_0
  · exact sharedDiskP473Value1_1
  · exact sharedDiskP473Value1_2
  · exact sharedDiskP473Value1_3
  · exact sharedDiskP473Value1_4
  · exact sharedDiskP473Value1_5
  · exact sharedDiskP473Value1_6
  · exact sharedDiskP473Value1_7
private theorem sharedDiskP473Value2_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 2 (0:Fin 8))=sharedDiskP473Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value2_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 2 (1:Fin 8))=sharedDiskP473Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value2_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 2 (2:Fin 8))=sharedDiskP473Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value2_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 2 (3:Fin 8))=sharedDiskP473Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value2_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 2 (4:Fin 8))=sharedDiskP473Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value2_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 2 (5:Fin 8))=sharedDiskP473Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value2_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 2 (6:Fin 8))=sharedDiskP473Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value2_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 2 (7:Fin 8))=sharedDiskP473Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 2 j)=sharedDiskP473Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value2_0
  · exact sharedDiskP473Value2_1
  · exact sharedDiskP473Value2_2
  · exact sharedDiskP473Value2_3
  · exact sharedDiskP473Value2_4
  · exact sharedDiskP473Value2_5
  · exact sharedDiskP473Value2_6
  · exact sharedDiskP473Value2_7
private theorem sharedDiskP473Value3_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 3 (0:Fin 8))=sharedDiskP473Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value3_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 3 (1:Fin 8))=sharedDiskP473Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value3_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 3 (2:Fin 8))=sharedDiskP473Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value3_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 3 (3:Fin 8))=sharedDiskP473Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value3_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 3 (4:Fin 8))=sharedDiskP473Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value3_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 3 (5:Fin 8))=sharedDiskP473Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value3_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 3 (6:Fin 8))=sharedDiskP473Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value3_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 3 (7:Fin 8))=sharedDiskP473Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 3 j)=sharedDiskP473Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value3_0
  · exact sharedDiskP473Value3_1
  · exact sharedDiskP473Value3_2
  · exact sharedDiskP473Value3_3
  · exact sharedDiskP473Value3_4
  · exact sharedDiskP473Value3_5
  · exact sharedDiskP473Value3_6
  · exact sharedDiskP473Value3_7
private theorem sharedDiskP473Value4_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 4 (0:Fin 8))=sharedDiskP473Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value4_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 4 (1:Fin 8))=sharedDiskP473Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value4_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 4 (2:Fin 8))=sharedDiskP473Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value4_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 4 (3:Fin 8))=sharedDiskP473Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value4_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 4 (4:Fin 8))=sharedDiskP473Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value4_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 4 (5:Fin 8))=sharedDiskP473Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value4_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 4 (6:Fin 8))=sharedDiskP473Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value4_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 4 (7:Fin 8))=sharedDiskP473Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 4 j)=sharedDiskP473Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value4_0
  · exact sharedDiskP473Value4_1
  · exact sharedDiskP473Value4_2
  · exact sharedDiskP473Value4_3
  · exact sharedDiskP473Value4_4
  · exact sharedDiskP473Value4_5
  · exact sharedDiskP473Value4_6
  · exact sharedDiskP473Value4_7
private theorem sharedDiskP473Value5_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 5 (0:Fin 8))=sharedDiskP473Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value5_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 5 (1:Fin 8))=sharedDiskP473Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value5_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 5 (2:Fin 8))=sharedDiskP473Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value5_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 5 (3:Fin 8))=sharedDiskP473Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value5_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 5 (4:Fin 8))=sharedDiskP473Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value5_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 5 (5:Fin 8))=sharedDiskP473Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value5_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 5 (6:Fin 8))=sharedDiskP473Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value5_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 5 (7:Fin 8))=sharedDiskP473Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 5 j)=sharedDiskP473Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value5_0
  · exact sharedDiskP473Value5_1
  · exact sharedDiskP473Value5_2
  · exact sharedDiskP473Value5_3
  · exact sharedDiskP473Value5_4
  · exact sharedDiskP473Value5_5
  · exact sharedDiskP473Value5_6
  · exact sharedDiskP473Value5_7
private theorem sharedDiskP473Value6_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 6 (0:Fin 8))=sharedDiskP473Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value6_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 6 (1:Fin 8))=sharedDiskP473Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value6_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 6 (2:Fin 8))=sharedDiskP473Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value6_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 6 (3:Fin 8))=sharedDiskP473Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value6_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 6 (4:Fin 8))=sharedDiskP473Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value6_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 6 (5:Fin 8))=sharedDiskP473Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value6_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 6 (6:Fin 8))=sharedDiskP473Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value6_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 6 (7:Fin 8))=sharedDiskP473Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 6 j)=sharedDiskP473Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value6_0
  · exact sharedDiskP473Value6_1
  · exact sharedDiskP473Value6_2
  · exact sharedDiskP473Value6_3
  · exact sharedDiskP473Value6_4
  · exact sharedDiskP473Value6_5
  · exact sharedDiskP473Value6_6
  · exact sharedDiskP473Value6_7
private theorem sharedDiskP473Value7_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 7 (0:Fin 8))=sharedDiskP473Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value7_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 7 (1:Fin 8))=sharedDiskP473Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value7_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 7 (2:Fin 8))=sharedDiskP473Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value7_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 7 (3:Fin 8))=sharedDiskP473Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value7_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 7 (4:Fin 8))=sharedDiskP473Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value7_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 7 (5:Fin 8))=sharedDiskP473Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value7_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 7 (6:Fin 8))=sharedDiskP473Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value7_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 7 (7:Fin 8))=sharedDiskP473Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 7 j)=sharedDiskP473Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value7_0
  · exact sharedDiskP473Value7_1
  · exact sharedDiskP473Value7_2
  · exact sharedDiskP473Value7_3
  · exact sharedDiskP473Value7_4
  · exact sharedDiskP473Value7_5
  · exact sharedDiskP473Value7_6
  · exact sharedDiskP473Value7_7
private theorem sharedDiskP473Value8_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 8 (0:Fin 8))=sharedDiskP473Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value8_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 8 (1:Fin 8))=sharedDiskP473Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value8_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 8 (2:Fin 8))=sharedDiskP473Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value8_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 8 (3:Fin 8))=sharedDiskP473Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value8_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 8 (4:Fin 8))=sharedDiskP473Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value8_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 8 (5:Fin 8))=sharedDiskP473Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value8_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 8 (6:Fin 8))=sharedDiskP473Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value8_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 8 (7:Fin 8))=sharedDiskP473Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 8 j)=sharedDiskP473Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value8_0
  · exact sharedDiskP473Value8_1
  · exact sharedDiskP473Value8_2
  · exact sharedDiskP473Value8_3
  · exact sharedDiskP473Value8_4
  · exact sharedDiskP473Value8_5
  · exact sharedDiskP473Value8_6
  · exact sharedDiskP473Value8_7
private theorem sharedDiskP473Value9_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 9 (0:Fin 8))=sharedDiskP473Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value9_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 9 (1:Fin 8))=sharedDiskP473Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value9_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 9 (2:Fin 8))=sharedDiskP473Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value9_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 9 (3:Fin 8))=sharedDiskP473Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value9_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 9 (4:Fin 8))=sharedDiskP473Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value9_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 9 (5:Fin 8))=sharedDiskP473Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value9_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 9 (6:Fin 8))=sharedDiskP473Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value9_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 9 (7:Fin 8))=sharedDiskP473Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 9 j)=sharedDiskP473Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value9_0
  · exact sharedDiskP473Value9_1
  · exact sharedDiskP473Value9_2
  · exact sharedDiskP473Value9_3
  · exact sharedDiskP473Value9_4
  · exact sharedDiskP473Value9_5
  · exact sharedDiskP473Value9_6
  · exact sharedDiskP473Value9_7
private theorem sharedDiskP473Value10_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 10 (0:Fin 8))=sharedDiskP473Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value10_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 10 (1:Fin 8))=sharedDiskP473Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value10_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 10 (2:Fin 8))=sharedDiskP473Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value10_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 10 (3:Fin 8))=sharedDiskP473Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value10_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 10 (4:Fin 8))=sharedDiskP473Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value10_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 10 (5:Fin 8))=sharedDiskP473Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value10_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 10 (6:Fin 8))=sharedDiskP473Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value10_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 10 (7:Fin 8))=sharedDiskP473Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 10 j)=sharedDiskP473Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value10_0
  · exact sharedDiskP473Value10_1
  · exact sharedDiskP473Value10_2
  · exact sharedDiskP473Value10_3
  · exact sharedDiskP473Value10_4
  · exact sharedDiskP473Value10_5
  · exact sharedDiskP473Value10_6
  · exact sharedDiskP473Value10_7
private theorem sharedDiskP473Value11_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 11 (0:Fin 8))=sharedDiskP473Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value11_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 11 (1:Fin 8))=sharedDiskP473Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value11_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 11 (2:Fin 8))=sharedDiskP473Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value11_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 11 (3:Fin 8))=sharedDiskP473Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value11_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 11 (4:Fin 8))=sharedDiskP473Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value11_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 11 (5:Fin 8))=sharedDiskP473Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value11_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 11 (6:Fin 8))=sharedDiskP473Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value11_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 11 (7:Fin 8))=sharedDiskP473Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 11 j)=sharedDiskP473Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value11_0
  · exact sharedDiskP473Value11_1
  · exact sharedDiskP473Value11_2
  · exact sharedDiskP473Value11_3
  · exact sharedDiskP473Value11_4
  · exact sharedDiskP473Value11_5
  · exact sharedDiskP473Value11_6
  · exact sharedDiskP473Value11_7
private theorem sharedDiskP473Value12_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 12 (0:Fin 8))=sharedDiskP473Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value12_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 12 (1:Fin 8))=sharedDiskP473Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value12_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 12 (2:Fin 8))=sharedDiskP473Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value12_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 12 (3:Fin 8))=sharedDiskP473Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value12_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 12 (4:Fin 8))=sharedDiskP473Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value12_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 12 (5:Fin 8))=sharedDiskP473Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value12_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 12 (6:Fin 8))=sharedDiskP473Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value12_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 12 (7:Fin 8))=sharedDiskP473Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 12 j)=sharedDiskP473Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value12_0
  · exact sharedDiskP473Value12_1
  · exact sharedDiskP473Value12_2
  · exact sharedDiskP473Value12_3
  · exact sharedDiskP473Value12_4
  · exact sharedDiskP473Value12_5
  · exact sharedDiskP473Value12_6
  · exact sharedDiskP473Value12_7
private theorem sharedDiskP473Value13_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 13 (0:Fin 8))=sharedDiskP473Values 13 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value13_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 13 (1:Fin 8))=sharedDiskP473Values 13 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value13_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 13 (2:Fin 8))=sharedDiskP473Values 13 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value13_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 13 (3:Fin 8))=sharedDiskP473Values 13 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value13_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 13 (4:Fin 8))=sharedDiskP473Values 13 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value13_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 13 (5:Fin 8))=sharedDiskP473Values 13 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value13_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 13 (6:Fin 8))=sharedDiskP473Values 13 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value13_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 13 (7:Fin 8))=sharedDiskP473Values 13 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values13_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 13 j)=sharedDiskP473Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value13_0
  · exact sharedDiskP473Value13_1
  · exact sharedDiskP473Value13_2
  · exact sharedDiskP473Value13_3
  · exact sharedDiskP473Value13_4
  · exact sharedDiskP473Value13_5
  · exact sharedDiskP473Value13_6
  · exact sharedDiskP473Value13_7
private theorem sharedDiskP473Value14_0 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 14 (0:Fin 8))=sharedDiskP473Values 14 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value14_1 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 14 (1:Fin 8))=sharedDiskP473Values 14 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value14_2 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 14 (2:Fin 8))=sharedDiskP473Values 14 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value14_3 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 14 (3:Fin 8))=sharedDiskP473Values 14 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value14_4 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 14 (4:Fin 8))=sharedDiskP473Values 14 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value14_5 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 14 (5:Fin 8))=sharedDiskP473Values 14 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value14_6 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 14 (6:Fin 8))=sharedDiskP473Values 14 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP473Value14_7 : truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 14 (7:Fin 8))=sharedDiskP473Values 14 (7:Fin 8) := by decide +kernel
theorem sharedDiskP473Values14_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points 14 j)=sharedDiskP473Values 14 j := by
  intro j
  fin_cases j
  · exact sharedDiskP473Value14_0
  · exact sharedDiskP473Value14_1
  · exact sharedDiskP473Value14_2
  · exact sharedDiskP473Value14_3
  · exact sharedDiskP473Value14_4
  · exact sharedDiskP473Value14_5
  · exact sharedDiskP473Value14_6
  · exact sharedDiskP473Value14_7
theorem sharedDiskP473Values_eq : ∀ (i : Fin 15) (j : Fin 8), truncatedChordCell 1 sharedDiskP473Params (sharedChord469Gauss8Points i j)=sharedDiskP473Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP473Values0_eq
  · exact sharedDiskP473Values1_eq
  · exact sharedDiskP473Values2_eq
  · exact sharedDiskP473Values3_eq
  · exact sharedDiskP473Values4_eq
  · exact sharedDiskP473Values5_eq
  · exact sharedDiskP473Values6_eq
  · exact sharedDiskP473Values7_eq
  · exact sharedDiskP473Values8_eq
  · exact sharedDiskP473Values9_eq
  · exact sharedDiskP473Values10_eq
  · exact sharedDiskP473Values11_eq
  · exact sharedDiskP473Values12_eq
  · exact sharedDiskP473Values13_eq
  · exact sharedDiskP473Values14_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP473Box : HorizontalRectangle := ⟨(109/200),(14/25),(3426383759135/6597069766656),(3445557210181/6597069766656),(2249454328552555191970280717127715/1298074214633706907132624082305024),(118714465992187399048941828708103/20282409603651670423947251286016),(-2631257654288306085569704014514641/649037107316853453566312041152512),(776213964906804629519953917630653/2596148429267413814265248164610048),true,[]⟩
noncomputable def sharedDiskP473Grid : CGrid := momentChordGrid sharedDiskP473Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984)
theorem sharedDiskP473Columns : containedInReported sharedDiskP473Grid.re sharedDiskP473Box.reLo sharedDiskP473Box.reHi=true ∧ containedInReported sharedDiskP473Grid.im sharedDiskP473Box.imLo sharedDiskP473Box.imHi=true := by
  rw [sharedDiskP473Grid,momentChordGrid_eq_tabulated sharedDiskP473Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984) sharedChord469Gauss8Points sharedChord469Gauss8Weights sharedDiskP473Values sharedChord469Gauss8Points_eq sharedChord469Gauss8Weights_eq sharedDiskP473Values_eq]
  decide +kernel
theorem sharedDiskP473Sound : sharedDiskP473Box.Sound := by
  intro t a tl tu al au
  change (((109/200):ℚ):ℝ)≤t at tl
  change t≤(((14/25):ℚ):ℝ) at tu
  change (((3426383759135/6597069766656):ℚ):ℝ)≤a at al
  change a≤(((3445557210181/6597069766656):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP473Params_ok] at ps
  have band := sharedChord469ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((21/40):ℚ)≤(109/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((14/25):ℚ)≤(63/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3408482035145/6597069766656):ℚ)≤(3426383759135/6597069766656))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3445557210181/6597069766656):ℚ)≤(885480886574489/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord469Bd (by decide +kernel) (by decide +kernel) sharedChord469M (by decide +kernel) (sharedChord469Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP473Columns.1 sharedDiskP473Columns.2
def sharedDiskP473Rows : List SignRow := [positive_473.toSignRow, positive_474.toSignRow, positive_475.toSignRow]
theorem sharedDiskP473Rows_actual : ∀ r∈sharedDiskP473Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP473Rows.all (sharedDiskP473Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP473Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP476Params : ChordParams := ⟨⟨(-5123552747296108052766),(-4426019336711592472504),true⟩,⟨3140381920274374494150651,3248098052119305391872077,true⟩,⟨63735640460353219000794,70142040912228811484149,true⟩,⟨82329028036362969205544,90001330311296817929245,true⟩,⟨145679948767687213563435,156829706061940997655404,true⟩,⟨1198721959136840937086612,1200106071075922191450748,true⟩,⟨(-3366289657518417328597063),(-3274692261322664187715966),true⟩,⟨⟨1156833285446852224382056,1243496110215437003908297,true⟩,⟨(-46),46,true⟩⟩⟩
theorem sharedDiskP476Params_ok : chordParams (Grid.ofRats (14/25) (23/40)) (Grid.ofRats (1145855741371/2199023255552) (3460522300531/6597069766656))=sharedDiskP476Params := by decide +kernel
def sharedDiskP476Values (i : Fin 15) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-9159157561240908560176762),(-2746413433603616293294680),true⟩,⟨(-2744971024785242098632169),3192640755628642890862442,true⟩⟩
  | 0,1 => ⟨⟨(-8683034157934982623196907),(-2499438652455364693679371),true⟩,⟨(-2771366791501224334186841),3037842716661309486687971,true⟩⟩
  | 0,2 => ⟨⟨(-8306998922056821796420836),(-2304396182069133353503426),true⟩,⟨(-2785101555967836775677738),2886646648023088386744437,true⟩⟩
  | 0,3 => ⟨⟨(-8081390575306277172346019),(-2191558002030405152269114),true⟩,⟨(-2790480051383904222486896),2785393372089346325697764,true⟩⟩
  | 0,4 => ⟨⟨(-9668455026362511819244607),(-3047843997272063865898420),true⟩,⟨(-2705133291566867899424577),3304269693827674799842521,true⟩⟩
  | 0,5 => ⟨⟨(-10139107179542995637161421),(-3365172130583071524664286),true⟩,⟨(-2657618843908896447792285),3348801547126129696662272,true⟩⟩
  | 0,6 => ⟨⟨(-10507582504541277694915636),(-3642136281843263476117995),true⟩,⟨(-2613607120297323375918444),3338581734463695412156838,true⟩⟩
  | 0,7 => ⟨⟨(-10727573142566008503367352),(-3820116717780578290709534),true⟩,⟨(-2584744928405693400884952),3311735283292814633655148,true⟩⟩
  | 1,0 => ⟨⟨(-6462660920424324113792015),(-1498607427475388227503614),true⟩,⟨(-2774772330568564880456277),1894667757643506591380933,true⟩⟩
  | 1,1 => ⟨⟨(-6041363930516192742072130),(-1344193928447362307646448),true⟩,⟨(-2757738470165608420175175),1632828520692663222247907,true⟩⟩
  | 1,2 => ⟨⟨(-5719687834254717517284803),(-1231432606405763772749380),true⟩,⟨(-2741884933688899072818142),1428965018859508931526509,true⟩⟩
  | 1,3 => ⟨⟨(-5531069993088245753936675),(-1167066074992414257861572),true⟩,⟨(-2731550201543191997383075),1308470621193239616722473,true⟩⟩
  | 1,4 => ⟨⟨(-6931861496993002019146178),(-1681378227563799874445272),true⟩,⟨(-2788110374608469413829610),2175647907741838311561020,true⟩⟩
  | 1,5 => ⟨⟨(-7383355052438071364240936),(-1870056603746569127370272),true⟩,⟨(-2794579843817808369534604),2431011054271057783313956,true⟩⟩
  | 1,6 => ⟨⟨(-7749023097021477975308225),(-2033559005932713334209328),true⟩,⟨(-2794705911755781546997227),2623714329798657585778935,true⟩⟩
  | 1,7 => ⟨⟨(-7972378489816689718122428),(-2138690813562374769952634),true⟩,⟨(-2792341007934767310881464),2733922057837516467541434,true⟩⟩
  | 2,0 => ⟨⟨(-4261143117218522561401510),(-754091456528995304277483),true⟩,⟨(-2646346199105304659606375),603771750212571080484046,true⟩⟩
  | 2,1 => ⟨⟨(-3949066436091323872200013),(-655156065043236928680646),true⟩,⟨(-2621651934475493019077138),435672303954479118241542,true⟩⟩
  | 2,2 => ⟨⟨(-3714478922908540923100314),(-580512418774799887611162),true⟩,⟨(-2602182344807962882378584),310736895761946238603994,true⟩⟩
  | 2,3 => ⟨⟨(-3578187866225862038321326),(-536883364438392467086973),true⟩,⟨(-2590507385320919621569967),238906238341487790257020,true⟩⟩
  | 2,4 => ⟨⟨(-4616429621571962916849808),(-867127052344155522324558),true⟩,⟨(-2672754867794230748473986),796643386367530940390502,true⟩⟩
  | 2,5 => ⟨⟨(-4967375807563835045316340),(-980215249724341643115845),true⟩,⟨(-2696950160165281837275251),987443658372479479501083,true⟩⟩
  | 2,6 => ⟨⟨(-5259071445110579788572151),(-1076010065547131831364368),true⟩,⟨(-2715502874007639887926137),1145326457482017505437121,true⟩⟩
  | 2,7 => ⟨⟨(-5441049422344075943209976),(-1136749497847086450202592),true⟩,⟨(-2726363968924868581380516),1250815972043222474368191,true⟩⟩
  | 3,0 => ⟨⟨(-2690026633342385649688940),(-236858671970434626036430),true⟩,⟨(-2505384979109450778987069),(-180913011501941270600694),true⟩⟩
  | 3,1 => ⟨⟨(-2479923989405375705727085),(-159279989131180970558988),true⟩,⟨(-2482135240516060542111077),(-262226580877906990213624),true⟩⟩
  | 3,2 => ⟨⟨(-2321422348903240492346171),(-99293914525676430240546),true⟩,⟨(-2463797969899423952739802),(-321647092850930306730996),true⟩⟩
  | 3,3 => ⟨⟨(-2229006912721685601404336),(-63673967358175590068246),true⟩,⟨(-2452751758355931179975312),(-355447670852026138061926),true⟩⟩
  | 3,4 => ⟨⟨(-2928801584775651408654945),(-322738598820048057335893),true⟩,⟨(-2530538674196755723659953),(-85448800951775261052209),true⟩⟩
  | 3,5 => ⟨⟨(-3174537896027817751931872),(-405736635141134308759522),true⟩,⟨(-2554267374683732520211188),30426566540210104079764,true⟩⟩
  | 3,6 => ⟨⟨(-3382834378764273849584851),(-473839151637390233898638),true⟩,⟨(-2573289521606536401549268),137130195157969879399748,true⟩⟩
  | 3,7 => ⟨⟨(-3513431350785097441461512),(-516059731394492337683768),true⟩,⟨(-2584864158424104025056917),205004463639149500217401,true⟩⟩
  | 4,0 => ⟨⟨(-317040706341035055528248),933804668334567243177902,true⟩,⟨(-2119405301065259686093593),(-778514081075915583761019),true⟩⟩
  | 4,1 => ⟨⟨54453648046676012650401,1198847384321036371475339,true⟩,⟨(-2015915120850819413722584),(-778947303249254637302932),true⟩⟩
  | 4,2 => ⟨⟨301742988007767481927284,1395712237920272264343429,true⟩,⟨(-1937456241895949595012202),(-763925248234820335571223),true⟩⟩
  | 4,3 => ⟨⟨428174655341949451299230,1509114938843129256056475,true⟩,⟨(-1896288091346186028395537),(-749878146804512682746813),true⟩⟩
  | 4,4 => ⟨⟨(-778924618181851972368531),627267353785906811266860,true⟩,⟨(-2225696898588558619399162),(-744570575452242800350074),true⟩⟩
  | 4,5 => ⟨⟨(-1289754727571662567231583),341304041700011032754651,true⟩,⟨(-2320232252529656565947209),(-654077472367363768927783),true⟩⟩
  | 4,6 => ⟨⟨(-1783001735509162731044341),119151720455929637426773,true⟩,⟨(-2395048534049926090371060),(-508461507006916799510019),true⟩⟩
  | 4,7 => ⟨⟨(-2119983617510252658858242),(-20994455001901121893783),true⟩,⟨(-2439352831339931206218966),(-394459281435123120784880),true⟩⟩
  | 5,0 => ⟨⟨1764594510755001024067229,2760143297082376324446126,true⟩,⟨(-1273571460701023407323943),(-382600306940625531228290),true⟩⟩
  | 5,1 => ⟨⟨2013290427815272668085038,2992543969977216685635468,true⟩,⟨(-1117514415126607414286621),(-275228705560363788605220),true⟩⟩
  | 5,2 => ⟨⟨2179497835914665927835492,3144840564938296927395358,true⟩,⟨(-1004200544913795446269623),(-196812542554447769396550),true⟩⟩
  | 5,3 => ⟨⟨2267945151189342686627798,3224346274444601379050976,true⟩,⟨(-940358280654103106862282),(-152739588725876201172638),true⟩⟩
  | 5,4 => ⟨⟨1442281950663531675123876,2455180790769464198422643,true⟩,⟨(-1455542180260738734694348),(-504537632166359851027873),true⟩⟩
  | 5,5 => ⟨⟨1080792136785374629447092,2113028047372382830573019,true⟩,⟨(-1635158539068093601190747),(-617376838522282089082302),true⟩⟩
  | 5,6 => ⟨⟨744571730834876168600727,1798626675415292956598748,true⟩,⟨(-1779839806070720570584210),(-697777972400461426546393),true⟩⟩
  | 5,7 => ⟨⟨516526149166666672532820,1589189337529670025394248,true⟩,⟨(-1865700690561635712153053),(-737732095588253075416312),true⟩⟩
  | 6,0 => ⟨⟨2866687206135417326835446,3658527330638412023608194,true⟩,⟨(-350080705738054495497514),227911269567126692271216,true⟩⟩
  | 6,1 => ⟨⟨2894144648256685121919439,3638397254362101027525852,true⟩,⟨(-275985712392724047721753),261688394532289808858142,true⟩⟩
  | 6,2 => ⟨⟨2896356265711177451047064,3606051934663487501536754,true⟩,⟨(-239088273658596741817351),272033456686945281104140,true⟩⟩
  | 6,3 => ⟨⟨2892753702317045231798752,3583456456680756665485759,true⟩,⟨(-225313463525953088845141),272188721695098146948631,true⟩⟩
  | 6,4 => ⟨⟨2788105069443872774608196,3633280596060424912046322,true⟩,⟨(-469261810427773698003991),160301784030624567261080,true⟩⟩
  | 6,5 => ⟨⟨2646307761907117802718064,3540295815203971819518974,true⟩,⟨(-624641993210314449599617),61119698466386930218847,true⟩⟩
  | 6,6 => ⟨⟨2469091486564344782457221,3398956357519281686173748,true⟩,⟨(-783339852402320085991130),(-45527274984833350635799),true⟩⟩
  | 6,7 => ⟨⟨2327146730160283583702767,3276768207604632910417955,true⟩,⟨(-896018657962989133333375),(-122252302302029813456674),true⟩⟩
  | 7,0 => ⟨⟨2815912029766555142672092,3613885557011670614700199,true⟩,⟨(-381750590190533548710294),196404973285807660585708,true⟩⟩
  | 7,1 => ⟨⟨2848809331808303355194299,3723408207655976791288199,true⟩,⟨(-521779443393390744557103),124370217092353383724150,true⟩⟩
  | 7,2 => ⟨⟨2909367611202531708115758,3874667295895308162444818,true⟩,⟨(-692919499743979666008898),36982309633029538783335,true⟩⟩
  | 7,3 => ⟨⟨2964583872445878092239997,4004006091404903875416090,true⟩,⟨(-836080552861252017881025),(-34911054260634906261286),true⟩⟩
  | 7,4 => ⟨⟨2818726262933712943728032,3563765574399091849874546,true⟩,⟨(-290389412497822688863159),243543375916220293706469,true⟩⟩
  | 7,5 => ⟨⟨2843460557340197578058091,3556451848762718121289529,true⟩,⟨(-242571383191402974268610),267191317322854908298342,true⟩⟩
  | 7,6 => ⟨⟨2870444049416598969551329,3566143077556534245696877,true⟩,⟨(-225104292077010532083952),273740947449400236862388,true⟩⟩
  | 7,7 => ⟨⟨2887258580474442963577124,3575157061760428002504850,true⟩,⟨(-222584022243436881369573),272475918183060032490920,true⟩⟩
  | 8,0 => ⟨⟨3327616003334519995618883,4937586207521758757061644,true⟩,⟨(-2014821412826899847102732),(-619063679914283210362707),true⟩⟩
  | 8,1 => ⟨⟨3438241798829809045818902,5362189796758732446144013,true⟩,⟨(-2705525301898256044152826),(-960962571921982773851027),true⟩⟩
  | 8,2 => ⟨⟨3485648184115274995516101,5757085779643153768739441,true⟩,⟨(-3492376016544379654158749),(-1348003471109653277738928),true⟩⟩
  | 8,3 => ⟨⟨3471435854516131810582031,6012037584088086437183089,true⟩,⟨(-4113566907269559286406490),(-1650886980015107294686745),true⟩⟩
  | 8,4 => ⟨⟨3200802944605574083513271,4575260836363332295312201,true⟩,⟨(-1513949095819635687239687),(-370645752417306697389577),true⟩⟩
  | 8,5 => ⟨⟨3095658692094900161883824,4311969120810805958612433,true⟩,⟨(-1188197358337033255472644),(-209199846404966530319679),true⟩⟩
  | 8,6 => ⟨⟨3025322809968271712096855,4145289378056974858891708,true⟩,⟨(-994674234632560315699723),(-113391721231760291774880),true⟩⟩
  | 8,7 => ⟨⟨2988638245186995638888627,4059859632227520156155963,true⟩,⟨(-898330079531487261352917),(-65715516890120919225462),true⟩⟩
  | 9,0 => ⟨⟨3215030427776709237168506,6505198544853141832547591,true⟩,⟨(-5876544763002273428676529),(-2493807122630300855977795),true⟩⟩
  | 9,1 => ⟨⟨3065376267034374749353980,6600355411027874383553754,true⟩,⟨(-6458392773777498015837136),(-2765701635775915486735020),true⟩⟩
  | 9,2 => ⟨⟨2909850841339501815201328,6657133700225590590262840,true⟩,⟨(-6964016367030937244553845),(-2999124335208523381627949),true⟩⟩
  | 9,3 => ⟨⟨2797350369427355221997404,6680961407548286150784992,true⟩,⟨(-7288915024186668483819256),(-3147635658955676878863864),true⟩⟩
  | 9,4 => ⟨⟨3329018993836000390292917,6383144454339560684829686,true⟩,⟨(-5317613583155412524940682),(-2229522085023399929319619),true⟩⟩
  | 9,5 => ⟨⟨3401225709069070625965972,6257708725650580883419160,true⟩,⟨(-4851887735766023094763375),(-2007140164526665380649221),true⟩⟩
  | 9,6 => ⟨⟨3439927150856512414083829,6153732307049907445887166,true⟩,⟨(-4517353410570264578224723),(-1846260477093679772947550),true⟩⟩
  | 9,7 => ⟨⟨3456723500799386164690808,6089930846906658431609384,true⟩,⟨(-4329112493211025783253187),(-1755336332009441980831996),true⟩⟩
  | 10,0 => ⟨⟨1328173487640589999909028,6430338571771774475611914,true⟩,⟨(-10174846571446908979090189),(-4406641179622733804568822),true⟩⟩
  | 10,1 => ⟨⟨611749449129789498380780,6144952937413696799675813,true⟩,⟨(-11108837016978077901681378),(-4776899989390566826969404),true⟩⟩
  | 10,2 => ⟨⟨(-173998459213257168899326),5818992480901543479895373,true⟩,⟨(-11908869241269298190489735),(-5057586534790306510386756),true⟩⟩
  | 10,3 => ⟨⟨(-723694071736864804208779),5572884404709980450307426,true⟩,⟨(-12390129332985619457290096),(-5216007188069866146262361),true⟩⟩
  | 10,4 => ⟨⟨1908741673336049121390889,6609956060062769320897090,true⟩,⟨(-9232110070672881039843788),(-4008661680085531648814258),true⟩⟩
  | 10,5 => ⟨⟨2332443395777279806632724,6686080806074891231499642,true⟩,⟨(-8408116621808935262936166),(-3649624064944969983268599),true⟩⟩
  | 10,6 => ⟨⟨2600409075412095422533596,6698263262074895239541417,true⟩,⟨(-7799432031754093129035700),(-3378526106341702910133689),true⟩⟩
  | 10,7 => ⟨⟨2737114907324398318707169,6689178762971013038280551,true⟩,⟨(-7452059322892753721301283),(-3221754997941139073598080),true⟩⟩
  | 11,0 => ⟨⟨(-3331917105553304102060709),4215018593508095276600062,true⟩,⟨(-14098815304314226106404459),(-5678329039357241378961510),true⟩⟩
  | 11,1 => ⟨⟨(-4168415549839896525704127),3724787783678745946640103,true⟩,⟨(-14475184169121318857898783),(-5741270428869707031377753),true⟩⟩
  | 11,2 => ⟨⟨(-4865977468850932784858747),3297907884476840007705908,true⟩,⟨(-14730653524616305043279454),(-5765182332680397085438735),true⟩⟩
  | 11,3 => ⟨⟨(-5300073797139239180867640),3024122697976866165936995,true⟩,⟨(-14863095448921882598167099),(-5767178207574153323940166),true⟩⟩
  | 11,4 => ⟨⟨(-2494320780147936329449141),4681033379508699604344807,true⟩,⟨(-13642807762233197685614919),(-5576212712621606840765696),true⟩⟩
  | 11,5 => ⟨⟨(-1771791318045979618327142),5061419377560170913307672,true⟩,⟨(-13181878314378798893931208),(-5454463480611860922551955),true⟩⟩
  | 11,6 => ⟨⟨(-1239988751189566327846395),5327342497283602031777566,true⟩,⟨(-12799477819722946789571372),(-5343214647755479640058684),true⟩⟩
  | 11,7 => ⟨⟨(-936488250068919022410357),5473274370675755015516427,true⟩,⟨(-12563606607946860321548001),(-5270841475997595973707030),true⟩⟩
  | 12,0 => ⟨⟨(-8720179428252688724058570),911023984317215230471458,true⟩,⟨(-15150624923003027614360328),(-5284033896364276681231374),true⟩⟩
  | 12,1 => ⟨⟨(-9667528027437869502206535),306571434257468991311894,true⟩,⟨(-14950244959121984749510224),(-4985378531651664924590152),true⟩⟩
  | 12,2 => ⟨⟨(-10388101576058638307635280),(-174509541088449030466032),true⟩,⟨(-14687657572800334820099231),(-4703282951422115323849360),true⟩⟩
  | 12,3 => ⟨⟨(-10821230095604485399608068),(-459966068923463822030548),true⟩,⟨(-14483272301016442115489819),(-4496670113764289934922010),true⟩⟩
  | 12,4 => ⟨⟨(-7681879007245586875107525),1537577898759383858146752,true⟩,⟨(-15215569817747208029507727),(-5533556059603945227584644),true⟩⟩
  | 12,5 => ⟨⟨(-6714664478696138087992408),2092752874381489574817493,true⟩,⟨(-15151292308379838580528410),(-5702569474059275473179517),true⟩⟩
  | 12,6 => ⟨⟨(-5960486221885207698329296),2595635481113833634554275,true⟩,⟨(-15025301613196665962351507),(-5751282759937100337374523),true⟩⟩
  | 12,7 => ⟨⟨(-5513965123784937780239047),2886931798460990895882940,true⟩,⟨(-14920846510155940494387383),(-5764537208963356303944741),true⟩⟩
  | 13,0 => ⟨⟨(-13438391963900162343521083),(-2443491930903962931496169),true⟩,⟨(-11841809374272099610312878),(-2373540848929746220525824),true⟩⟩
  | 13,1 => ⟨⟨(-13804317768262088016695613),(-2898660040758150634715736),true⟩,⟨(-10783389952247030445384603),(-1711826239322588205082765),true⟩⟩
  | 13,2 => ⟨⟨(-13953051880890338061870279),(-3212674910189567113645222),true⟩,⟨(-9869775730088735769460667),(-1188855671044085618994562),true⟩⟩
  | 13,3 => ⟨⟨(-13979818929255746972321145),(-3379959607961152771397245),true⟩,⟨(-9293173616909195571577467),(-878420123073778725326895),true⟩⟩
  | 13,4 => ⟨⟨(-12844123100975923582249379),(-1894586935889802003460956),true⟩,⟨(-12834659464919803095569701),(-3065242478752814567790299),true⟩⟩
  | 13,5 => ⟨⟨(-12127656093508590924809971),(-1340014643450470080278282),true⟩,⟨(-13609997948822681915939873),(-3675167079576532402254273),true⟩⟩
  | 13,6 => ⟨⟨(-11467963691575559795946905),(-880590225344958568137464),true⟩,⟨(-14114771433275012722121302),(-4124578655888873322554004),true⟩⟩
  | 13,7 => ⟨⟨(-11037593602582677638554831),(-598011745729893716684384),true⟩,⟨(-14371580826882136277897578),(-4378507437971752929304653),true⟩⟩
  | 14,0 => ⟨⟨(-12744387167770435221575152),(-4043120208918191039756103),true⟩,⟨(-4795514152821060082662536),1512265199154862272721900,true⟩⟩
  | 14,1 => ⟨⟨(-11996900764126472319019674),(-4044941790231373704874005),true⟩,⟨(-3617098860442987827334170),2155893083030679061976760,true⟩⟩
  | 14,2 => ⟨⟨(-11316735399305687383728983),(-3995703216685750325885338),true⟩,⟨(-2749028670557513972134061),2575751239258315408541898,true⟩⟩
  | 14,3 => ⟨⟨(-10883761154015246791140831),(-3898938515512689854102589),true⟩,⟨(-2258978398186890162399372),2789454710416505997308060,true⟩⟩
  | 14,4 => ⟨⟨(-13370493075142391488064175),(-3954933835816251491035424),true⟩,⟨(-6130479328082217949663742),749235632805649477669606,true⟩⟩
  | 14,5 => ⟨⟨(-13759447848492330927330567),(-3787468623535324268632193),true⟩,⟨(-7404800469283812801878530),82708325201448926003864,true⟩⟩
  | 14,6 => ⟨⟨(-13930991470789147735038281),(-3595494212533484248578472),true⟩,⟨(-8410878641815541020172717),(-429902686234377079121421),true⟩⟩
  | 14,7 => ⟨⟨(-13975510052364641605181162),(-3454803931875641963590287),true⟩,⟨(-9007799954938802882603700),(-729950607005100230545791),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP476Value0_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 0 (0:Fin 8))=sharedDiskP476Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value0_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 0 (1:Fin 8))=sharedDiskP476Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value0_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 0 (2:Fin 8))=sharedDiskP476Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value0_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 0 (3:Fin 8))=sharedDiskP476Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value0_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 0 (4:Fin 8))=sharedDiskP476Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value0_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 0 (5:Fin 8))=sharedDiskP476Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value0_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 0 (6:Fin 8))=sharedDiskP476Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value0_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 0 (7:Fin 8))=sharedDiskP476Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 0 j)=sharedDiskP476Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value0_0
  · exact sharedDiskP476Value0_1
  · exact sharedDiskP476Value0_2
  · exact sharedDiskP476Value0_3
  · exact sharedDiskP476Value0_4
  · exact sharedDiskP476Value0_5
  · exact sharedDiskP476Value0_6
  · exact sharedDiskP476Value0_7
private theorem sharedDiskP476Value1_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 1 (0:Fin 8))=sharedDiskP476Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value1_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 1 (1:Fin 8))=sharedDiskP476Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value1_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 1 (2:Fin 8))=sharedDiskP476Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value1_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 1 (3:Fin 8))=sharedDiskP476Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value1_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 1 (4:Fin 8))=sharedDiskP476Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value1_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 1 (5:Fin 8))=sharedDiskP476Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value1_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 1 (6:Fin 8))=sharedDiskP476Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value1_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 1 (7:Fin 8))=sharedDiskP476Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 1 j)=sharedDiskP476Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value1_0
  · exact sharedDiskP476Value1_1
  · exact sharedDiskP476Value1_2
  · exact sharedDiskP476Value1_3
  · exact sharedDiskP476Value1_4
  · exact sharedDiskP476Value1_5
  · exact sharedDiskP476Value1_6
  · exact sharedDiskP476Value1_7
private theorem sharedDiskP476Value2_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 2 (0:Fin 8))=sharedDiskP476Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value2_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 2 (1:Fin 8))=sharedDiskP476Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value2_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 2 (2:Fin 8))=sharedDiskP476Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value2_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 2 (3:Fin 8))=sharedDiskP476Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value2_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 2 (4:Fin 8))=sharedDiskP476Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value2_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 2 (5:Fin 8))=sharedDiskP476Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value2_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 2 (6:Fin 8))=sharedDiskP476Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value2_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 2 (7:Fin 8))=sharedDiskP476Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 2 j)=sharedDiskP476Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value2_0
  · exact sharedDiskP476Value2_1
  · exact sharedDiskP476Value2_2
  · exact sharedDiskP476Value2_3
  · exact sharedDiskP476Value2_4
  · exact sharedDiskP476Value2_5
  · exact sharedDiskP476Value2_6
  · exact sharedDiskP476Value2_7
private theorem sharedDiskP476Value3_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 3 (0:Fin 8))=sharedDiskP476Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value3_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 3 (1:Fin 8))=sharedDiskP476Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value3_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 3 (2:Fin 8))=sharedDiskP476Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value3_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 3 (3:Fin 8))=sharedDiskP476Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value3_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 3 (4:Fin 8))=sharedDiskP476Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value3_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 3 (5:Fin 8))=sharedDiskP476Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value3_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 3 (6:Fin 8))=sharedDiskP476Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value3_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 3 (7:Fin 8))=sharedDiskP476Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 3 j)=sharedDiskP476Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value3_0
  · exact sharedDiskP476Value3_1
  · exact sharedDiskP476Value3_2
  · exact sharedDiskP476Value3_3
  · exact sharedDiskP476Value3_4
  · exact sharedDiskP476Value3_5
  · exact sharedDiskP476Value3_6
  · exact sharedDiskP476Value3_7
private theorem sharedDiskP476Value4_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 4 (0:Fin 8))=sharedDiskP476Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value4_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 4 (1:Fin 8))=sharedDiskP476Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value4_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 4 (2:Fin 8))=sharedDiskP476Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value4_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 4 (3:Fin 8))=sharedDiskP476Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value4_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 4 (4:Fin 8))=sharedDiskP476Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value4_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 4 (5:Fin 8))=sharedDiskP476Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value4_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 4 (6:Fin 8))=sharedDiskP476Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value4_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 4 (7:Fin 8))=sharedDiskP476Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 4 j)=sharedDiskP476Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value4_0
  · exact sharedDiskP476Value4_1
  · exact sharedDiskP476Value4_2
  · exact sharedDiskP476Value4_3
  · exact sharedDiskP476Value4_4
  · exact sharedDiskP476Value4_5
  · exact sharedDiskP476Value4_6
  · exact sharedDiskP476Value4_7
private theorem sharedDiskP476Value5_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 5 (0:Fin 8))=sharedDiskP476Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value5_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 5 (1:Fin 8))=sharedDiskP476Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value5_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 5 (2:Fin 8))=sharedDiskP476Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value5_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 5 (3:Fin 8))=sharedDiskP476Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value5_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 5 (4:Fin 8))=sharedDiskP476Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value5_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 5 (5:Fin 8))=sharedDiskP476Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value5_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 5 (6:Fin 8))=sharedDiskP476Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value5_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 5 (7:Fin 8))=sharedDiskP476Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 5 j)=sharedDiskP476Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value5_0
  · exact sharedDiskP476Value5_1
  · exact sharedDiskP476Value5_2
  · exact sharedDiskP476Value5_3
  · exact sharedDiskP476Value5_4
  · exact sharedDiskP476Value5_5
  · exact sharedDiskP476Value5_6
  · exact sharedDiskP476Value5_7
private theorem sharedDiskP476Value6_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 6 (0:Fin 8))=sharedDiskP476Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value6_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 6 (1:Fin 8))=sharedDiskP476Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value6_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 6 (2:Fin 8))=sharedDiskP476Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value6_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 6 (3:Fin 8))=sharedDiskP476Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value6_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 6 (4:Fin 8))=sharedDiskP476Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value6_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 6 (5:Fin 8))=sharedDiskP476Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value6_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 6 (6:Fin 8))=sharedDiskP476Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value6_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 6 (7:Fin 8))=sharedDiskP476Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 6 j)=sharedDiskP476Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value6_0
  · exact sharedDiskP476Value6_1
  · exact sharedDiskP476Value6_2
  · exact sharedDiskP476Value6_3
  · exact sharedDiskP476Value6_4
  · exact sharedDiskP476Value6_5
  · exact sharedDiskP476Value6_6
  · exact sharedDiskP476Value6_7
private theorem sharedDiskP476Value7_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 7 (0:Fin 8))=sharedDiskP476Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value7_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 7 (1:Fin 8))=sharedDiskP476Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value7_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 7 (2:Fin 8))=sharedDiskP476Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value7_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 7 (3:Fin 8))=sharedDiskP476Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value7_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 7 (4:Fin 8))=sharedDiskP476Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value7_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 7 (5:Fin 8))=sharedDiskP476Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value7_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 7 (6:Fin 8))=sharedDiskP476Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value7_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 7 (7:Fin 8))=sharedDiskP476Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 7 j)=sharedDiskP476Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value7_0
  · exact sharedDiskP476Value7_1
  · exact sharedDiskP476Value7_2
  · exact sharedDiskP476Value7_3
  · exact sharedDiskP476Value7_4
  · exact sharedDiskP476Value7_5
  · exact sharedDiskP476Value7_6
  · exact sharedDiskP476Value7_7
private theorem sharedDiskP476Value8_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 8 (0:Fin 8))=sharedDiskP476Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value8_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 8 (1:Fin 8))=sharedDiskP476Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value8_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 8 (2:Fin 8))=sharedDiskP476Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value8_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 8 (3:Fin 8))=sharedDiskP476Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value8_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 8 (4:Fin 8))=sharedDiskP476Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value8_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 8 (5:Fin 8))=sharedDiskP476Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value8_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 8 (6:Fin 8))=sharedDiskP476Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value8_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 8 (7:Fin 8))=sharedDiskP476Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 8 j)=sharedDiskP476Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value8_0
  · exact sharedDiskP476Value8_1
  · exact sharedDiskP476Value8_2
  · exact sharedDiskP476Value8_3
  · exact sharedDiskP476Value8_4
  · exact sharedDiskP476Value8_5
  · exact sharedDiskP476Value8_6
  · exact sharedDiskP476Value8_7
private theorem sharedDiskP476Value9_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 9 (0:Fin 8))=sharedDiskP476Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value9_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 9 (1:Fin 8))=sharedDiskP476Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value9_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 9 (2:Fin 8))=sharedDiskP476Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value9_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 9 (3:Fin 8))=sharedDiskP476Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value9_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 9 (4:Fin 8))=sharedDiskP476Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value9_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 9 (5:Fin 8))=sharedDiskP476Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value9_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 9 (6:Fin 8))=sharedDiskP476Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value9_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 9 (7:Fin 8))=sharedDiskP476Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 9 j)=sharedDiskP476Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value9_0
  · exact sharedDiskP476Value9_1
  · exact sharedDiskP476Value9_2
  · exact sharedDiskP476Value9_3
  · exact sharedDiskP476Value9_4
  · exact sharedDiskP476Value9_5
  · exact sharedDiskP476Value9_6
  · exact sharedDiskP476Value9_7
private theorem sharedDiskP476Value10_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 10 (0:Fin 8))=sharedDiskP476Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value10_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 10 (1:Fin 8))=sharedDiskP476Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value10_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 10 (2:Fin 8))=sharedDiskP476Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value10_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 10 (3:Fin 8))=sharedDiskP476Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value10_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 10 (4:Fin 8))=sharedDiskP476Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value10_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 10 (5:Fin 8))=sharedDiskP476Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value10_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 10 (6:Fin 8))=sharedDiskP476Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value10_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 10 (7:Fin 8))=sharedDiskP476Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 10 j)=sharedDiskP476Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value10_0
  · exact sharedDiskP476Value10_1
  · exact sharedDiskP476Value10_2
  · exact sharedDiskP476Value10_3
  · exact sharedDiskP476Value10_4
  · exact sharedDiskP476Value10_5
  · exact sharedDiskP476Value10_6
  · exact sharedDiskP476Value10_7
private theorem sharedDiskP476Value11_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 11 (0:Fin 8))=sharedDiskP476Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value11_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 11 (1:Fin 8))=sharedDiskP476Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value11_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 11 (2:Fin 8))=sharedDiskP476Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value11_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 11 (3:Fin 8))=sharedDiskP476Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value11_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 11 (4:Fin 8))=sharedDiskP476Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value11_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 11 (5:Fin 8))=sharedDiskP476Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value11_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 11 (6:Fin 8))=sharedDiskP476Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value11_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 11 (7:Fin 8))=sharedDiskP476Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 11 j)=sharedDiskP476Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value11_0
  · exact sharedDiskP476Value11_1
  · exact sharedDiskP476Value11_2
  · exact sharedDiskP476Value11_3
  · exact sharedDiskP476Value11_4
  · exact sharedDiskP476Value11_5
  · exact sharedDiskP476Value11_6
  · exact sharedDiskP476Value11_7
private theorem sharedDiskP476Value12_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 12 (0:Fin 8))=sharedDiskP476Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value12_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 12 (1:Fin 8))=sharedDiskP476Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value12_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 12 (2:Fin 8))=sharedDiskP476Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value12_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 12 (3:Fin 8))=sharedDiskP476Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value12_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 12 (4:Fin 8))=sharedDiskP476Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value12_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 12 (5:Fin 8))=sharedDiskP476Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value12_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 12 (6:Fin 8))=sharedDiskP476Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value12_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 12 (7:Fin 8))=sharedDiskP476Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 12 j)=sharedDiskP476Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value12_0
  · exact sharedDiskP476Value12_1
  · exact sharedDiskP476Value12_2
  · exact sharedDiskP476Value12_3
  · exact sharedDiskP476Value12_4
  · exact sharedDiskP476Value12_5
  · exact sharedDiskP476Value12_6
  · exact sharedDiskP476Value12_7
private theorem sharedDiskP476Value13_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 13 (0:Fin 8))=sharedDiskP476Values 13 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value13_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 13 (1:Fin 8))=sharedDiskP476Values 13 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value13_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 13 (2:Fin 8))=sharedDiskP476Values 13 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value13_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 13 (3:Fin 8))=sharedDiskP476Values 13 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value13_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 13 (4:Fin 8))=sharedDiskP476Values 13 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value13_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 13 (5:Fin 8))=sharedDiskP476Values 13 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value13_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 13 (6:Fin 8))=sharedDiskP476Values 13 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value13_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 13 (7:Fin 8))=sharedDiskP476Values 13 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values13_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 13 j)=sharedDiskP476Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value13_0
  · exact sharedDiskP476Value13_1
  · exact sharedDiskP476Value13_2
  · exact sharedDiskP476Value13_3
  · exact sharedDiskP476Value13_4
  · exact sharedDiskP476Value13_5
  · exact sharedDiskP476Value13_6
  · exact sharedDiskP476Value13_7
private theorem sharedDiskP476Value14_0 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 14 (0:Fin 8))=sharedDiskP476Values 14 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value14_1 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 14 (1:Fin 8))=sharedDiskP476Values 14 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value14_2 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 14 (2:Fin 8))=sharedDiskP476Values 14 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value14_3 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 14 (3:Fin 8))=sharedDiskP476Values 14 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value14_4 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 14 (4:Fin 8))=sharedDiskP476Values 14 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value14_5 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 14 (5:Fin 8))=sharedDiskP476Values 14 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value14_6 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 14 (6:Fin 8))=sharedDiskP476Values 14 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP476Value14_7 : truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 14 (7:Fin 8))=sharedDiskP476Values 14 (7:Fin 8) := by decide +kernel
theorem sharedDiskP476Values14_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points 14 j)=sharedDiskP476Values 14 j := by
  intro j
  fin_cases j
  · exact sharedDiskP476Value14_0
  · exact sharedDiskP476Value14_1
  · exact sharedDiskP476Value14_2
  · exact sharedDiskP476Value14_3
  · exact sharedDiskP476Value14_4
  · exact sharedDiskP476Value14_5
  · exact sharedDiskP476Value14_6
  · exact sharedDiskP476Value14_7
theorem sharedDiskP476Values_eq : ∀ (i : Fin 15) (j : Fin 8), truncatedChordCell 1 sharedDiskP476Params (sharedChord469Gauss8Points i j)=sharedDiskP476Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP476Values0_eq
  · exact sharedDiskP476Values1_eq
  · exact sharedDiskP476Values2_eq
  · exact sharedDiskP476Values3_eq
  · exact sharedDiskP476Values4_eq
  · exact sharedDiskP476Values5_eq
  · exact sharedDiskP476Values6_eq
  · exact sharedDiskP476Values7_eq
  · exact sharedDiskP476Values8_eq
  · exact sharedDiskP476Values9_eq
  · exact sharedDiskP476Values10_eq
  · exact sharedDiskP476Values11_eq
  · exact sharedDiskP476Values12_eq
  · exact sharedDiskP476Values13_eq
  · exact sharedDiskP476Values14_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP476Box : HorizontalRectangle := ⟨(14/25),(23/40),(1145855741371/2199023255552),(3460522300531/6597069766656),(1993973510476551635687770649456799/1298074214633706907132624082305024),(3558582855825978959231837067522895/649037107316853453566312041152512),(-1335569848481745471240943246732409/324518553658426726783156020576256),(19049929829569414444107639853959/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP476Grid : CGrid := momentChordGrid sharedDiskP476Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984)
theorem sharedDiskP476Columns : containedInReported sharedDiskP476Grid.re sharedDiskP476Box.reLo sharedDiskP476Box.reHi=true ∧ containedInReported sharedDiskP476Grid.im sharedDiskP476Box.imLo sharedDiskP476Box.imHi=true := by
  rw [sharedDiskP476Grid,momentChordGrid_eq_tabulated sharedDiskP476Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984) sharedChord469Gauss8Points sharedChord469Gauss8Weights sharedDiskP476Values sharedChord469Gauss8Points_eq sharedChord469Gauss8Weights_eq sharedDiskP476Values_eq]
  decide +kernel
theorem sharedDiskP476Sound : sharedDiskP476Box.Sound := by
  intro t a tl tu al au
  change (((14/25):ℚ):ℝ)≤t at tl
  change t≤(((23/40):ℚ):ℝ) at tu
  change (((1145855741371/2199023255552):ℚ):ℝ)≤a at al
  change a≤(((3460522300531/6597069766656):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP476Params_ok] at ps
  have band := sharedChord469ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((21/40):ℚ)≤(14/25))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((23/40):ℚ)≤(63/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3408482035145/6597069766656):ℚ)≤(1145855741371/2199023255552))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3460522300531/6597069766656):ℚ)≤(885480886574489/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord469Bd (by decide +kernel) (by decide +kernel) sharedChord469M (by decide +kernel) (sharedChord469Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP476Columns.1 sharedDiskP476Columns.2
def sharedDiskP476Rows : List SignRow := [positive_476.toSignRow, positive_477.toSignRow, positive_478.toSignRow]
theorem sharedDiskP476Rows_actual : ∀ r∈sharedDiskP476Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP476Rows.all (sharedDiskP476Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP476Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP479Params : ChordParams := ⟨⟨(-5887045039874982984452),(-5123552747296108052630),true⟩,⟨3045118078183642228382089,3148100907192954146335013,true⟩,⟨67926089279174125061817,74484988350973855851837,true⟩,⟨89428502844509036795337,97380389906197666665971,true⟩,⟨156641090812429937381428,168012581900329882437506,true⟩,⟨1197208787375325067471768,1198721959136840937086884,true⟩,⟨(-3274692261322664187727143),(-3187408755280903418029572),true⟩,⟨⟨1154037517283605721098457,1243437910143048557154521,true⟩,⟨(-46),46,true⟩⟩⟩
theorem sharedDiskP479Params_ok : chordParams (Grid.ofRats (23/40) (59/100)) (Grid.ofRats (3452812738613/6597069766656) (3476328955951/6597069766656))=sharedDiskP479Params := by decide +kernel
def sharedDiskP479Values (i : Fin 15) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-8998094028888041071059036),(-2720281427745514834214948),true⟩,⟨(-2672750944715446843415014),3127472296464705023521822,true⟩⟩
  | 0,1 => ⟨⟨(-8562121634981247973515499),(-2488621967651200562833662),true⟩,⟨(-2696259541648161454242090),2994888755454777205763428,true⟩⟩
  | 0,2 => ⟨⟨(-8217404142368368972442418),(-2312053256312016397035269),true⟩,⟨(-2708752625968679600277332),2864375584848410726429400,true⟩⟩
  | 0,3 => ⟨⟨(-8010334047294581134249206),(-2205985777573071865849766),true⟩,⟨(-2713777444787649413683774),2776462703465922404978944,true⟩⟩
  | 0,4 => ⟨⟨(-9464200611936053612467347),(-3000769535609882387896890),true⟩,⟨(-2637788138778552882471013),3222201421935621552940360,true⟩⟩
  | 0,5 => ⟨⟨(-9895038549908798133669698),(-3293875890427781852219032),true⟩,⟨(-2596460886402487760175438),3259369009166146641059697,true⟩⟩
  | 0,6 => ⟨⟨(-10232568101982781685637883),(-3548295599385854727640448),true⟩,⟨(-2558340979511587078790668),3250076478115522262921430,true⟩⟩
  | 0,7 => ⟨⟨(-10434213645988591248887352),(-3711259158760647130257085),true⟩,⟨(-2533369475350843164005936),3226927993231334771153406,true⟩⟩
  | 1,0 => ⟨⟨(-6515154607194020427914547),(-1547550623319011844191970),true⟩,⟨(-2701475998285744705996920),1986095694074824387718472,true⟩⟩
  | 1,1 => ⟨⟨(-6122172560119922247277687),(-1399250857930606856287234),true⟩,⟨(-2686251420308243779118305),1747764034381296639353577,true⟩⟩
  | 1,2 => ⟨⟨(-5820749737491048474202849),(-1290688855394771086517534),true⟩,⟨(-2671830641858787485649573),1560183226282481670531668,true⟩⟩
  | 1,3 => ⟨⟨(-5643416263352466128511760),(-1228646610316835865482232),true⟩,⟨(-2662330761950483447256316),1448447930862285380824397,true⟩⟩
  | 1,4 => ⟨⟨(-6950686871083431509387993),(-1722402382304650019905534),true⟩,⟨(-2713059620927001772152168),2238744113643678840703468,true⟩⟩
  | 1,5 => ⟨⟨(-7367963091528272488109569),(-1902028912148466643607309),true⟩,⟨(-2718312688579015602237777),2465673340821813165986198,true⟩⟩
  | 1,6 => ⟨⟨(-7704830772745209513432393),(-2056939577054172314785453),true⟩,⟨(-2717950143765686947775966),2635265715061540779722703,true⟩⟩
  | 1,7 => ⟨⟨(-7910196551352549606254504),(-2156183985070941505221103),true⟩,⟨(-2715562819570718612313660),2731620537925812020402486,true⟩⟩
  | 2,0 => ⟨⟨(-4436422942539443933392129),(-830664288672708712631856),true⟩,⟨(-2581682518013874533830445),761735961265440897140038,true⟩⟩
  | 2,1 => ⟨⟨(-4136434322341709055872163),(-735637679047889455680742),true⟩,⟨(-2557917744079258006279519),599840815707074260024360,true⟩⟩
  | 2,2 => ⟨⟨(-3910005246317441263962832),(-664130684092893940268741),true⟩,⟨(-2539105796234522757065040),478330965599798781415880,true⟩⟩
  | 2,3 => ⟨⟨(-3778094127166988142561646),(-622421157057960134170692),true⟩,⟨(-2527806087023290078240983),407988230234260721055289,true⟩⟩
  | 2,4 => ⟨⟨(-4776222708138865177569936),(-939497967779578718737915),true⟩,⟨(-2606920536627294341959515),945365111024502761461726,true⟩⟩
  | 2,5 => ⟨⟨(-5110090836115508258617296),(-1048553770747627109577732),true⟩,⟨(-2629826268980269618275876),1124917219176037513563034,true⟩⟩
  | 2,6 => ⟨⟨(-5386609645591354298604955),(-1140894922173235772411807),true⟩,⟨(-2647340638991694210491928),1285426245806858284104060,true⟩⟩
  | 2,7 => ⟨⟨(-5558620905886010208137178),(-1199411824515923829769045),true⟩,⟨(-2657537886602001031822249),1394750656960450884814894,true⟩⟩
  | 3,0 => ⟨⟨(-2897171833334754249316137),(-337566857207476716428310),true⟩,⟨(-2445573988530211784109223),(-45413877323127492012427),true⟩⟩
  | 3,1 => ⟨⟨(-2690124304228551752766287),(-264482614527552250303810),true⟩,⟨(-2423324831710145727257915),(-131523232770250534072268),true⟩⟩
  | 3,2 => ⟨⟨(-2535027043258601977296952),(-208120647522298687443242),true⟩,⟨(-2405880176159626758509489),(-192600952100281917877172),true⟩⟩
  | 3,3 => ⟨⟨(-2444513184183159066211924),(-174710128460576580750667),true⟩,⟨(-2395419675323670566898499),(-227567859848477430652581),true⟩⟩
  | 3,4 => ⟨⟨(-3142900719287999128830573),(-418740880118077738999436),true⟩,⟨(-2469782678397469113150223),76744815391723157243085,true⟩⟩
  | 3,5 => ⟨⟨(-3385919309983622246875662),(-497469432352072267728605),true⟩,⟨(-2492713063548548047091021),201700223218374999419486,true⟩⟩
  | 3,6 => ⟨⟨(-3588568071077265987636368),(-562272747245831559500228),true⟩,⟨(-2511130636805364921434669),307689509687405054873735,true⟩⟩
  | 3,7 => ⟨⟨(-3715327511927984823502443),(-602537669964839039897195),true⟩,⟨(-2522341371296177769517548),374662170814467796640521,true⟩⟩
  | 4,0 => ⟨⟨(-557340908194442182134129),726501316106797186164627,true⟩,⟨(-2090816691457157580521048),(-731145169079385968700804),true⟩⟩
  | 4,1 => ⟨⟨(-193850577114684451398610),974026194820528499423099,true⟩,⟨(-1998821977184708901611198),(-746993899924190482010656),true⟩⟩
  | 4,2 => ⟨⟨61553412034546287346885,1158328165648033403272241,true⟩,⟨(-1923822501300093048773325),(-743260082533311978648598),true⟩⟩
  | 4,3 => ⟨⟨201728104184607018255303,1264744086444748050784364,true⟩,⟨(-1877922017242665257465600),(-735585494015140471105812),true⟩⟩
  | 4,4 => ⟨⟨(-1009216473001560958964781),444707669378514209725097,true⟩,⟨(-2185436534151283188936847),(-677483361765833790501333),true⟩⟩
  | 4,5 => ⟨⟨(-1522786800373687543219213),199606698390193806572045,true⟩,⟨(-2272759882500967936590608),(-545997739866121363459413),true⟩⟩
  | 4,6 => ⟨⟨(-2007054961643627855067218),(-6829121835178351529704),true⟩,⟨(-2341391709173784884276383),(-388237064937257831631107),true⟩⟩
  | 4,7 => ⟨⟨(-2337664791583219261397798),(-134730643957346041578212),true⟩,⟨(-2382781621201839022799930),(-268143198721604269407534),true⟩⟩
  | 5,0 => ⟨⟨1505723013089068005146753,2463313100720500296586468,true⟩,⟨(-1311144430384201265866789),(-426718153213352330226120),true⟩⟩
  | 5,1 => ⟨⟨1753599050186563746382382,2695389207435110287669806,true⟩,⟨(-1164265506620356133844900),(-326748708798713104706503),true⟩⟩
  | 5,2 => ⟨⟨1921716840769721490668896,2850852520905851579849320,true⟩,⟨(-1056496740678796071183405),(-252288063061045979578957),true⟩⟩
  | 5,3 => ⟨⟨2012285320828115811186271,2933525688147273852844180,true⟩,⟨(-995371776867967538070179),(-209926091393197603050583),true⟩⟩
  | 5,4 => ⟨⟨1188825206176575104992484,2165068378196527897024049,true⟩,⟨(-1480016404115285754693689),(-536959850149764726466746),true⟩⟩
  | 5,5 => ⟨⟨836966476311212297194667,1836127305099126909546495,true⟩,⟨(-1643847236429325419063357),(-634496167339656891095946),true⟩⟩
  | 5,6 => ⟨⟨511508346048952436495029,1537519569925462758142364,true⟩,⟨(-1773343416566109105546047),(-699146543523823535967080),true⟩⟩
  | 5,7 => ⟨⟨291175887260840049354146,1340018256742164906295117,true⟩,⟨(-1848915801729614449950921),(-727865678955302844294549),true⟩⟩
  | 6,0 => ⟨⟨2691112931338529931774798,3473642107813551694313521,true⟩,⟨(-415259832481605469111557),173992049104145445252604,true⟩⟩
  | 6,1 => ⟨⟨2748130947172573981539734,3491084814132682075669497,true⟩,⟨(-340243226434320471828537),212730198541429200625370,true⟩⟩
  | 6,2 => ⟨⟨2773790354960846115840090,3488358673240286643252332,true⟩,⟨(-302871942691986012688047),226720295339202292726387,true⟩⟩
  | 6,3 => ⟨⟨2784161314391315053718644,3483391334674596284422610,true⟩,⟨(-289115237329560394834020),228795271449191079250959,true⟩⟩
  | 6,4 => ⟨⟨2582184966768880366385010,3409317563275804218101400,true⟩,⟨(-534817453631177716208168),101529147298854736905236,true⟩⟩
  | 6,5 => ⟨⟨2415362214777355053173451,3283436082066516719510850,true⟩,⟨(-688685954375336974566938),(-437073894470484653504),true⟩⟩
  | 6,6 => ⟨⟨2222375557067217700399345,3120761569447933250401155,true⟩,⟨(-843781393379045581886748),(-105304535199736738767806),true⟩⟩
  | 6,7 => ⟨⟨2073446571547161152658391,2988782724622647231421502,true⟩,⟨(-952746807516438228283516),(-180406086422250859598455),true⟩⟩
  | 7,0 => ⟨⟨2807408390404460202091515,3636461550476356794529487,true⟩,⟨(-465646219830654618566361),153223961842423626146056,true⟩⟩
  | 7,1 => ⟨⟨2864754833295542926298785,3781826688501211590515041,true⟩,⟨(-625180286822908070353126),73030419940241422869077,true⟩⟩
  | 7,2 => ⟨⟨2942987320810548068606232,3963254811574227775764094,true⟩,⟨(-821317232037262452431627),(-25646215020449497630404),true⟩⟩
  | 7,3 => ⟨⟨3007529015853098411011854,4111690683721940318646229,true⟩,⟨(-985803373896676052584938),(-107100960641793247186180),true⟩⟩
  | 7,4 => ⟨⟨2782206986518473264643105,3549475955028800181349036,true⟩,⟨(-362497069119840346203179),203751051965116717435111,true⟩⟩
  | 7,5 => ⟨⟨2779234988323701656189982,3508199091812566378097234,true⟩,⟨(-308997841628462323099194),227392523972616493246815,true⟩⟩
  | 7,6 => ⟨⟨2783142589767471915781195,3490811122016462552132073,true⟩,⟨(-289468857934590110694666),232476053997014900282945,true⟩⟩
  | 7,7 => ⟨⟨2785563754302544875378707,3483339562938394599572857,true⟩,⟨(-286472171050301874903861),229875227746206381706271,true⟩⟩
  | 8,0 => ⟨⟨3371030372649690414728218,5113885571675884192234492,true⟩,⟨(-2335160942577976259346488),(-780379549743102560342187),true⟩⟩
  | 8,1 => ⟨⟨3451536541642750502781968,5541070788969314141503193,true⟩,⟨(-3115104034224745099871437),(-1169110623070149907357586),true⟩⟩
  | 8,2 => ⟨⟨3450277581267578774760132,5919032213625818676421667,true⟩,⟨(-3991430944431963530745148),(-1602390458784435358753332),true⟩⟩
  | 8,3 => ⟨⟨3390163265728472314182608,6149145523962143745962952,true⟩,⟨(-4673549276458193019633820),(-1936112260165923798522906),true⟩⟩
  | 8,4 => ⟨⟨3255024277418950781797373,4735566217261859374797361,true⟩,⟨(-1763994277094203356317782),(-494892406657617704580693),true⟩⟩
  | 8,5 => ⟨⟨3149466775338116611077321,4452837456548089864381005,true⟩,⟨(-1390508968390026698364825),(-308414936317519193275838),true⟩⟩
  | 8,6 => ⟨⟨3074873831578663821816321,4269894325157387319400351,true⟩,⟨(-1168134990723607926008186),(-197664213116734413954400),true⟩⟩
  | 8,7 => ⟨⟨3034573359368827837433605,4174639785621986171086084,true⟩,⟨(-1057368383020925110743522),(-142616278265747171156483),true⟩⟩
  | 9,0 => ⟨⟨2981785974533938289456749,6531174156043441033263616,true⟩,⟨(-6560358907584039443724377),(-2838708714375453916491415),true⟩⟩
  | 9,1 => ⟨⟨2777952111032327509570657,6579374651473092405566674,true⟩,⟨(-7166463054298679753388930),(-3121193305016094319879254),true⟩⟩
  | 9,2 => ⟨⟨2574654224859814052988914,6592042951870219490750041,true⟩,⟨(-7686161420280230614912595),(-3360116785168511665975222),true⟩⟩
  | 9,3 => ⟨⟨2431315922608022956133168,6586068331931824340598902,true⟩,⟨(-8016572936600105933959262),(-3510331348122763505545263),true⟩⟩
  | 9,4 => ⟨⟨3146436342146814393657228,6449885721756927232775904,true⟩,⟨(-5970227110593945490942587),(-2559984155948628046744958),true⟩⟩
  | 9,5 => ⟨⟨3259349806103262299689113,6354736659787631498332697,true⟩,⟨(-5472731252295457709397546),(-2322389288942946741079828),true⟩⟩
  | 9,6 => ⟨⟨3326193629277847430841426,6270210164319944753082174,true⟩,⟨(-5112198315212302525969407),(-2148801666384042383420235),true⟩⟩
  | 9,7 => ⟨⟨3358346385003045342134365,6216431795359559792339532,true⟩,⟨(-4908175378117544411643865),(-2050073731568023487799089),true⟩⟩
  | 10,0 => ⟨⟨668885437413429003997931,6032941277595059650265152,true⟩,⟨(-10834711816903972480081034),(-4718431112277132044414826),true⟩⟩
  | 10,1 => ⟨⟨(-240110950104034681782241),5642217003217134762460759,true⟩,⟨(-11746154064728628825281328),(-5045004431751618309602850),true⟩⟩
  | 10,2 => ⟨⟨(-1104910873067635210565545),5231030511572211134547460,true⟩,⟨(-12459091402405701187030315),(-5279182134914351588977831),true⟩⟩
  | 10,3 => ⟨⟨(-1684934260879256318770871),4934451263595064993067590,true⟩,⟨(-12874641284008455984369652),(-5404244277551983978050009),true⟩⟩
  | 10,4 => ⟨⟨1362116077008914524661144,6317479817359333172623938,true⟩,⟨(-9930906695380697990251468),(-4350714374226525717711474),true⟩⟩
  | 10,5 => ⟨⟨1860913950164704335729610,6480979963320604775413091,true⟩,⟨(-9132635211247939704632230),(-4007017382708084251431469),true⟩⟩
  | 10,6 => ⟨⟨2185983281795539400887374,6554457749932032855199132,true⟩,⟨(-8530003945268282317494770),(-3740971302688460847852760),true⟩⟩
  | 10,7 => ⟨⟨2355593881601137893448867,6578921542480036060236697,true⟩,⟨(-8181421131387498237967863),(-3584761400129155768220338),true⟩⟩
  | 11,0 => ⟨⟨(-4326556232945268494203941),3412504502184956948525006,true⟩,⟨(-14232055508542972409315972),(-5703556397546100079702084),true⟩⟩
  | 11,1 => ⟨⟨(-5140059829556422654121600),2893602431110021704409538,true⟩,⟨(-14488500383091007802439092),(-5715333039864899810671867),true⟩⟩
  | 11,2 => ⟨⟨(-5807112755522070632510899),2451194195660075566708232,true⟩,⟨(-14643177752941020451131997),(-5697789860348532930055484),true⟩⟩
  | 11,3 => ⟨⟨(-6217172635372303915014362),2171548566138777408831628,true⟩,⟨(-14712888448946840546901236),(-5674691434061931766447524),true⟩⟩
  | 11,4 => ⟨⟨(-3496411589312034438317789),3918495415857730414728860,true⟩,⟨(-13893787453696002706510844),(-5653714391310751961559782),true⟩⟩
  | 11,5 => ⟨⟨(-2766988127441802828328874),4342788711259408038762413,true⟩,⟨(-13531326777149483277695961),(-5577390084052336534831817),true⟩⟩
  | 11,6 => ⟨⟨(-2221676905123660399264169),4646873138101125308315717,true⟩,⟨(-13218828742587529383490839),(-5499459939386654134613530),true⟩⟩
  | 11,7 => ⟨⟨(-1907063854304266409534983),4816903956177179283843220,true⟩,⟨(-13021624048061487640726881),(-5445952233306067349889516),true⟩⟩
  | 12,0 => ⟨⟨(-9315708549912229374552153),261112210998053209063038,true⟩,⟨(-14527901566190015440825119),(-4944796248021833971215312),true⟩⟩
  | 12,1 => ⟨⟨(-10131163597063882924624160),(-294057644802074469744191),true⟩,⟨(-14212095202569779725583705),(-4615916023382187258122706),true⟩⟩
  | 12,2 => ⟨⟨(-10766027178038458113316743),(-727034229020313735936689),true⟩,⟨(-13870811957841444626186834),(-4288255836082398629861602),true⟩⟩
  | 12,3 => ⟨⟨(-11147979612826629427827478),(-985256709157437726966431),true⟩,⟨(-13625414436801830912593222),(-4052620775155120476401385),true⟩⟩
  | 12,4 => ⟨⟨(-8399932730119041772524953),857150188094005976575010,true⟩,⟨(-14729489838291727350027063),(-5236926615294423718115464),true⟩⟩
  | 12,5 => ⟨⟨(-7527175634560577739670402),1396664345451989057372794,true⟩,⟨(-14798979280160565940114784),(-5452916039392571762749934),true⟩⟩
  | 12,6 => ⟨⟨(-6833725369319839159208423),1808380533707928430039085,true⟩,⟨(-14780104878944866096983885),(-5586472865468460566419580),true⟩⟩
  | 12,7 => ⟨⟨(-6417817201242287498935028),2048731912191013216037301,true⟩,⟨(-14739793898163081860932707),(-5651571362985850815859541),true⟩⟩
  | 13,0 => ⟨⟨(-13179230578763169990074495),(-2716907141854341431939879),true⟩,⟨(-10875898841231262193755524),(-2019357048698822156123753),true⟩⟩
  | 13,1 => ⟨⟨(-13410043807591313624947338),(-3097932459960302406550190),true⟩,⟨(-9860428113494449761820656),(-1413774177060499349489105),true⟩⟩
  | 13,2 => ⟨⟨(-13470888041344618869129387),(-3356407557031343103000117),true⟩,⟨(-9002660001800259873641787),(-941222687950017505611315),true⟩⟩
  | 13,3 => ⟨⟨(-13454289524906103441451565),(-3492310810405827042364576),true⟩,⟨(-8468147610002607854910132),(-662785573569754243507969),true⟩⟩
  | 13,4 => ⟨⟨(-12751705899773901375294946),(-2248835998524469808213282),true⟩,⟨(-11859054457060560353562002),(-2663925924973000659188730),true⟩⟩
  | 13,5 => ⟨⟨(-12202052030854238612216643),(-1767175008324964889581028),true⟩,⟨(-12659127569590548188997389),(-3244827615073052974306045),true⟩⟩
  | 13,6 => ⟨⟨(-11676527180720464713626609),(-1361674017778411011413300),true⟩,⟨(-13205205807623445582867644),(-3682463871085560606451430),true⟩⟩
  | 13,7 => ⟨⟨(-11326113017855718653551815),(-1109342729656152957346067),true⟩,⟨(-13495403522275594611719724),(-3934199194198616273569833),true⟩⟩
  | 14,0 => ⟨⟨(-12152772147401996177318811),(-3999101678866313005590906),true⟩,⟨(-4404402332420297135138561),1495090794814158700690173,true⟩⟩
  | 14,1 => ⟨⟨(-11463712231711927700929145),(-3985594355158461435807539),true⟩,⟨(-3353815218005444067030288),2062598138228551568735297,true⟩⟩
  | 14,2 => ⟨⟨(-10847354221957457030527273),(-3931335499431847414007014),true⟩,⟨(-2579002238901638565969849),2436127290852474348154431,true⟩⟩
  | 14,3 => ⟨⟨(-10457208362969968768236648),(-3840626616316184505673210),true⟩,⟨(-2140376261144150743566266),2628237439223864335920274,true⟩⟩
  | 14,4 => ⟨⟨(-12751424170463358728313682),(-3941375936483077420331906),true⟩,⟨(-5597703086070317719394359),802861605166993430694240,true⟩⟩
  | 14,5 => ⟨⟨(-13153205349911549939436773),(-3815471456533972804733078),true⟩,⟨(-6744918558428324758693569),216620657771924596638795,true⟩⟩
  | 14,6 => ⟨⟨(-13355788155725687655320600),(-3665009942438314667727855),true⟩,⟨(-7658428076162732823335444),(-262721288929681842777242),true⟩⟩
  | 14,7 => ⟨⟨(-13431762247914685810904695),(-3552626022950762566855616),true⟩,⟨(-8205252637464071393284380),(-530088203676914760558303),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP479Value0_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 0 (0:Fin 8))=sharedDiskP479Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value0_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 0 (1:Fin 8))=sharedDiskP479Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value0_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 0 (2:Fin 8))=sharedDiskP479Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value0_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 0 (3:Fin 8))=sharedDiskP479Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value0_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 0 (4:Fin 8))=sharedDiskP479Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value0_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 0 (5:Fin 8))=sharedDiskP479Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value0_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 0 (6:Fin 8))=sharedDiskP479Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value0_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 0 (7:Fin 8))=sharedDiskP479Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 0 j)=sharedDiskP479Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value0_0
  · exact sharedDiskP479Value0_1
  · exact sharedDiskP479Value0_2
  · exact sharedDiskP479Value0_3
  · exact sharedDiskP479Value0_4
  · exact sharedDiskP479Value0_5
  · exact sharedDiskP479Value0_6
  · exact sharedDiskP479Value0_7
private theorem sharedDiskP479Value1_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 1 (0:Fin 8))=sharedDiskP479Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value1_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 1 (1:Fin 8))=sharedDiskP479Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value1_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 1 (2:Fin 8))=sharedDiskP479Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value1_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 1 (3:Fin 8))=sharedDiskP479Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value1_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 1 (4:Fin 8))=sharedDiskP479Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value1_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 1 (5:Fin 8))=sharedDiskP479Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value1_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 1 (6:Fin 8))=sharedDiskP479Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value1_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 1 (7:Fin 8))=sharedDiskP479Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 1 j)=sharedDiskP479Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value1_0
  · exact sharedDiskP479Value1_1
  · exact sharedDiskP479Value1_2
  · exact sharedDiskP479Value1_3
  · exact sharedDiskP479Value1_4
  · exact sharedDiskP479Value1_5
  · exact sharedDiskP479Value1_6
  · exact sharedDiskP479Value1_7
private theorem sharedDiskP479Value2_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 2 (0:Fin 8))=sharedDiskP479Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value2_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 2 (1:Fin 8))=sharedDiskP479Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value2_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 2 (2:Fin 8))=sharedDiskP479Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value2_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 2 (3:Fin 8))=sharedDiskP479Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value2_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 2 (4:Fin 8))=sharedDiskP479Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value2_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 2 (5:Fin 8))=sharedDiskP479Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value2_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 2 (6:Fin 8))=sharedDiskP479Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value2_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 2 (7:Fin 8))=sharedDiskP479Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 2 j)=sharedDiskP479Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value2_0
  · exact sharedDiskP479Value2_1
  · exact sharedDiskP479Value2_2
  · exact sharedDiskP479Value2_3
  · exact sharedDiskP479Value2_4
  · exact sharedDiskP479Value2_5
  · exact sharedDiskP479Value2_6
  · exact sharedDiskP479Value2_7
private theorem sharedDiskP479Value3_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 3 (0:Fin 8))=sharedDiskP479Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value3_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 3 (1:Fin 8))=sharedDiskP479Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value3_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 3 (2:Fin 8))=sharedDiskP479Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value3_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 3 (3:Fin 8))=sharedDiskP479Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value3_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 3 (4:Fin 8))=sharedDiskP479Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value3_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 3 (5:Fin 8))=sharedDiskP479Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value3_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 3 (6:Fin 8))=sharedDiskP479Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value3_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 3 (7:Fin 8))=sharedDiskP479Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 3 j)=sharedDiskP479Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value3_0
  · exact sharedDiskP479Value3_1
  · exact sharedDiskP479Value3_2
  · exact sharedDiskP479Value3_3
  · exact sharedDiskP479Value3_4
  · exact sharedDiskP479Value3_5
  · exact sharedDiskP479Value3_6
  · exact sharedDiskP479Value3_7
private theorem sharedDiskP479Value4_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 4 (0:Fin 8))=sharedDiskP479Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value4_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 4 (1:Fin 8))=sharedDiskP479Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value4_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 4 (2:Fin 8))=sharedDiskP479Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value4_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 4 (3:Fin 8))=sharedDiskP479Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value4_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 4 (4:Fin 8))=sharedDiskP479Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value4_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 4 (5:Fin 8))=sharedDiskP479Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value4_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 4 (6:Fin 8))=sharedDiskP479Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value4_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 4 (7:Fin 8))=sharedDiskP479Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 4 j)=sharedDiskP479Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value4_0
  · exact sharedDiskP479Value4_1
  · exact sharedDiskP479Value4_2
  · exact sharedDiskP479Value4_3
  · exact sharedDiskP479Value4_4
  · exact sharedDiskP479Value4_5
  · exact sharedDiskP479Value4_6
  · exact sharedDiskP479Value4_7
private theorem sharedDiskP479Value5_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 5 (0:Fin 8))=sharedDiskP479Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value5_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 5 (1:Fin 8))=sharedDiskP479Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value5_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 5 (2:Fin 8))=sharedDiskP479Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value5_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 5 (3:Fin 8))=sharedDiskP479Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value5_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 5 (4:Fin 8))=sharedDiskP479Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value5_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 5 (5:Fin 8))=sharedDiskP479Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value5_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 5 (6:Fin 8))=sharedDiskP479Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value5_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 5 (7:Fin 8))=sharedDiskP479Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 5 j)=sharedDiskP479Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value5_0
  · exact sharedDiskP479Value5_1
  · exact sharedDiskP479Value5_2
  · exact sharedDiskP479Value5_3
  · exact sharedDiskP479Value5_4
  · exact sharedDiskP479Value5_5
  · exact sharedDiskP479Value5_6
  · exact sharedDiskP479Value5_7
private theorem sharedDiskP479Value6_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 6 (0:Fin 8))=sharedDiskP479Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value6_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 6 (1:Fin 8))=sharedDiskP479Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value6_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 6 (2:Fin 8))=sharedDiskP479Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value6_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 6 (3:Fin 8))=sharedDiskP479Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value6_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 6 (4:Fin 8))=sharedDiskP479Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value6_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 6 (5:Fin 8))=sharedDiskP479Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value6_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 6 (6:Fin 8))=sharedDiskP479Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value6_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 6 (7:Fin 8))=sharedDiskP479Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 6 j)=sharedDiskP479Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value6_0
  · exact sharedDiskP479Value6_1
  · exact sharedDiskP479Value6_2
  · exact sharedDiskP479Value6_3
  · exact sharedDiskP479Value6_4
  · exact sharedDiskP479Value6_5
  · exact sharedDiskP479Value6_6
  · exact sharedDiskP479Value6_7
private theorem sharedDiskP479Value7_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 7 (0:Fin 8))=sharedDiskP479Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value7_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 7 (1:Fin 8))=sharedDiskP479Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value7_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 7 (2:Fin 8))=sharedDiskP479Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value7_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 7 (3:Fin 8))=sharedDiskP479Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value7_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 7 (4:Fin 8))=sharedDiskP479Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value7_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 7 (5:Fin 8))=sharedDiskP479Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value7_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 7 (6:Fin 8))=sharedDiskP479Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value7_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 7 (7:Fin 8))=sharedDiskP479Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 7 j)=sharedDiskP479Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value7_0
  · exact sharedDiskP479Value7_1
  · exact sharedDiskP479Value7_2
  · exact sharedDiskP479Value7_3
  · exact sharedDiskP479Value7_4
  · exact sharedDiskP479Value7_5
  · exact sharedDiskP479Value7_6
  · exact sharedDiskP479Value7_7
private theorem sharedDiskP479Value8_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 8 (0:Fin 8))=sharedDiskP479Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value8_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 8 (1:Fin 8))=sharedDiskP479Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value8_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 8 (2:Fin 8))=sharedDiskP479Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value8_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 8 (3:Fin 8))=sharedDiskP479Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value8_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 8 (4:Fin 8))=sharedDiskP479Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value8_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 8 (5:Fin 8))=sharedDiskP479Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value8_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 8 (6:Fin 8))=sharedDiskP479Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value8_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 8 (7:Fin 8))=sharedDiskP479Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 8 j)=sharedDiskP479Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value8_0
  · exact sharedDiskP479Value8_1
  · exact sharedDiskP479Value8_2
  · exact sharedDiskP479Value8_3
  · exact sharedDiskP479Value8_4
  · exact sharedDiskP479Value8_5
  · exact sharedDiskP479Value8_6
  · exact sharedDiskP479Value8_7
private theorem sharedDiskP479Value9_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 9 (0:Fin 8))=sharedDiskP479Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value9_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 9 (1:Fin 8))=sharedDiskP479Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value9_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 9 (2:Fin 8))=sharedDiskP479Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value9_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 9 (3:Fin 8))=sharedDiskP479Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value9_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 9 (4:Fin 8))=sharedDiskP479Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value9_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 9 (5:Fin 8))=sharedDiskP479Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value9_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 9 (6:Fin 8))=sharedDiskP479Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value9_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 9 (7:Fin 8))=sharedDiskP479Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 9 j)=sharedDiskP479Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value9_0
  · exact sharedDiskP479Value9_1
  · exact sharedDiskP479Value9_2
  · exact sharedDiskP479Value9_3
  · exact sharedDiskP479Value9_4
  · exact sharedDiskP479Value9_5
  · exact sharedDiskP479Value9_6
  · exact sharedDiskP479Value9_7
private theorem sharedDiskP479Value10_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 10 (0:Fin 8))=sharedDiskP479Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value10_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 10 (1:Fin 8))=sharedDiskP479Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value10_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 10 (2:Fin 8))=sharedDiskP479Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value10_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 10 (3:Fin 8))=sharedDiskP479Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value10_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 10 (4:Fin 8))=sharedDiskP479Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value10_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 10 (5:Fin 8))=sharedDiskP479Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value10_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 10 (6:Fin 8))=sharedDiskP479Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value10_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 10 (7:Fin 8))=sharedDiskP479Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 10 j)=sharedDiskP479Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value10_0
  · exact sharedDiskP479Value10_1
  · exact sharedDiskP479Value10_2
  · exact sharedDiskP479Value10_3
  · exact sharedDiskP479Value10_4
  · exact sharedDiskP479Value10_5
  · exact sharedDiskP479Value10_6
  · exact sharedDiskP479Value10_7
private theorem sharedDiskP479Value11_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 11 (0:Fin 8))=sharedDiskP479Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value11_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 11 (1:Fin 8))=sharedDiskP479Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value11_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 11 (2:Fin 8))=sharedDiskP479Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value11_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 11 (3:Fin 8))=sharedDiskP479Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value11_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 11 (4:Fin 8))=sharedDiskP479Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value11_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 11 (5:Fin 8))=sharedDiskP479Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value11_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 11 (6:Fin 8))=sharedDiskP479Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value11_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 11 (7:Fin 8))=sharedDiskP479Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 11 j)=sharedDiskP479Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value11_0
  · exact sharedDiskP479Value11_1
  · exact sharedDiskP479Value11_2
  · exact sharedDiskP479Value11_3
  · exact sharedDiskP479Value11_4
  · exact sharedDiskP479Value11_5
  · exact sharedDiskP479Value11_6
  · exact sharedDiskP479Value11_7
private theorem sharedDiskP479Value12_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 12 (0:Fin 8))=sharedDiskP479Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value12_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 12 (1:Fin 8))=sharedDiskP479Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value12_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 12 (2:Fin 8))=sharedDiskP479Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value12_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 12 (3:Fin 8))=sharedDiskP479Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value12_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 12 (4:Fin 8))=sharedDiskP479Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value12_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 12 (5:Fin 8))=sharedDiskP479Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value12_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 12 (6:Fin 8))=sharedDiskP479Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value12_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 12 (7:Fin 8))=sharedDiskP479Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 12 j)=sharedDiskP479Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value12_0
  · exact sharedDiskP479Value12_1
  · exact sharedDiskP479Value12_2
  · exact sharedDiskP479Value12_3
  · exact sharedDiskP479Value12_4
  · exact sharedDiskP479Value12_5
  · exact sharedDiskP479Value12_6
  · exact sharedDiskP479Value12_7
private theorem sharedDiskP479Value13_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 13 (0:Fin 8))=sharedDiskP479Values 13 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value13_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 13 (1:Fin 8))=sharedDiskP479Values 13 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value13_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 13 (2:Fin 8))=sharedDiskP479Values 13 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value13_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 13 (3:Fin 8))=sharedDiskP479Values 13 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value13_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 13 (4:Fin 8))=sharedDiskP479Values 13 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value13_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 13 (5:Fin 8))=sharedDiskP479Values 13 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value13_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 13 (6:Fin 8))=sharedDiskP479Values 13 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value13_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 13 (7:Fin 8))=sharedDiskP479Values 13 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values13_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 13 j)=sharedDiskP479Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value13_0
  · exact sharedDiskP479Value13_1
  · exact sharedDiskP479Value13_2
  · exact sharedDiskP479Value13_3
  · exact sharedDiskP479Value13_4
  · exact sharedDiskP479Value13_5
  · exact sharedDiskP479Value13_6
  · exact sharedDiskP479Value13_7
private theorem sharedDiskP479Value14_0 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 14 (0:Fin 8))=sharedDiskP479Values 14 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value14_1 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 14 (1:Fin 8))=sharedDiskP479Values 14 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value14_2 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 14 (2:Fin 8))=sharedDiskP479Values 14 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value14_3 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 14 (3:Fin 8))=sharedDiskP479Values 14 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value14_4 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 14 (4:Fin 8))=sharedDiskP479Values 14 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value14_5 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 14 (5:Fin 8))=sharedDiskP479Values 14 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value14_6 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 14 (6:Fin 8))=sharedDiskP479Values 14 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP479Value14_7 : truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 14 (7:Fin 8))=sharedDiskP479Values 14 (7:Fin 8) := by decide +kernel
theorem sharedDiskP479Values14_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points 14 j)=sharedDiskP479Values 14 j := by
  intro j
  fin_cases j
  · exact sharedDiskP479Value14_0
  · exact sharedDiskP479Value14_1
  · exact sharedDiskP479Value14_2
  · exact sharedDiskP479Value14_3
  · exact sharedDiskP479Value14_4
  · exact sharedDiskP479Value14_5
  · exact sharedDiskP479Value14_6
  · exact sharedDiskP479Value14_7
theorem sharedDiskP479Values_eq : ∀ (i : Fin 15) (j : Fin 8), truncatedChordCell 1 sharedDiskP479Params (sharedChord469Gauss8Points i j)=sharedDiskP479Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP479Values0_eq
  · exact sharedDiskP479Values1_eq
  · exact sharedDiskP479Values2_eq
  · exact sharedDiskP479Values3_eq
  · exact sharedDiskP479Values4_eq
  · exact sharedDiskP479Values5_eq
  · exact sharedDiskP479Values6_eq
  · exact sharedDiskP479Values7_eq
  · exact sharedDiskP479Values8_eq
  · exact sharedDiskP479Values9_eq
  · exact sharedDiskP479Values10_eq
  · exact sharedDiskP479Values11_eq
  · exact sharedDiskP479Values12_eq
  · exact sharedDiskP479Values13_eq
  · exact sharedDiskP479Values14_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP479Box : HorizontalRectangle := ⟨(23/40),(59/100),(3452812738613/6597069766656),(3476328955951/6597069766656),(978855544101142614705552504004903/649037107316853453566312041152512),(3304894625106460806992725784886175/649037107316853453566312041152512),(-2615407902117974893198513150367303/649037107316853453566312041152512),(-320321159706780666718083606916237/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP479Grid : CGrid := momentChordGrid sharedDiskP479Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984)
theorem sharedDiskP479Columns : containedInReported sharedDiskP479Grid.re sharedDiskP479Box.reLo sharedDiskP479Box.reHi=true ∧ containedInReported sharedDiskP479Grid.im sharedDiskP479Box.imLo sharedDiskP479Box.imHi=true := by
  rw [sharedDiskP479Grid,momentChordGrid_eq_tabulated sharedDiskP479Params chordGaussRule8 1 sharedChord469Bd sharedChord469M (23175049/18014398509481984) sharedChord469Gauss8Points sharedChord469Gauss8Weights sharedDiskP479Values sharedChord469Gauss8Points_eq sharedChord469Gauss8Weights_eq sharedDiskP479Values_eq]
  decide +kernel
theorem sharedDiskP479Sound : sharedDiskP479Box.Sound := by
  intro t a tl tu al au
  change (((23/40):ℚ):ℝ)≤t at tl
  change t≤(((59/100):ℚ):ℝ) at tu
  change (((3452812738613/6597069766656):ℚ):ℝ)≤a at al
  change a≤(((3476328955951/6597069766656):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP479Params_ok] at ps
  have band := sharedChord469ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((21/40):ℚ)≤(23/40))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((59/100):ℚ)≤(63/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3408482035145/6597069766656):ℚ)≤(3452812738613/6597069766656))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3476328955951/6597069766656):ℚ)≤(885480886574489/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord469Bd (by decide +kernel) (by decide +kernel) sharedChord469M (by decide +kernel) (sharedChord469Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP479Columns.1 sharedDiskP479Columns.2
def sharedDiskP479Rows : List SignRow := [positive_479.toSignRow, positive_480.toSignRow, positive_481.toSignRow]
theorem sharedDiskP479Rows_actual : ∀ r∈sharedDiskP479Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP479Rows.all (sharedDiskP479Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP479Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP469Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP473Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP476Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP479Rows_actual
