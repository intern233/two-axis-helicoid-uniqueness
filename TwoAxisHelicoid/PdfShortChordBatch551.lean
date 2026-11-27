import TwoAxisHelicoid.PdfSharedChord521Gauss8
import TwoAxisHelicoid.PdfSharedChord521Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP551Params : ChordParams := ⟨⟨(-29037675283874159307102),(-28877231036482020019087),true⟩,⟨1864085236001804005973657,1871263892177183193976966,true⟩,⟨135270940725744519622503,136206320591415247928437,true⟩,⟨257138353199734140303417,258669794751546805334058,true⟩,⟨364921465852546026771639,365981260706676082007392,true⟩,⟨1152212684636219936576952,1152518735821102584591188,true⟩,⟨(-2152002611340369426275348),(-2148239113012535181666801),true⟩,⟨⟨1141204554050118396811987,1155689221960415483281968,true⟩,⟨(-80141033),80141033,true⟩⟩⟩
theorem sharedDiskP551Params_ok : chordParams (Grid.ofRats (673/800) (337/400)) (Grid.ofRats (965668038965851/1649267441664000) (967278651701851/1649267441664000))=sharedDiskP551Params := by decide +kernel
def sharedDiskP551Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3029556647727251832044426),(-2738024365263177124764333),true⟩,⟨(-218966262259907878804716),19647872617330592799902,true⟩⟩
  | 0,1 => ⟨⟨(-2704623066231571458723719),(-2435278443680086061048822),true⟩,⟨(-272466518404828583557635),(-45792453212894832139853),true⟩⟩
  | 0,2 => ⟨⟨(-2468831433003771268308888),(-2217194696811221599053313),true⟩,⟨(-319991484255513901929198),(-104471186522671912892729),true⟩⟩
  | 0,3 => ⟨⟨(-2335687492655720378027843),(-2094415006774145321712681),true⟩,⟨(-349910299763013206068723),(-141208215712570441971732),true⟩⟩
  | 0,4 => ⟨⟨(-3412368598196654166342278),(-3098400075326206764849122),true⟩,⟨(-174730125146136554754198),72290921630134588891482,true⟩⟩
  | 0,5 => ⟨⟨(-3800177652154676092480456),(-3467775496290101869933018),true⟩,⟨(-151469148151814814297804),97861722555789311229911,true⟩⟩
  | 0,6 => ⟨⟨(-4126791882111923986764399),(-3782206668197914187734333),true⟩,⟨(-149169741896045743729994),97562007086054911938890,true⟩⟩
  | 0,7 => ⟨⟨(-4331225002063110953181540),(-3980446815081066026012275),true⟩,⟨(-157566497950575058063462),86430335651106814854761,true⟩⟩
  | 1,0 => ⟨⟨(-1525844427264471340000507),(-1353125940633391996682371),true⟩,⟨(-569639318098889433955548),(-412269669112089729745649),true⟩⟩
  | 1,1 => ⟨⟨(-1347355389223074978225701),(-1190187105265295432046884),true⟩,⟨(-623161781026557879987334),(-478392603995315874380009),true⟩⟩
  | 1,2 => ⟨⟨(-1217462493847790685214301),(-1071465005020795026676969),true⟩,⟨(-662009794004378680244778),(-526418518650844946813920),true⟩⟩
  | 1,3 => ⟨⟨(-1143494224777633855306139),(-1003765980612750869164087),true⟩,⟨(-683866876065440126618854),(-553463698050026145724219),true⟩⟩
  | 1,4 => ⟨⟨(-1738035267986536746729312),(-1546791087127560069221129),true⟩,⟨(-507241861987684903625856),(-335207518512563507749052),true⟩⟩
  | 1,5 => ⟨⟨(-1958160033941224706351294),(-1747965056218594140659615),true⟩,⟨(-445461442534107825092937),(-258940372024115056175014),true⟩⟩
  | 1,6 => ⟨⟨(-2149788971620651558426381),(-1923540795846933343579569),true⟩,⟨(-395103912157925205973306),(-196838506962672979708317),true⟩⟩
  | 1,7 => ⟨⟨(-2273411370480424154850760),(-2037104225139419680464186),true⟩,⟨(-364620503434294135730912),(-159300576921472189209184),true⟩⟩
  | 2,0 => ⟨⟨(-318180954448063977658238),(-234899815712590966775895),true⟩,⟨(-882207431970175075273406),(-798002853955620470469735),true⟩⟩
  | 2,1 => ⟨⟨(-140952940360895885395900),(-64877955591721617497488),true⟩,⟨(-906213965391384815056110),(-827707308637932433683146),true⟩⟩
  | 2,2 => ⟨⟨(-11074911007808478358422),60692941414216648009626,true⟩,⟨(-918562415477090103883785),(-843620917429363664424168),true⟩⟩
  | 2,3 => ⟨⟨63438751646983824632358,133225377039926614722958,true⟩,⟨(-923778229639855948565673),(-850658742178065604364083),true⟩⟩
  | 2,4 => ⟨⟨(-529550889597883596173326),(-435822667351602399421734),true⟩,⟨(-842844404478136742488698),(-750567343890618085102728),true⟩⟩
  | 2,5 => ⟨⟨(-754188649723177776496558),(-645668478069428310867661),true⟩,⟨(-790830204912349972987557),(-686536834845106725886318),true⟩⟩
  | 2,6 => ⟨⟨(-956565907833987497030702),(-832258768671238768191642),true⟩,⟨(-737396828576029207853051),(-619845856213833764095822),true⟩⟩
  | 2,7 => ⟨⟨(-1091567677045579750425867),(-956189641387735002014990),true⟩,⟨(-699023223705028273704492),(-572233570887472550950858),true⟩⟩
  | 3,0 => ⟨⟨963883447661543981746711,1032910352190316819437057,true⟩,⟨(-950391267496724514012728),(-881534013428930222381023),true⟩⟩
  | 3,1 => ⟨⟨1184782238014960661532215,1257289226676972197757161,true⟩,⟨(-979625745357389492399025),(-908325537782538319774639),true⟩⟩
  | 3,2 => ⟨⟨1355668563831694061885440,1431748927357178545899954,true⟩,⟨(-1021264423119057189747512),(-947086338303678963183453),true⟩⟩
  | 3,3 => ⟨⟨1457836214246197599614686,1536475144688207803049074,true⟩,⟨(-1056674308766202329194582),(-980298505967527315785472),true⟩⟩
  | 3,4 => ⟨⟨715712904198871906302666,782182989289969063066328,true⟩,⟨(-938263615142962742924058),(-870676849659114227340413),true⟩⟩
  | 3,5 => ⟨⟨467894186736917031979096,533172574459593214230781,true⟩,⟨(-935285621937171837135491),(-867567290830054207120494),true⟩⟩
  | 3,6 => ⟨⟨254851471881255706291855,320616642009364174591965,true⟩,⟨(-931808353009912694658473),(-862627916854479608857818),true⟩⟩
  | 3,7 => ⟨⟨116112326492029012502691,184646061388610837131713,true⟩,⟨(-926707236776606935976147),(-854778912916672662503061),true⟩⟩
  | 4,0 => ⟨⟨2195514723016757956019009,2320071783434539193607341,true⟩,⟨(-1768137036755063806642112),(-1645097378691024921365501),true⟩⟩
  | 4,1 => ⟨⟨2354527924845331794551768,2502876005200347173859094,true⟩,⟨(-2218666392538841486803761),(-2069586048163590045449308),true⟩⟩
  | 4,2 => ⟨⟨2415420088320770391038380,2588383489733808028930766,true⟩,⟨(-2713145272523452048869464),(-2536151659630255663197397),true⟩⟩
  | 4,3 => ⟨⟨2399010098578526024845473,2589848591041455349485634,true⟩,⟨(-3084072376613833842017968),(-2886245459699315096746660),true⟩⟩
  | 4,4 => ⟨⟨1984192189135736164901832,2089907204431100890056528,true⟩,⟨(-1441538684729577089603938),(-1338350513996609222342216),true⟩⟩
  | 4,5 => ⟨⟨1775548939155246268182362,1868133464179081379931824,true⟩,⟨(-1238706378596895477689112),(-1148844464986121176615389),true⟩⟩
  | 4,6 => ⟨⟨1608343231934913732114378,1692758711254521122887757,true⟩,⟨(-1127785940298704590837964),(-1045942861780524415143712),true⟩⟩
  | 4,7 => ⟨⟨1507158037158868101875231,1587404619667716172359073,true⟩,⟨(-1077285423252610521719832),(-999433338812941949974607),true⟩⟩
  | 5,0 => ⟨⟨2133766030953536134519398,2369191915372196216195238,true⟩,⟨(-4033157926713651622104709),(-3781390698126581437895397),true⟩⟩
  | 5,1 => ⟨⟨1990795540346311814068578,2239203033445775414669898,true⟩,⟨(-4312110854091719615563160),(-4044103800049514776563180),true⟩⟩
  | 5,2 => ⟨⟨1847921850552666430054671,2106979731934438788816822,true⟩,⟨(-4540684830549489987396760),(-4259165095569827181489358),true⟩⟩
  | 5,3 => ⟨⟨1747536254811414440377417,2013139700642942131293477,true⟩,⟨(-4680762994985996395212750),(-4390850569190371259076925),true⟩⟩
  | 5,4 => ⟨⟨2247435785244792329592034,2469620688197172655792744,true⟩,⟨(-3749143253377847407812855),(-3513688200682435788882021),true⟩⟩
  | 5,5 => ⟨⟨2322438130345480374408967,2532977024408980224804056,true⟩,⟨(-3500484403851525092677628),(-3279170713510681454437508),true⟩⟩
  | 5,6 => ⟨⟨2364029187369481819142840,2565837548017205300262849,true⟩,⟨(-3315161229582991836920825),(-3104323501959797906691862),true⟩⟩
  | 5,7 => ⟨⟨2382512974946335689797655,2579267778519210680917273,true⟩,⟨(-3208431069557368578212105),(-3003608214760867048135417),true⟩⟩
  | 6,0 => ⟨⟨576036040562148687771522,901206969119248671349818,true⟩,⟨(-5689169216848347444162326),(-5328025919287950464582696),true⟩⟩
  | 6,1 => ⟨⟨94087997271042495077955,442490007124670028372790,true⟩,⟨(-5912510519070658180311850),(-5528203190850289601361634),true⟩⟩
  | 6,2 => ⟨⟨(-338064407876137491369452),29631147246260928703973,true⟩,⟨(-6049311433787872495117660),(-5647416925981425514577321),true⟩⟩
  | 6,3 => ⟨⟨(-619200119964971172324649),(-239342928890108415971974),true⟩,⟨(-6109700691253140074964166),(-5697795254152261805628985),true⟩⟩
  | 6,4 => ⟨⟨1015073358775043904361408,1317074353149543105424869,true⟩,⟨(-5407045493325589130169903),(-5070497365977423087965680),true⟩⟩
  | 6,5 => ⟨⟨1353391222076934422136421,1639824570114333322619625,true⟩,⟨(-5122290927926238517495973),(-4805191560121642686643011),true⟩⟩
  | 6,6 => ⟨⟨1576857740545970714363805,1852288521505377753311755,true⟩,⟨(-4890086572612768383559629),(-4587441779978034967605711),true⟩⟩
  | 6,7 => ⟨⟨1694688090862212699450685,1963492302418598491354715,true⟩,⟨(-4749091588795058157519476),(-4455049936316577822788374),true⟩⟩
  | 7,0 => ⟨⟨(-3026385052363673450035637),(-2567763305161946583311358),true⟩,⟨(-5766625999862839597777087),(-5312788479769652903375331),true⟩⟩
  | 7,1 => ⟨⟨(-3688963406667182605532394),(-3218288434640248469204572),true⟩,⟨(-5350173712248953386079470),(-4901854662345709406584576),true⟩⟩
  | 7,2 => ⟨⟨(-4160953010092889216669195),(-3686134554991556891908045),true⟩,⟨(-4913176540133690922405207),(-4476578861343544328101662),true⟩⟩
  | 7,3 => ⟨⟨(-4412686259201675510677637),(-3938081432430224564937118),true⟩,⟨(-4606903767414245159655368),(-4180704826516406244124272),true⟩⟩
  | 7,4 => ⟨⟨(-2278779864930835537607975),(-1839551828957847057726279),true⟩,⟨(-6044893164034444249641619),(-5595170796667685463172837),true⟩⟩
  | 7,5 => ⟨⟨(-1587009246642062543895016),(-1169952035783737504155602),true⟩,⟨(-6158877088807433460352939),(-5720482270314578297296688),true⟩⟩
  | 7,6 => ⟨⟨(-1062346670879145662739410),(-664555897565611621968136),true⟩,⟨(-6162158013674510181849338),(-5736612795686548350258150),true⟩⟩
  | 7,7 => ⟨⟨(-760806166485365210815083),(-375047820080637021812007),true⟩,⟨(-6132048969145612286383998),(-5715504685467972180935161),true⟩⟩
  | 8,0 => ⟨⟨(-5106432123057851164136168),(-4707935344870508782046710),true⟩,⟨(-1739213550750652373303407),(-1460519817555000352320283),true⟩⟩
  | 8,1 => ⟨⟨(-4885793603895565557862683),(-4529577754929994158448161),true⟩,⟨(-955822158912752169249337),(-730487204268051042810667),true⟩⟩
  | 8,2 => ⟨⟨(-4606087647890973016638910),(-4287023793027911352442667),true⟩,⟨(-406668168001906607988451),(-222520434178811169366377),true⟩⟩
  | 8,3 => ⟨⟨(-4402096775572325286740351),(-4106601456146219242299635),true⟩,⟨(-114151713800560519905749),47645546994339122326492,true⟩⟩
  | 8,4 => ⟨⟨(-5145820108687717613936682),(-4710728191832186328675368),true⟩,⟨(-2640208273588300516086456),(-2306961145252468055572247),true⟩⟩
  | 8,5 => ⟨⟨(-4985386603168376556740310),(-4526515557043513334262501),true⟩,⟨(-3477187905486633462878756),(-3099707218425708425156841),true⟩⟩
  | 8,6 => ⟨⟨(-4728734371030984409913376),(-4258613680581680107979446),true⟩,⟨(-4100272587746347602179069),(-3694154790682994261898294),true⟩⟩
  | 8,7 => ⟨⟨(-4524096188201044670508924),(-4050393125508682177475214),true⟩,⟨(-4447712788909123641947506),(-4027471315664570986534128),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP551Value0_0 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP551Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value0_1 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP551Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value0_2 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP551Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value0_3 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP551Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value0_4 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP551Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value0_5 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP551Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value0_6 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP551Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value0_7 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP551Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP551Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 0 j)=sharedDiskP551Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP551Value0_0
  · exact sharedDiskP551Value0_1
  · exact sharedDiskP551Value0_2
  · exact sharedDiskP551Value0_3
  · exact sharedDiskP551Value0_4
  · exact sharedDiskP551Value0_5
  · exact sharedDiskP551Value0_6
  · exact sharedDiskP551Value0_7
private theorem sharedDiskP551Value1_0 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP551Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value1_1 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP551Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value1_2 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP551Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value1_3 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP551Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value1_4 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP551Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value1_5 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP551Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value1_6 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP551Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value1_7 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP551Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP551Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 1 j)=sharedDiskP551Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP551Value1_0
  · exact sharedDiskP551Value1_1
  · exact sharedDiskP551Value1_2
  · exact sharedDiskP551Value1_3
  · exact sharedDiskP551Value1_4
  · exact sharedDiskP551Value1_5
  · exact sharedDiskP551Value1_6
  · exact sharedDiskP551Value1_7
private theorem sharedDiskP551Value2_0 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP551Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value2_1 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP551Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value2_2 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP551Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value2_3 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP551Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value2_4 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP551Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value2_5 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP551Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value2_6 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP551Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value2_7 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP551Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP551Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 2 j)=sharedDiskP551Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP551Value2_0
  · exact sharedDiskP551Value2_1
  · exact sharedDiskP551Value2_2
  · exact sharedDiskP551Value2_3
  · exact sharedDiskP551Value2_4
  · exact sharedDiskP551Value2_5
  · exact sharedDiskP551Value2_6
  · exact sharedDiskP551Value2_7
private theorem sharedDiskP551Value3_0 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP551Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value3_1 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP551Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value3_2 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP551Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value3_3 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP551Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value3_4 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP551Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value3_5 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP551Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value3_6 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP551Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value3_7 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP551Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP551Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 3 j)=sharedDiskP551Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP551Value3_0
  · exact sharedDiskP551Value3_1
  · exact sharedDiskP551Value3_2
  · exact sharedDiskP551Value3_3
  · exact sharedDiskP551Value3_4
  · exact sharedDiskP551Value3_5
  · exact sharedDiskP551Value3_6
  · exact sharedDiskP551Value3_7
private theorem sharedDiskP551Value4_0 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP551Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value4_1 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP551Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value4_2 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP551Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value4_3 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP551Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value4_4 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP551Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value4_5 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP551Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value4_6 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP551Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value4_7 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP551Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP551Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 4 j)=sharedDiskP551Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP551Value4_0
  · exact sharedDiskP551Value4_1
  · exact sharedDiskP551Value4_2
  · exact sharedDiskP551Value4_3
  · exact sharedDiskP551Value4_4
  · exact sharedDiskP551Value4_5
  · exact sharedDiskP551Value4_6
  · exact sharedDiskP551Value4_7
private theorem sharedDiskP551Value5_0 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP551Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value5_1 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP551Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value5_2 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP551Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value5_3 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP551Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value5_4 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP551Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value5_5 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP551Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value5_6 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP551Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value5_7 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP551Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP551Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 5 j)=sharedDiskP551Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP551Value5_0
  · exact sharedDiskP551Value5_1
  · exact sharedDiskP551Value5_2
  · exact sharedDiskP551Value5_3
  · exact sharedDiskP551Value5_4
  · exact sharedDiskP551Value5_5
  · exact sharedDiskP551Value5_6
  · exact sharedDiskP551Value5_7
private theorem sharedDiskP551Value6_0 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP551Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value6_1 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP551Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value6_2 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP551Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value6_3 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP551Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value6_4 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP551Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value6_5 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP551Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value6_6 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP551Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value6_7 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP551Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP551Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 6 j)=sharedDiskP551Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP551Value6_0
  · exact sharedDiskP551Value6_1
  · exact sharedDiskP551Value6_2
  · exact sharedDiskP551Value6_3
  · exact sharedDiskP551Value6_4
  · exact sharedDiskP551Value6_5
  · exact sharedDiskP551Value6_6
  · exact sharedDiskP551Value6_7
private theorem sharedDiskP551Value7_0 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP551Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value7_1 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP551Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value7_2 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP551Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value7_3 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP551Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value7_4 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP551Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value7_5 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP551Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value7_6 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP551Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value7_7 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP551Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP551Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 7 j)=sharedDiskP551Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP551Value7_0
  · exact sharedDiskP551Value7_1
  · exact sharedDiskP551Value7_2
  · exact sharedDiskP551Value7_3
  · exact sharedDiskP551Value7_4
  · exact sharedDiskP551Value7_5
  · exact sharedDiskP551Value7_6
  · exact sharedDiskP551Value7_7
private theorem sharedDiskP551Value8_0 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP551Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value8_1 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP551Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value8_2 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP551Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value8_3 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP551Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value8_4 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP551Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value8_5 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP551Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value8_6 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP551Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP551Value8_7 : truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP551Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP551Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points 8 j)=sharedDiskP551Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP551Value8_0
  · exact sharedDiskP551Value8_1
  · exact sharedDiskP551Value8_2
  · exact sharedDiskP551Value8_3
  · exact sharedDiskP551Value8_4
  · exact sharedDiskP551Value8_5
  · exact sharedDiskP551Value8_6
  · exact sharedDiskP551Value8_7
theorem sharedDiskP551Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP551Params (sharedChord521Gauss8Points i j)=sharedDiskP551Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP551Values0_eq
  · exact sharedDiskP551Values1_eq
  · exact sharedDiskP551Values2_eq
  · exact sharedDiskP551Values3_eq
  · exact sharedDiskP551Values4_eq
  · exact sharedDiskP551Values5_eq
  · exact sharedDiskP551Values6_eq
  · exact sharedDiskP551Values7_eq
  · exact sharedDiskP551Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP551Box : HorizontalRectangle := ⟨(673/800),(337/400),(965668038965851/1649267441664000),(967278651701851/1649267441664000),(388817556353615293547029436427225/5192296858534827628530496329220096),(2197397391636076312924047016586201/5192296858534827628530496329220096),(-4169131237500812611629530350364103/1298074214633706907132624082305024),(-3702931188022164445959168244590023/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP551Grid : CGrid := momentChordGrid sharedDiskP551Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP551Columns : containedInReported sharedDiskP551Grid.re sharedDiskP551Box.reLo sharedDiskP551Box.reHi=true ∧ containedInReported sharedDiskP551Grid.im sharedDiskP551Box.imLo sharedDiskP551Box.imHi=true := by
  rw [sharedDiskP551Grid,momentChordGrid_eq_tabulated sharedDiskP551Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP551Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP551Values_eq]
  decide +kernel
theorem sharedDiskP551Sound : sharedDiskP551Box.Sound := by
  intro t a tl tu al au
  change (((673/800):ℚ):ℝ)≤t at tl
  change t≤(((337/400):ℚ):ℝ) at tu
  change (((965668038965851/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((967278651701851/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP551Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(673/800))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((337/400):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(965668038965851/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((967278651701851/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP551Columns.1 sharedDiskP551Columns.2
def sharedDiskP551Rows : List SignRow := [positive_551.toSignRow]
theorem sharedDiskP551Rows_actual : ∀ r∈sharedDiskP551Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP551Rows.all (sharedDiskP551Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP551Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP552Params : ChordParams := ⟨⟨(-29198531619297108118944),(-29037675283874159306498),true⟩,⟨1859586282514489382978864,1866747612859508491143890,true⟩,⟨135516048309055843366551,136451364059118215190012,true⟩,⟨258100761733994199814640,259634214114253917722687,true⟩,⟨365886286407650895686046,366945987165987309579689,true⟩,⟨1151905927009781769896904,1152212684636219936578106,true⟩,⟨(-2148239113012535181675797),(-2144485450619538367131149),true⟩,⟨⟨1140847624282238061892517,1155339324940774658904385,true⟩,⟨(-85025408),85025408,true⟩⟩⟩
theorem sharedDiskP552Params_ok : chordParams (Grid.ofRats (337/400) (27/32)) (Grid.ofRats (322101534088827/549755813888000) (322638405000827/549755813888000))=sharedDiskP552Params := by decide +kernel
def sharedDiskP552Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3028465934175569363993396),(-2736468261619833803660433),true⟩,⟨(-218203762628522739273438),20864919425103563312543,true⟩⟩
  | 0,1 => ⟨⟨(-2704795627918856851473578),(-2434932946512445985655922),true⟩,⟨(-271216812349118755778338),(-44056146009342195399596),true⟩⟩
  | 0,2 => ⟨⟨(-2469811665604295929494362),(-2217638941893282463266115),true⟩,⟨(-318381864061256810583311),(-102376771072371971972473),true⟩⟩
  | 0,3 => ⟨⟨(-2337095066190785959466556),(-2095272988338469732400396),true⟩,⟨(-348101663469451163785655),(-138904480484915384254913),true⟩⟩
  | 0,4 => ⟨⟨(-3409606249188090160125745),(-3095240345928295359476107),true⟩,⟨(-174484920906415841717937),72961042280180915037358,true⟩⟩
  | 0,5 => ⟨⟨(-3795539262101397460640128),(-3462809224230254709031919),true⟩,⟨(-151639702382720656882304),98113780253342288764389,true⟩⟩
  | 0,6 => ⟨⟨(-4120450932049653171611932),(-3775592625594648868322346),true⟩,⟨(-149577248647012613199635),97586659913021296841456,true⟩⟩
  | 0,7 => ⟨⟨(-4323767397056462342307749),(-3972749918408858626169479),true⟩,⟨(-158072181255317587201770),86386724292808443687668,true⟩⟩
  | 1,0 => ⟨⟨(-1529326300527062125989862),(-1356040621560703739392433),true⟩,⟨(-566913607316913358351709),(-409035686780484366405946),true⟩⟩
  | 1,1 => ⟨⟨(-1351192431201303411354798),(-1193470715657875023788701),true⟩,⟨(-620358294692534363745127),(-475094685626917964086853),true⟩⟩
  | 1,2 => ⟨⟨(-1221542168538755964147821),(-1075005160662897858463838),true⟩,⟨(-659191439911284842972644),(-523119828104019353511683),true⟩⟩
  | 1,3 => ⟨⟨(-1147707387995591714172182),(-1007448871723519521018872),true⟩,⟨(-681057381457456877604630),(-550183259688771386402306),true⟩⟩
  | 1,4 => ⟨⟨(-1741053689695992958994731),(-1549234541364993800240677),true⟩,⟨(-504681970369604023358244),(-332131596954631882919413),true⟩⟩
  | 1,5 => ⟨⟨(-1960641279517394105287878),(-1749873043885221763693274),true⟩,⟨(-443139931195474487120723),(-256104174925535626423972),true⟩⟩
  | 1,6 => ⟨⟨(-2151750318712176758402517),(-1924937895451897712931172),true⟩,⟨(-393030349666003073930083),(-194257979723476746096990),true⟩⟩
  | 1,7 => ⟨⟨(-2275009989399767862270094),(-2038147745206015551477345),true⟩,⟨(-362721070770346771988093),(-156901683183936433866939),true⟩⟩
  | 2,0 => ⟨⟨(-323776819483858652629397),(-240189529963015641624285),true⟩,⟨(-880418750819855463254814),(-795969878946924962571747),true⟩⟩
  | 2,1 => ⟨⟨(-146862851702412844751105),(-70515412069311253503024),true⟩,⟨(-904873609305114362610550),(-826147095918740862724644),true⟩⟩
  | 2,2 => ⟨⟨(-17215784453129319754404),54792947171309987722195,true⟩,⟨(-917585368211277302106171),(-842438439227123056725947),true⟩⟩
  | 2,3 => ⟨⟨57177314710771538012368,127182656014873872171557,true⟩,⟨(-923020204684676273774384),(-849702212624218834796632),true⟩⟩
  | 2,4 => ⟨⟨(-534780067806419842650777),(-440699551363949080643525),true⟩,⟨(-840612027080855674259550),(-748055258636376771452760),true⟩⟩
  | 2,5 => ⟨⟨(-759073697075442673038012),(-650083220553268404664855),true⟩,⟨(-788297527206228222235577),(-683593852361580199101215),true⟩⟩
  | 2,6 => ⟨⟨(-961105799820158196817253),(-836295314128984482010669),true⟩,⟨(-734670307820868126031736),(-616675729971427872308014),true⟩⟩
  | 2,7 => ⟨⟨(-1095872915727431214567495),(-959971615088651219953164),true⟩,⟨(-696227881047165327355616),(-568974405251828181614757),true⟩⟩
  | 3,0 => ⟨⟨956415688206309733612076,1025512432015774985306524,true⟩,⟨(-952425674473441718759457),(-883454494723199464859080),true⟩⟩
  | 3,1 => ⟨⟨1177140631777920677099980,1249725188205263192285074,true⟩,⟨(-982342333940181223084472),(-910915779962900277027876),true⟩⟩
  | 3,2 => ⟨⟨1347908308035178718768626,1424077311550033201979778,true⟩,⟨(-1024514334414633156632861),(-950195907893687316041505),true⟩⟩
  | 3,3 => ⟨⟨1450000883474869528262888,1528737125352572732168439,true⟩,⟨(-1060250545293229618202790),(-983724178440572185602110),true⟩⟩
  | 3,4 => ⟨⟨708501761754085001277312,775042324282707758479780,true⟩,⟨(-939522995576446401213227),(-871828542501433732934641),true⟩⟩
  | 3,5 => ⟨⟨461015445542648042105409,526375477331932916790813,true⟩,⟨(-935757058009245179319638),(-867928622253002229373275),true⟩⟩
  | 3,6 => ⟨⟨248262439037574551115759,314199730908413054511904,true⟩,⟨(-931636867993216093809694),(-862286564297921552902277),true⟩⟩
  | 3,7 => ⟨⟨109759047689276914389086,178504033460099501420147,true⟩,⟨(-926107685070841789792296),(-853985162111495624870733),true⟩⟩
  | 4,0 => ⟨⟨2185935778622618270514042,2310673564674655942137846,true⟩,⟨(-1774551393557805634060344),(-1651245175440061538889827),true⟩⟩
  | 4,1 => ⟨⟨2343381919669416464426558,2491941026517547724671462,true⟩,⟨(-2225884396281555854105497),(-2076492020313268048110923),true⟩⟩
  | 4,2 => ⟨⟨2402295983444018948292951,2575486355058415141016336,true⟩,⟨(-2720700618166094767288163),(-2543365335694603006034489),true⟩⟩
  | 4,3 => ⟨⟨2384287635867460233641595,2575353047068566941573309,true⟩,⟨(-3091515543752648990341949),(-2893339211702616047430156),true⟩⟩
  | 4,4 => ⟨⟨1975544505591962634544718,2081408344927982146609321,true⟩,⟨(-1447017646932408888049469),(-1343607529888355407867939),true⟩⟩
  | 4,5 => ⟨⟨1767365511589139689554684,1860074221248347220921172,true⟩,⟨(-1243373217079097729607500),(-1153323227688467766577309),true⟩⟩
  | 4,6 => ⟨⟨1600374985507089782578945,1684899269901546428071491,true⟩,⟨(-1131861634308580091372238),(-1049851981221248452049444),true⟩⟩
  | 4,7 => ⟨⟨1499283041956013541039764,1579630896269374379606240,true⟩,⟨(-1081022494644204238744880),(-1003014734241891649125299),true⟩⟩
  | 5,0 => ⟨⟨2114791317359683274729262,2350392727068419273659467,true⟩,⟨(-4038772943889142725115718),(-3786701595005096005076009),true⟩⟩
  | 5,1 => ⟨⟨1970599234167903124583234,2219151105882669942575188,true⟩,⟨(-4316708733581273379060572),(-4048432178479948336107072),true⟩⟩
  | 5,2 => ⟨⟨1826762217473704838785494,2085932487179265558199043,true⟩,⟨(-4544256713894459715100698),(-4262504766556435521273808),true⟩⟩
  | 5,3 => ⟨⟨1725810686798798613591762,1991503710179614704803568,true⟩,⟨(-4683610936890406311359652),(-4393493646353426041373179),true⟩⟩
  | 5,4 => ⟨⟨2229733431878908040674091,2452117573695845915670066,true⟩,⟨(-3755555083756430457713911),(-3519771465832550009603693),true⟩⟩
  | 5,5 => ⟨⟨2305857083603123720712400,2516609924871674081281197,true⟩,⟨(-3507412671715204619799418),(-3285757010980895584159769),true⟩⟩
  | 5,6 => ⟨⟨2348280573762769442265386,2550310400191227591379590,true⟩,⟨(-3322371112004499387969808),(-3111185882180831444760811),true⟩⟩
  | 5,7 => ⟨⟨2367240401257966347366130,2564219719891863769623439,true⟩,⟨(-3215764662532400506040178),(-3010592753056357246549733),true⟩⟩
  | 6,0 => ⟨⟨551268886156575727872928,876758044443590250310376,true⟩,⟨(-5683878658284079748912810),(-5322582877545085732047464),true⟩⟩
  | 6,1 => ⟨⟨69480708388679811095172,418101480131797317853648,true⟩,⟨(-5904005132982119403618047),(-5519695143858309512775585),true⟩⟩
  | 6,2 => ⟨⟨(-362092184052334844797461),5765491502815137914043,true⟩,⟨(-6038060903973940971015463),(-5636303650033988129821930),true⟩⟩
  | 6,3 => ⟨⟨(-642603522165405485205979),(-262613093562160745498104),true⟩,⟨(-6096745509557401093320615),(-5685070181356585287122393),true⟩⟩
  | 6,4 => ⟨⟨990733266902510924832565,1292895385826544481075155,true⟩,⟨(-5404789859337487015658023),(-5068105404145605073570050),true⟩⟩
  | 6,5 => ⟨⟨1330071118988896142128754,1616503115694181711135139,true⟩,⟨(-5122294375151660632709638),(-4805103591390905729776235),true⟩⟩
  | 6,6 => ⟨⟨1554333584938230866486364,1829814753966525694461274,true⟩,⟨(-4891701639014079501676578),(-4588900108753896250592202),true⟩⟩
  | 6,7 => ⟨⟨1672694951397115279802201,1941576651652286774811101,true⟩,⟨(-4751557898287911008203036),(-4457326084773267641527968),true⟩⟩
  | 7,0 => ⟨⟨(-3038247652472073818889143),(-2580207888311516981460793),true⟩,⟨(-5742983174555317049608928),(-5290149655223385898294915),true⟩⟩
  | 7,1 => ⟨⟨(-3695745441610487582419679),(-3225870157008713863331145),true⟩,⟨(-5325541458671842110765222),(-4878395071665439471825467),true⟩⟩
  | 7,2 => ⟨⟨(-4163524927815222113781710),(-3689659680622519121191093),true⟩,⟨(-4888796188973669585846037),(-4453458264767050204218908),true⟩⟩
  | 7,3 => ⟨⟨(-4412761662022463952744818),(-3939188619774366257749937),true⟩,⟨(-4583154225929850441253737),(-4158242150137618440590641),true⟩⟩
  | 7,4 => ⟨⟨(-2295365852687488911879193),(-1856480860129626784968435),true⟩,⟨(-6023624016574197203131896),(-5574680151679915591204257),true⟩⟩
  | 7,5 => ⟨⟨(-1607060581953799357937595),(-1190137059222942630193885),true⟩,⟨(-6140653609153251816786952),(-5702811966965739966807267),true⟩⟩
  | 7,6 => ⟨⟨(-1084439098256038831373429),(-686633058538229396946742),true⟩,⟨(-6146665026834650652927386),(-5721497827326181886222489),true⟩⟩
  | 7,7 => ⟨⟨(-783833164936499485885485),(-397978432299088644935247),true⟩,⟨(-6118261967262619828948011),(-5701994919187891596609989),true⟩⟩
  | 8,0 => ⟨⟨(-5095288007064956021363844),(-4697834975440861683071926),true⟩,⟨(-1729175177545202062455838),(-1451291688939011220371914),true⟩⟩
  | 8,1 => ⟨⟨(-4875038601737124073937073),(-4519671051235003694887354),true⟩,⟨(-950448966446734509786246),(-725642879542208006969649),true⟩⟩
  | 8,2 => ⟨⟨(-4596606025199547136817824),(-4278204807478399643906407),true⟩,⟨(-404464149615948599339284),(-220636398851050614333419),true⟩⟩
  | 8,3 => ⟨⟨(-4393691035178990219767329),(-4098736674429878925221312),true⟩,⟨(-113533469864702787009326),48078756138618329106504,true⟩⟩
  | 8,4 => ⟨⟨(-5136082282700379807281468),(-4702152449878740910387565),true⟩,⟨(-2624982487426462745625799),(-2292801333903790653460162),true⟩⟩
  | 8,5 => ⟨⟨(-4978648772018710761803484),(-4520953362352410446137354),true⟩,⟨(-3457666845438746131201505),(-3081413337756330982128670),true⟩⟩
  | 8,6 => ⟨⟨(-4725328582367260293903759),(-4256329673109109697046193),true⟩,⟨(-4078120112029931270775894),(-3673289225659721377451429),true⟩⟩
  | 8,7 => ⟨⟨(-4522996238289266585599213),(-4050358205143917390642928),true⟩,⟨(-4424399890141872884771447),(-4005450753729692047828387),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP552Value0_0 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP552Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value0_1 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP552Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value0_2 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP552Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value0_3 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP552Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value0_4 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP552Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value0_5 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP552Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value0_6 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP552Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value0_7 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP552Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP552Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 0 j)=sharedDiskP552Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP552Value0_0
  · exact sharedDiskP552Value0_1
  · exact sharedDiskP552Value0_2
  · exact sharedDiskP552Value0_3
  · exact sharedDiskP552Value0_4
  · exact sharedDiskP552Value0_5
  · exact sharedDiskP552Value0_6
  · exact sharedDiskP552Value0_7
private theorem sharedDiskP552Value1_0 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP552Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value1_1 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP552Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value1_2 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP552Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value1_3 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP552Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value1_4 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP552Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value1_5 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP552Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value1_6 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP552Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value1_7 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP552Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP552Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 1 j)=sharedDiskP552Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP552Value1_0
  · exact sharedDiskP552Value1_1
  · exact sharedDiskP552Value1_2
  · exact sharedDiskP552Value1_3
  · exact sharedDiskP552Value1_4
  · exact sharedDiskP552Value1_5
  · exact sharedDiskP552Value1_6
  · exact sharedDiskP552Value1_7
private theorem sharedDiskP552Value2_0 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP552Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value2_1 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP552Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value2_2 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP552Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value2_3 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP552Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value2_4 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP552Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value2_5 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP552Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value2_6 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP552Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value2_7 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP552Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP552Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 2 j)=sharedDiskP552Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP552Value2_0
  · exact sharedDiskP552Value2_1
  · exact sharedDiskP552Value2_2
  · exact sharedDiskP552Value2_3
  · exact sharedDiskP552Value2_4
  · exact sharedDiskP552Value2_5
  · exact sharedDiskP552Value2_6
  · exact sharedDiskP552Value2_7
private theorem sharedDiskP552Value3_0 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP552Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value3_1 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP552Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value3_2 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP552Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value3_3 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP552Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value3_4 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP552Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value3_5 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP552Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value3_6 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP552Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value3_7 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP552Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP552Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 3 j)=sharedDiskP552Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP552Value3_0
  · exact sharedDiskP552Value3_1
  · exact sharedDiskP552Value3_2
  · exact sharedDiskP552Value3_3
  · exact sharedDiskP552Value3_4
  · exact sharedDiskP552Value3_5
  · exact sharedDiskP552Value3_6
  · exact sharedDiskP552Value3_7
private theorem sharedDiskP552Value4_0 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP552Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value4_1 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP552Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value4_2 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP552Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value4_3 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP552Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value4_4 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP552Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value4_5 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP552Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value4_6 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP552Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value4_7 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP552Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP552Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 4 j)=sharedDiskP552Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP552Value4_0
  · exact sharedDiskP552Value4_1
  · exact sharedDiskP552Value4_2
  · exact sharedDiskP552Value4_3
  · exact sharedDiskP552Value4_4
  · exact sharedDiskP552Value4_5
  · exact sharedDiskP552Value4_6
  · exact sharedDiskP552Value4_7
private theorem sharedDiskP552Value5_0 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP552Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value5_1 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP552Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value5_2 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP552Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value5_3 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP552Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value5_4 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP552Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value5_5 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP552Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value5_6 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP552Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value5_7 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP552Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP552Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 5 j)=sharedDiskP552Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP552Value5_0
  · exact sharedDiskP552Value5_1
  · exact sharedDiskP552Value5_2
  · exact sharedDiskP552Value5_3
  · exact sharedDiskP552Value5_4
  · exact sharedDiskP552Value5_5
  · exact sharedDiskP552Value5_6
  · exact sharedDiskP552Value5_7
private theorem sharedDiskP552Value6_0 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP552Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value6_1 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP552Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value6_2 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP552Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value6_3 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP552Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value6_4 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP552Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value6_5 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP552Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value6_6 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP552Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value6_7 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP552Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP552Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 6 j)=sharedDiskP552Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP552Value6_0
  · exact sharedDiskP552Value6_1
  · exact sharedDiskP552Value6_2
  · exact sharedDiskP552Value6_3
  · exact sharedDiskP552Value6_4
  · exact sharedDiskP552Value6_5
  · exact sharedDiskP552Value6_6
  · exact sharedDiskP552Value6_7
private theorem sharedDiskP552Value7_0 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP552Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value7_1 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP552Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value7_2 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP552Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value7_3 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP552Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value7_4 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP552Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value7_5 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP552Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value7_6 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP552Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value7_7 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP552Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP552Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 7 j)=sharedDiskP552Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP552Value7_0
  · exact sharedDiskP552Value7_1
  · exact sharedDiskP552Value7_2
  · exact sharedDiskP552Value7_3
  · exact sharedDiskP552Value7_4
  · exact sharedDiskP552Value7_5
  · exact sharedDiskP552Value7_6
  · exact sharedDiskP552Value7_7
private theorem sharedDiskP552Value8_0 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP552Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value8_1 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP552Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value8_2 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP552Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value8_3 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP552Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value8_4 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP552Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value8_5 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP552Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value8_6 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP552Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP552Value8_7 : truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP552Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP552Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points 8 j)=sharedDiskP552Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP552Value8_0
  · exact sharedDiskP552Value8_1
  · exact sharedDiskP552Value8_2
  · exact sharedDiskP552Value8_3
  · exact sharedDiskP552Value8_4
  · exact sharedDiskP552Value8_5
  · exact sharedDiskP552Value8_6
  · exact sharedDiskP552Value8_7
theorem sharedDiskP552Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP552Params (sharedChord521Gauss8Points i j)=sharedDiskP552Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP552Values0_eq
  · exact sharedDiskP552Values1_eq
  · exact sharedDiskP552Values2_eq
  · exact sharedDiskP552Values3_eq
  · exact sharedDiskP552Values4_eq
  · exact sharedDiskP552Values5_eq
  · exact sharedDiskP552Values6_eq
  · exact sharedDiskP552Values7_eq
  · exact sharedDiskP552Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP552Box : HorizontalRectangle := ⟨(337/400),(27/32),(322101534088827/549755813888000),(322638405000827/549755813888000),(651297497674079516465326971711119/10384593717069655257060992658440192),(4249946042896326290252577478045327/10384593717069655257060992658440192),(-1041651205036495774793067443776997/324518553658426726783156020576256),(-925674143262879790683276173635045/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP552Grid : CGrid := momentChordGrid sharedDiskP552Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP552Columns : containedInReported sharedDiskP552Grid.re sharedDiskP552Box.reLo sharedDiskP552Box.reHi=true ∧ containedInReported sharedDiskP552Grid.im sharedDiskP552Box.imLo sharedDiskP552Box.imHi=true := by
  rw [sharedDiskP552Grid,momentChordGrid_eq_tabulated sharedDiskP552Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP552Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP552Values_eq]
  decide +kernel
theorem sharedDiskP552Sound : sharedDiskP552Box.Sound := by
  intro t a tl tu al au
  change (((337/400):ℚ):ℝ)≤t at tl
  change t≤(((27/32):ℚ):ℝ) at tu
  change (((322101534088827/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((322638405000827/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP552Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(337/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((27/32):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(322101534088827/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((322638405000827/549755813888000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP552Columns.1 sharedDiskP552Columns.2
def sharedDiskP552Rows : List SignRow := [positive_552.toSignRow]
theorem sharedDiskP552Rows_actual : ∀ r∈sharedDiskP552Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP552Rows.all (sharedDiskP552Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP552Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP553Params : ChordParams := ⟨⟨(-29359799168472402862962),(-29198531619297108118340),true⟩,⟨1855096539260759436972735,1862240608756002620613058,true⟩,⟨135760410666075022176090,136695657811393972900631,true⟩,⟨259064784713126220124547,260600243801630579672165,true⟩,⟨366850530944069941607826,367910133788459005791693,true⟩,⟨1151598465189973591088542,1151905927009781769898056,true⟩,⟨(-2144485450619538367140125),(-2140741584690001343915825),true⟩,⟨⟨1140489586137500182433301,1154988242387248381815203,true⟩,⟨(-90191864),90191864,true⟩⟩⟩
theorem sharedDiskP553Params_ok : chordParams (Grid.ofRats (27/32) (169/200)) (Grid.ofRats (966942670134869/1649267441664000) (968553282870869/1649267441664000))=sharedDiskP553Params := by decide +kernel
def sharedDiskP553Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3027366534957321567904986),(-2734895383707896149683644),true⟩,⟨(-217454504991732678306012),22077064623325928055451,true⟩⟩
  | 0,1 => ⟨⟨(-2704955120788019300903877),(-2434566993527381707561914),true⟩,⟨(-269982385117977751335515),(-42327523176088670166667),true⟩⟩
  | 0,2 => ⟨⟨(-2470776638541128445443627),(-2218060960537176413467514),true⟩,⟨(-316788540659215013007029),(-100291459938292172475794),true⟩⟩
  | 0,3 => ⟨⟨(-2338486395173685692895718),(-2096108037027573296344814),true⟩,⟨(-346309658187470178381177),(-136610486429877685052597),true⟩⟩
  | 0,4 => ⟨⟨(-3406842338913123591292821),(-3092070196059648607668107),true⟩,⟨(-174250158326669485888223),73629795394392621168383,true⟩⟩
  | 0,5 => ⟨⟨(-3790908658112118085976182),(-3457841210503950076372120),true⟩,⟨(-151818093704905876876512),98367490754359195683657,true⟩⟩
  | 0,6 => ⟨⟨(-4114127141748134697793910),(-3768985765410091556620516),true⟩,⟨(-149991057524593931057697),97614601379678719176415,true⟩⟩
  | 0,7 => ⟨⟨(-4316333422026798630394847),(-3965066446322672860429769),true⟩,⟨(-158583744723727743755830),86346782413512642649340,true⟩⟩
  | 1,0 => ⟨⟨(-1532788942879268424132737),(-1358931001324937847335994),true⟩,⟨(-564201331723796859211226),(-405809893867194774733547),true⟩⟩
  | 1,1 => ⟨⟨(-1355009849456403383531406),(-1196729974165316127145888),true⟩,⟨(-617566153578875146177252),(-471803186256963506654353),true⟩⟩
  | 1,2 => ⟨⟨(-1225601898898612116394920),(-1078520894054342623219870),true⟩,⟨(-656382601288431737203264),(-519825959992532181772758),true⟩⟩
  | 1,3 => ⟨⟨(-1151900402335585546340139),(-1011107279919456316269405),true⟩,⟨(-678256252344189159015570),(-546906628832656890778747),true⟩⟩
  | 1,4 => ⟨⟨(-1744053360654501490977346),(-1551653764475091770177985),true⟩,⟨(-502137328851594488982940),(-329065287200412994263581),true⟩⟩
  | 1,5 => ⟨⟨(-1963104418356911559880380),(-1751757009381353905756638),true⟩,⟨(-440834787817872144796261),(-253278272828814034134096),true⟩⟩
  | 1,6 => ⟨⟨(-2153694353479611943656198),(-1926311378851613233416873),true⟩,⟨(-390973531006816069791466),(-191687718715983764744358),true⟩⟩
  | 1,7 => ⟨⟨(-2276591968755510841203500),(-2039168066865964270523874),true⟩,⟨(-360838355498331407243372),(-154512756820630682632257),true⟩⟩
  | 2,0 => ⟨⟨(-329349489021126606351639),(-245452893595103285317147),true⟩,⟨(-878622708847115542772225),(-793926409809029016755048),true⟩⟩
  | 2,1 => ⟨⟨(-152749024323334307914389),(-76126338885137007504814),true⟩,⟨(-903522534859029121692302),(-824573423640963561227340),true⟩⟩
  | 2,2 => ⟨⟨(-23332742331492228367537),48919476491426309539713,true⟩,⟨(-916595362770467593528915),(-841240526715976290700271),true⟩⟩
  | 2,3 => ⟨⟨50939720661118755776056,121166314840036563957260,true⟩,⟨(-922248038252217312272126),(-848729207266770968214402),true⟩⟩
  | 2,4 => ⟨⟨(-539986948567271008767803),(-445550528147923754228089),true⟩,⟨(-838376568436543703825760),(-745536464668750839189006),true⟩⟩
  | 2,5 => ⟨⟨(-763937189033429764155768),(-654472859208118897346668),true⟩,⟨(-785766134445706185476456),(-680648361984444597672793),true⟩⟩
  | 2,6 => ⟨⟨(-965624937379003729286696),(-840307141748853985637949),true⟩,⟨(-731948938768649780409855),(-613506551760011105998432),true⟩⟩
  | 2,7 => ⟨⟨(-1100157850575812705060137),(-963729052766600766089465),true⟩,⟨(-693440053108275138622531),(-565718292667800936537409),true⟩⟩
  | 3,0 => ⟨⟨948961392723252412293126,1018129811918420759997530,true⟩,⟨(-954438292238524292673962),(-885351678982162857218287),true⟩⟩
  | 3,1 => ⟨⟨1169506715583914797574562,1242170479141579260170349,true⟩,⟨(-985036401581154886294205),(-913482162268956606629444),true⟩⟩
  | 3,2 => ⟨⟨1340150416028440195121683,1416409556731578268326076,true⟩,⟨(-1027741043162464823968503),(-953281051121942489054587),true⟩⟩
  | 3,3 => ⟨⟨1442164389684461419431312,1520999357748419922258687,true⟩,⟨(-1063803009644839881860749),(-987124919703518792426546),true⟩⟩
  | 3,4 => ⟨⟨701309001873422664452842,767922124585330092354878,true⟩,⟨(-940761682755997700098692),(-872957805494005535719417),true⟩⟩
  | 3,5 => ⟨⟨454158324647053401248603,519602367997653841252424,true⟩,⟨(-936209583706963655762693),(-868269022060509430996418),true⟩⟩
  | 3,6 => ⟨⟨241696746382774912497423,307830322110288118708403,true⟩,⟨(-931448591105638660268529),(-861911151613699477645470),true⟩⟩
  | 3,7 => ⟨⟨103429545042595983260859,172388230284088892360977,true⟩,⟨(-925493205064694571294370),(-853174243935017011586355),true⟩⟩
  | 4,0 => ⟨⟨2176322191367514286966077,2301241686465676520344771,true⟩,⟨(-1780923618088580793152198),(-1657350138280374984436315),true⟩⟩
  | 4,1 => ⟨⟨2332191938034575988813216,2480962768429210284703851,true⟩,⟨(-2233043713238567304000373),(-2083338971528098042645403),true⟩⟩
  | 4,2 => ⟨⟨2389124213367014169865871,2562541900893763762769141,true⟩,⟨(-2728176513746248882473582),(-2550499718154958086310165),true⟩⟩
  | 4,3 => ⟨⟨2369519100618010558512886,2560811500995236936089902,true⟩,⟨(-3098862641433961074808671),(-2900337463325106856667914),true⟩⟩
  | 4,4 => ⟨⟨1966873264830077628038539,2072887096026449977597890,true⟩,⟨(-1452464409041307261829633),(-1348831429503697653687394),true⟩⟩
  | 4,5 => ⟨⟨1759168232206397568638642,1852002406198139189249498,true⟩,⟨(-1248012835023213291152231),(-1157773736386446776160596),true⟩⟩
  | 4,6 => ⟨⟨1592399873441842876960094,1677034311383088078410044,true⟩,⟨(-1135912336300190556221770),(-1053735008499331288273688),true⟩⟩
  | 4,7 => ⟨⟨1491405080720421800663052,1571855592858273972873514,true⟩,⟨(-1084735453687889706859533),(-1006570881999678818709141),true⟩⟩
  | 5,0 => ⟨⟨2095792716228497195327312,2331569084363736712915860,true⟩,⟨(-4044249458684073955439952),(-3791875659115584232524901),true⟩⟩
  | 5,1 => ⟨⟨1950391018783362797763478,2199086571549572480980366,true⟩,⟨(-4321156893633223359569653),(-4052612797100137189378108),true⟩⟩
  | 5,2 => ⟨⟨1805602571584295227614892,2064884461033034314591920,true⟩,⟨(-4547670618945456759812703),(-4265688624329305566714665),true⟩⟩
  | 5,3 => ⟨⟨1704093390132918260065073,1969875199911207048974134,true⟩,⟨(-4686296395428450384797379),(-4395976510633640439373645),true⟩⟩
  | 5,4 => ⟨⟨2211997664320048469164456,2434580646496709778339332,true⟩,⟨(-3761840691219738526600433),(-3525729856023330594639060),true⟩⟩
  | 5,5 => ⟨⟨2289236359605016597674366,2500202916556226641632251,true⟩,⟨(-3514225885438275286243534),(-3292229310598227406629247),true⟩⟩
  | 5,6 => ⟨⟨2332488818875025546800048,2534740011655009628139992,true⟩,⟨(-3329474384073654971105960),(-3117942489951186313602133),true⟩⟩
  | 5,7 => ⟨⟨2351923143756487435681204,2549126955987192817864268,true⟩,⟨(-3222996519417890702381534),(-3017476268265804314760494),true⟩⟩
  | 6,0 => ⟨⟨526599069359332547945246,852403722989114772401880,true⟩,⟨(-5678417821836246069126539),(-5316973275525429051489090),true⟩⟩
  | 6,1 => ⟨⟨45000856838252560951614,393837661007689447638513,true⟩,⟨(-5895341942224120263801096),(-5511032691903577615107000),true⟩⟩
  | 6,2 => ⟨⟨(-385968995672527209778345),(-17920735365488388327684),true⟩,⟨(-6026668944809998393724740),(-5625051794280356884757221),true⟩⟩
  | 6,3 => ⟨⟨(-665842940723111944643960),(-285722308836514835830637),true⟩,⟨(-6083661757835978447839616),(-5672218904721177866135756),true⟩⟩
  | 6,4 => ⟨⟨966459676500438418941261,1268781413499318817036638,true⟩,⟨(-5402359205576589081058589),(-5065541452247770210890360),true⟩⟩
  | 6,5 => ⟨⟨1306790934359351950756829,1593220865572197000674402,true⟩,⟨(-5122125146000417554306852),(-4804845390598587703454938),true⟩⟩
  | 6,6 => ⟨⟨1531831597183605408844253,1807362367166961321729864,true⟩,⟨(-4893148507485883290532683),(-4590192628195933612765096),true⟩⟩
  | 6,7 => ⟨⟨1650714413583946263712869,1919672807283489225800805,true⟩,⟨(-4753859712444621986293167),(-4459440052694974552109140),true⟩⟩
  | 7,0 => ⟨⟨(-3049917574249176309335730),(-2592458076550439614640453),true⟩,⟨(-5719364578793815329003530),(-5267529897344469267721083),true⟩⟩
  | 7,1 => ⟨⟨(-3702359918156657510857276),(-3233280201350042865072964),true⟩,⟨(-5300978475353171084118231),(-4854996747301693678163167),true⟩⟩
  | 7,2 => ⟨⟨(-4165959443650464655031579),(-3693041252432688640358161),true⟩,⟨(-4864513422485982463677050),(-4430425186954669827993754),true⟩⟩
  | 7,3 => ⟨⟨(-4412721134635439923464787),(-3940172525564157470656414),true⟩,⟨(-4559514684311618911014357),(-4135878355233003772076908),true⟩⟩
  | 7,4 => ⟨⟨(-2311750128065011135803524),(-1873208582920171931879810),true⟩,⟨(-6002326794759595992310116),(-5554159171980353089078611),true⟩⟩
  | 7,5 => ⟨⟨(-1626917153843955297871688),(-1210129158396223381167320),true⟩,⟨(-6122356176967995066107162),(-5685067721201036724927129),true⟩⟩
  | 7,6 => ⟨⟨(-1106350625126437645307890),(-708531921821024035362166),true⟩,⟨(-6131066717869864224292017),(-5706278952164503633421992),true⟩⟩
  | 7,7 => ⟨⟨(-806690281532012931083028),(-420742080167704628772885),true⟩,⟨(-6104353453447364036998463),(-5688365727896446855082077),true⟩⟩
  | 8,0 => ⟨⟨(-5084170852274026942947499),(-4687750634724553949020639),true⟩,⟨(-1719209194123871932634145),(-1442125304895092495496648),true⟩⟩
  | 8,1 => ⟨⟨(-4864318967068532071127602),(-4509790313417977027778648),true⟩,⟨(-945114534337372254503371),(-720829202482105258787360),true⟩⟩
  | 8,2 => ⟨⟨(-4587155435692443449307892),(-4269409155256014771099418),true⟩,⟨(-402275510541250620874187),(-218761643054973655984964),true⟩⟩
  | 8,3 => ⟨⟨(-4385310246679651740932943),(-4090890320135216610297581),true⟩,⟨(-112919415686490400482367),48512722016643611538833,true⟩⟩
  | 8,4 => ⟨⟨(-5126342893209595318170870),(-4693563852774852823321080),true⟩,⟨(-2609860919192513914138473),(-2278733289925455928697491),true⟩⟩
  | 8,5 => ⟨⟨(-4971867771478763789712183),(-4515337606621824725337766),true⟩,⟨(-3438266449890743903279586),(-3063227237754803978250796),true⟩⟩
  | 8,6 => ⟨⟨(-4721841251200870802687509),(-4253955147192083022941039),true⟩,⟨(-4056088258391875483723554),(-3652531997349752956013000),true⟩⟩
  | 8,7 => ⟨⟨(-4521791377793202492506215),(-4050210465427991219203100),true⟩,⟨(-4401201535347251553616711),(-3983533178299063502853009),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP553Value0_0 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP553Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value0_1 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP553Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value0_2 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP553Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value0_3 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP553Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value0_4 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP553Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value0_5 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP553Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value0_6 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP553Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value0_7 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP553Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP553Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 0 j)=sharedDiskP553Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP553Value0_0
  · exact sharedDiskP553Value0_1
  · exact sharedDiskP553Value0_2
  · exact sharedDiskP553Value0_3
  · exact sharedDiskP553Value0_4
  · exact sharedDiskP553Value0_5
  · exact sharedDiskP553Value0_6
  · exact sharedDiskP553Value0_7
private theorem sharedDiskP553Value1_0 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP553Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value1_1 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP553Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value1_2 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP553Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value1_3 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP553Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value1_4 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP553Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value1_5 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP553Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value1_6 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP553Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value1_7 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP553Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP553Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 1 j)=sharedDiskP553Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP553Value1_0
  · exact sharedDiskP553Value1_1
  · exact sharedDiskP553Value1_2
  · exact sharedDiskP553Value1_3
  · exact sharedDiskP553Value1_4
  · exact sharedDiskP553Value1_5
  · exact sharedDiskP553Value1_6
  · exact sharedDiskP553Value1_7
private theorem sharedDiskP553Value2_0 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP553Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value2_1 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP553Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value2_2 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP553Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value2_3 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP553Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value2_4 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP553Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value2_5 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP553Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value2_6 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP553Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value2_7 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP553Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP553Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 2 j)=sharedDiskP553Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP553Value2_0
  · exact sharedDiskP553Value2_1
  · exact sharedDiskP553Value2_2
  · exact sharedDiskP553Value2_3
  · exact sharedDiskP553Value2_4
  · exact sharedDiskP553Value2_5
  · exact sharedDiskP553Value2_6
  · exact sharedDiskP553Value2_7
private theorem sharedDiskP553Value3_0 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP553Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value3_1 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP553Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value3_2 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP553Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value3_3 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP553Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value3_4 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP553Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value3_5 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP553Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value3_6 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP553Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value3_7 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP553Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP553Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 3 j)=sharedDiskP553Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP553Value3_0
  · exact sharedDiskP553Value3_1
  · exact sharedDiskP553Value3_2
  · exact sharedDiskP553Value3_3
  · exact sharedDiskP553Value3_4
  · exact sharedDiskP553Value3_5
  · exact sharedDiskP553Value3_6
  · exact sharedDiskP553Value3_7
private theorem sharedDiskP553Value4_0 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP553Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value4_1 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP553Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value4_2 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP553Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value4_3 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP553Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value4_4 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP553Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value4_5 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP553Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value4_6 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP553Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value4_7 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP553Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP553Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 4 j)=sharedDiskP553Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP553Value4_0
  · exact sharedDiskP553Value4_1
  · exact sharedDiskP553Value4_2
  · exact sharedDiskP553Value4_3
  · exact sharedDiskP553Value4_4
  · exact sharedDiskP553Value4_5
  · exact sharedDiskP553Value4_6
  · exact sharedDiskP553Value4_7
private theorem sharedDiskP553Value5_0 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP553Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value5_1 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP553Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value5_2 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP553Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value5_3 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP553Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value5_4 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP553Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value5_5 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP553Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value5_6 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP553Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value5_7 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP553Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP553Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 5 j)=sharedDiskP553Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP553Value5_0
  · exact sharedDiskP553Value5_1
  · exact sharedDiskP553Value5_2
  · exact sharedDiskP553Value5_3
  · exact sharedDiskP553Value5_4
  · exact sharedDiskP553Value5_5
  · exact sharedDiskP553Value5_6
  · exact sharedDiskP553Value5_7
private theorem sharedDiskP553Value6_0 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP553Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value6_1 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP553Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value6_2 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP553Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value6_3 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP553Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value6_4 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP553Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value6_5 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP553Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value6_6 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP553Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value6_7 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP553Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP553Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 6 j)=sharedDiskP553Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP553Value6_0
  · exact sharedDiskP553Value6_1
  · exact sharedDiskP553Value6_2
  · exact sharedDiskP553Value6_3
  · exact sharedDiskP553Value6_4
  · exact sharedDiskP553Value6_5
  · exact sharedDiskP553Value6_6
  · exact sharedDiskP553Value6_7
private theorem sharedDiskP553Value7_0 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP553Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value7_1 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP553Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value7_2 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP553Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value7_3 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP553Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value7_4 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP553Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value7_5 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP553Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value7_6 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP553Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value7_7 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP553Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP553Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 7 j)=sharedDiskP553Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP553Value7_0
  · exact sharedDiskP553Value7_1
  · exact sharedDiskP553Value7_2
  · exact sharedDiskP553Value7_3
  · exact sharedDiskP553Value7_4
  · exact sharedDiskP553Value7_5
  · exact sharedDiskP553Value7_6
  · exact sharedDiskP553Value7_7
private theorem sharedDiskP553Value8_0 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP553Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value8_1 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP553Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value8_2 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP553Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value8_3 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP553Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value8_4 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP553Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value8_5 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP553Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value8_6 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP553Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP553Value8_7 : truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP553Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP553Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points 8 j)=sharedDiskP553Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP553Value8_0
  · exact sharedDiskP553Value8_1
  · exact sharedDiskP553Value8_2
  · exact sharedDiskP553Value8_3
  · exact sharedDiskP553Value8_4
  · exact sharedDiskP553Value8_5
  · exact sharedDiskP553Value8_6
  · exact sharedDiskP553Value8_7
theorem sharedDiskP553Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP553Params (sharedChord521Gauss8Points i j)=sharedDiskP553Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP553Values0_eq
  · exact sharedDiskP553Values1_eq
  · exact sharedDiskP553Values2_eq
  · exact sharedDiskP553Values3_eq
  · exact sharedDiskP553Values4_eq
  · exact sharedDiskP553Values5_eq
  · exact sharedDiskP553Values6_eq
  · exact sharedDiskP553Values7_eq
  · exact sharedDiskP553Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP553Box : HorizontalRectangle := ⟨(27/32),(169/200),(966942670134869/1649267441664000),(968553282870869/1649267441664000),(246555312316481544548755072643467/5192296858534827628530496329220096),(2068767604439530208272863545291147/5192296858534827628530496329220096),(-2084015381228269816734038195556265/649037107316853453566312041152512),(-1849189362518181006198123856514985/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP553Grid : CGrid := momentChordGrid sharedDiskP553Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP553Columns : containedInReported sharedDiskP553Grid.re sharedDiskP553Box.reLo sharedDiskP553Box.reHi=true ∧ containedInReported sharedDiskP553Grid.im sharedDiskP553Box.imLo sharedDiskP553Box.imHi=true := by
  rw [sharedDiskP553Grid,momentChordGrid_eq_tabulated sharedDiskP553Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP553Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP553Values_eq]
  decide +kernel
theorem sharedDiskP553Sound : sharedDiskP553Box.Sound := by
  intro t a tl tu al au
  change (((27/32):ℚ):ℝ)≤t at tl
  change t≤(((169/200):ℚ):ℝ) at tu
  change (((966942670134869/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((968553282870869/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP553Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(27/32))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((169/200):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(966942670134869/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((968553282870869/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP553Columns.1 sharedDiskP553Columns.2
def sharedDiskP553Rows : List SignRow := [positive_553.toSignRow]
theorem sharedDiskP553Rows_actual : ∀ r∈sharedDiskP553Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP553Rows.all (sharedDiskP553Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP553Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP554Params : ChordParams := ⟨⟨(-29521477054659314419056),(-29359799168472402862359),true⟩,⟨1850615962220977119529555,1857742835493535354203773,true⟩,⟨136004027094043068310689,136939201168791090915500,true⟩,⟨260030422891424585104775,261567884582751725838657,true⟩,⟨367814195189658697324633,368873696326307840482326,true⟩,⟨1151290301429039650701018,1151598465189973591089694,true⟩,⟨(-2140741584690001343924788),(-2137007475993293709173071),true⟩,⟨⟨1140130438701549248596326,1154635973609631470408405,true⟩,⟨(-95655784),95655784,true⟩⟩⟩
theorem sharedDiskP554Params_ok : chordParams (Grid.ofRats (169/200) (677/800)) (Grid.ofRats (193516448749849/329853488332800) (193838571297049/329853488332800))=sharedDiskP554Params := by decide +kernel
def sharedDiskP554Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3026258599555565814713651),(-2733305842309926923674920),true⟩,⟨(-216718438131258757017162),23284397209106354192925,true⟩⟩
  | 0,1 => ⟨⟨(-2705101705752798854003640),(-2434180701631695413843657),true⟩,⟨(-268763175932663727319906),(-40606479767042727134933),true⟩⟩
  | 0,2 => ⟨⟨(-2471726512705036239734729),(-2218460867862298172684490),true⟩,⟨(-315211453043342232495550),(-98215147020557216136007),true⟩⟩
  | 0,3 => ⟨⟨(-2339861639469691734192229),(-2096920265562900065309945),true⟩,⟨(-344534225660335105072536),(-134326128764533414586033),true⟩⟩
  | 0,4 => ⟨⟨(-3404076984626628780238653),(-3088889711082832423730651),true⟩,⟨(-174025806493052391615432),74297241532085160833859,true⟩⟩
  | 0,5 => ⟨⟨(-3786285901491048349700228),(-3452871490945822027919833),true⟩,⟨(-152004313865361101135893),98622886562831042540705,true⟩⟩
  | 0,6 => ⟨⟨(-4107820507847872645345140),(-3762386063340186082538060),true⟩,⟨(-150411174340757887956751),97645847336295964624320,true⟩⟩
  | 0,7 => ⟨⟨(-4308923026130893295912523),(-3957396329336321239878849),true⟩,⟨(-159101198522493105943972),86310522262026510648740,true⟩⟩
  | 1,0 => ⟨⟨(-1536232504832457339285626),(-1361797181940194089421598),true⟩,⟨(-561502492265323243918887),(-402592245303010115828958),true⟩⟩
  | 1,1 => ⟨⟨(-1358807795802613218295137),(-1199964985466894171518752),true⟩,⟨(-614785378423657345282743),(-468518082354301148564938),true⟩⟩
  | 1,2 => ⟨⟨(-1229641838866467225237575),(-1082012313289138213123322),true⟩,⟨(-653583313646498240721130),(-516536906986639988509226),true⟩⟩
  | 1,3 => ⟨⟨(-1156073423356214570117373),(-1014741315741639078543783),true⟩,⟨(-675463532594886123260571),(-543633807358162477924020),true⟩⟩
  | 1,4 => ⟨⟨(-1747034432155262124242561),(-1554048858368737977940171),true⟩,⟨(-499607916923547927437151),(-326008521203539885446838),true⟩⟩
  | 1,5 => ⟨⟨(-1965549604564072189351914),(-1753617057444768410105618),true⟩,⟨(-438545973486188727207059),(-250462578635037959518352),true⟩⟩
  | 1,6 => ⟨⟨(-2155621233168753735231303),(-1927661354722704968031753),true⟩,⟨(-388933405356435425331545),(-189127625317879245713330),true⟩⟩
  | 1,7 => ⟨⟨(-2278157467647930252457484),(-2040165301531038503653239),true⟩,⟨(-358972301385822356089797),(-152133694549241047266610),true⟩⟩
  | 2,0 => ⟨⟨(-334899138774111583066254),(-250690051123924952985421),true⟩,⟨(-876819413260148505434461),(-791872523317977642665664),true⟩⟩
  | 2,1 => ⟨⟨(-158611632873058099635283),(-81710882076991097223056),true⟩,⟨(-902160850068354918158846),(-822986371854744273331642),true⟩⟩
  | 2,2 => ⟨⟨(-29425955581408602234995),43072384725865858818654,true⟩,⟨(-915592504079237951887006),(-840027258623146955583824),true⟩⟩
  | 2,3 => ⟨⟨44725802460426211677950,115176211238716395729955,true⟩,⟨(-921461832090195750993532),(-847739802634505403287272),true⟩⟩
  | 2,4 => ⟨⟨(-545171704262988088050925),(-450375735875391380711569),true⟩,⟨(-836138127563703315934772),(-743011027699364544457536),true⟩⟩
  | 2,5 => ⟨⟨(-768779292783394681982252),(-658837521302818395157741),true⟩,⟨(-783236110037654398267618),(-677700409751079575665795),true⟩⟩
  | 2,6 => ⟨⟨(-970123481219894211650052),(-844294369547529962235513),true⟩,⟨(-729232785563983577458123),(-610338345927722975101886),true⟩⟩
  | 2,7 => ⟨⟨(-1104422638443599728686857),(-967462066872294566004620),true⟩,⟨(-690659789543492252393326),(-562465241401954529238971),true⟩⟩
  | 3,0 => ⟨⟨941520513439225607290659,1010762458039852914422928,true⟩,⟨(-956429115889810094123883),(-887225545178408731857110),true⟩⟩
  | 3,1 => ⟨⟨1161880487181150557893572,1234625111708800285965396,true⟩,⟨(-987707903587445934332313),(-916024623826549129172877),true⟩⟩
  | 3,2 => ⟨⟨1332394924212119131035446,1408745714485520652085287,true⟩,⟨(-1030944470690782239573505),(-956341672854907030406222),true⟩⟩
  | 3,3 => ⟨⟨1434326794061476604450059,1513261918754350530660561,true⟩,⟨(-1067331601368250873055137),(-990500612598607864114366),true⟩⟩
  | 3,4 => ⟨⟨694134532159259230817023,760822311750931091337970,true⟩,⟨(-941979710897012676541632),(-874064656228362447196165),true⟩⟩
  | 3,5 => ⟨⟨447322695778351869784051,512853133087192046120249,true⟩,⟨(-936643265466875575158473),(-868588538800741871243041),true⟩⟩
  | 3,6 => ⟨⟨235154240181744091602898,301486356575359154107713,true⟩,⟨(-931243611434913948740798),(-861517004311076605814097),true⟩⟩
  | 3,7 => ⟨⟨97123654510315922274468,166298511875650634726687,true⟩,⟨(-924863895655957060064223),(-852346232735525005670793),true⟩⟩
  | 4,0 => ⟨⟨2166674327213731540657767,2291776538482416524191652,true⟩,⟨(-1787253410064251350366819),(-1663411943806540878484637),true⟩⟩
  | 4,1 => ⟨⟨2320958541273510821784441,2469941820723469298630072,true⟩,⟨(-2240144002045320867317597),(-2090126533287980653182144),true⟩⟩
  | 4,2 => ⟨⟨2375905571992978642093745,2549550955593099527636517,true⟩,⟨(-2735572641188296113762686),(-2557554456234733695453215),true⟩⟩
  | 4,3 => ⟨⟨2354705465829195235549088,2546224965588533644562950,true⟩,⟨(-3106113421393254854159661),(-2907239928264430807912448),true⟩⟩
  | 4,4 => ⟨⟨1958178701554841089377785,2064343712790981587947435,true⟩,⟨(-1457878735830981439036559),(-1354021957219365467702347),true⟩⟩
  | 4,5 => ⟨⟨1750957253056771503795768,1843918189172223407197094,true⟩,⟨(-1252625055714887611974152),(-1162195795787705698224470),true⟩⟩
  | 4,6 => ⟨⟨1584417996692474208913341,1669163953342108227534690,true⟩,⟨(-1139937911448496652072128),(-1057591791333880047907087),true⟩⟩
  | 4,7 => ⟨⟨1483524227170865782959617,1564078799133606715899567,true⟩,⟨(-1088424188980200077373345),(-1010101653788438817401623),true⟩⟩
  | 5,0 => ⟨⟨2076771609310602898290211,2312722426504238877455203,true⟩,⟨(-4049587634458582105178050),(-3796912995726061158286918),true⟩⟩
  | 5,1 => ⟨⟨1930172360180126298615339,2179010960378604835539159,true⟩,⟨(-4325455688213598195966876),(-4056645943767569116971391),true⟩⟩
  | 5,2 => ⟨⟨1784444426326021401036079,2043837236583282649516578,true⟩,⟨(-4550927080858392946028949),(-4268717130554159676236677),true⟩⟩
  | 5,3 => ⟨⟨1682385895153767449895078,1948255773492548817600936,true⟩,⟨(-4688820028114257991388495),(-4398299741156400522507747),true⟩⟩
  | 5,4 => ⟨⟨2194229756724547374223249,2417011232273931557660004,true⟩,⟨(-3768000078583392544715624),(-3531563323083587335171812),true⟩⟩
  | 5,5 => ⟨⟨2272577125693670434880301,2483757213571672833235545,true⟩,⟨(-3520923934065376000277162),(-3298587455830089776994419),true⟩⟩
  | 5,6 => ⟨⟨2316655005259272528861313,2519127508470089998442359,true⟩,⟨(-3336470865708869928581295),(-3124593103189255868218113),true⟩⟩
  | 5,7 => ⟨⟨2336562234791364616824419,2533990560892380404758387,true⟩,⟨(-3230126426203015843123732),(-3024258506274225164088719),true⟩⟩
  | 6,0 => ⟨⟨502027749075172225352811,828145257967320076172839,true⟩,⟨(-5672788487932075787329900),(-5311198778627042205513764),true⟩⟩
  | 6,1 => ⟨⟨20649266431334269060743,369699480075711580989648,true⟩,⟨(-5886523024422063866232718),(-5502217782486276779831450),true⟩⟩
  | 6,2 => ⟨⟨(-409694365466346174616594),(-41448537590454789582796),true⟩,⟨(-6015137813626125906512618),(-5613663475560993391691211),true⟩⟩
  | 6,3 => ⟨⟨(-688918138658092137096288),(-308670215731577289070937),true⟩,⟨(-6070451765551536733497879),(-5659243608274732612942658),true⟩⟩
  | 6,4 => ⟨⟨942253980263048493805598,1244733917071048847906192,true⟩,⟨(-5399754956170127105127140),(-5062806830760912357623489),true⟩⟩
  | 6,5 => ⟨⟨1283552169125049327480236,1569979406284762851136888,true⟩,⟨(-5121784340392891971445002),(-4804417961944196201169082),true⟩⟩
  | 6,6 => ⟨⟨1509353311497989994972154,1784932974342477543967782,true⟩,⟨(-4894428034549987677651844),(-4591320108577257572454872),true⟩⟩
  | 6,7 => ⟨⟨1628748012066490080591392,1897782379105369805413045,true⟩,⟨(-4755997751608270844401205),(-4461392479541646510425865),true⟩⟩
  | 7,0 => ⟨⟨(-3061396445326626593746137),(-2604515371555430217843725),true⟩,⟨(-5695771718946426594800953),(-5244930597543020124253158),true⟩⟩
  | 7,1 => ⟨⟨(-3708808670337855380739261),(-3240520297007190919191333),true⟩,⟨(-5276485626048172006740036),(-4831660473793196322637616),true⟩⟩
  | 7,2 => ⟨⟨(-4168258359870751356278393),(-3696280992367431526585187),true⟩,⟨(-4840328565795030042065426),(-4407479907512660194790554),true⟩⟩
  | 7,3 => ⟨⟨(-4412566375188449716475137),(-3941034784693379481542147),true⟩,⟨(-4535985162864605371300511),(-4113613437444794459825480),true⟩⟩
  | 7,4 => ⟨⟨(-2327933856701996849702867),(-1889736026866639740594317),true⟩,⟨(-5981003529702923225072247),(-5533609748644447556873950),true⟩⟩
  | 7,5 => ⟨⟨(-1646579573419144275997542),(-1229928809043931004821784),true⟩,⟨(-6103987097372329242722311),(-5667251688066825669191369),true⟩⟩
  | 7,6 => ⟨⟨(-1128081404215137399632408),(-730252510485039188350701),true⟩,⟨(-6115365457596003066983057),(-5690958390952429542712435),true⟩⟩
  | 7,7 => ⟨⟨(-829377402951248449408055),(-443338525666643174918129),true⟩,⟨(-6090325780023142783901487),(-5674619316568697696249133),true⟩⟩
  | 8,0 => ⟨⟨(-5073080747633842896780753),(-4677682446756913370170325),true⟩,⟨(-1709314991263370840695187),(-1433020100549328961605267),true⟩⟩
  | 8,1 => ⟨⟨(-4853634586877806240585471),(-4499935458014963971630120),true⟩,⟨(-939818531154782890869166),(-716045867059402327602928),true⟩⟩
  | 8,2 => ⟨⟨(-4577735752033067507329689),(-4260636726211564303700745),true⟩,⟨(-400102134380940104385741),(-216896058661459316066308),true⟩⟩
  | 8,3 => ⟨⟨(-4376954321300231550947103),(-4083062311742299900078034),true⟩,⟨(-112309536005974272291977),48947462611095029805331,true⟩⟩
  | 8,4 => ⟨⟨(-5116602472458601568186887),(-4684962954063138280799067),true⟩,⟨(-2594842804834703312197068),(-2264756296595591846393979),true⟩⟩
  | 8,5 => ⟨⟨(-4965044656826539990120406),(-4509669337785568234692946),true⟩,⟨(-3418986066280521066960720),(-3045148296029504772636652),true⟩⟩
  | 8,6 => ⟨⟨(-4718273818859787969993292),(-4251491507808860082259870),true⟩,⟨(-4034176662461716995941322),(-3631882745740374824273900),true⟩⟩
  | 8,7 => ⟨⟨(-4520483233192668046158437),(-4049951478273077666257147),true⟩,⟨(-4378117608424511733085743),(-3961718458481258630611925),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP554Value0_0 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP554Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value0_1 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP554Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value0_2 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP554Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value0_3 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP554Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value0_4 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP554Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value0_5 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP554Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value0_6 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP554Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value0_7 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP554Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP554Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 0 j)=sharedDiskP554Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP554Value0_0
  · exact sharedDiskP554Value0_1
  · exact sharedDiskP554Value0_2
  · exact sharedDiskP554Value0_3
  · exact sharedDiskP554Value0_4
  · exact sharedDiskP554Value0_5
  · exact sharedDiskP554Value0_6
  · exact sharedDiskP554Value0_7
private theorem sharedDiskP554Value1_0 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP554Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value1_1 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP554Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value1_2 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP554Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value1_3 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP554Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value1_4 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP554Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value1_5 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP554Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value1_6 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP554Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value1_7 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP554Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP554Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 1 j)=sharedDiskP554Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP554Value1_0
  · exact sharedDiskP554Value1_1
  · exact sharedDiskP554Value1_2
  · exact sharedDiskP554Value1_3
  · exact sharedDiskP554Value1_4
  · exact sharedDiskP554Value1_5
  · exact sharedDiskP554Value1_6
  · exact sharedDiskP554Value1_7
private theorem sharedDiskP554Value2_0 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP554Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value2_1 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP554Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value2_2 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP554Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value2_3 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP554Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value2_4 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP554Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value2_5 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP554Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value2_6 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP554Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value2_7 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP554Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP554Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 2 j)=sharedDiskP554Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP554Value2_0
  · exact sharedDiskP554Value2_1
  · exact sharedDiskP554Value2_2
  · exact sharedDiskP554Value2_3
  · exact sharedDiskP554Value2_4
  · exact sharedDiskP554Value2_5
  · exact sharedDiskP554Value2_6
  · exact sharedDiskP554Value2_7
private theorem sharedDiskP554Value3_0 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP554Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value3_1 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP554Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value3_2 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP554Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value3_3 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP554Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value3_4 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP554Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value3_5 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP554Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value3_6 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP554Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value3_7 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP554Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP554Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 3 j)=sharedDiskP554Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP554Value3_0
  · exact sharedDiskP554Value3_1
  · exact sharedDiskP554Value3_2
  · exact sharedDiskP554Value3_3
  · exact sharedDiskP554Value3_4
  · exact sharedDiskP554Value3_5
  · exact sharedDiskP554Value3_6
  · exact sharedDiskP554Value3_7
private theorem sharedDiskP554Value4_0 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP554Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value4_1 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP554Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value4_2 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP554Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value4_3 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP554Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value4_4 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP554Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value4_5 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP554Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value4_6 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP554Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value4_7 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP554Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP554Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 4 j)=sharedDiskP554Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP554Value4_0
  · exact sharedDiskP554Value4_1
  · exact sharedDiskP554Value4_2
  · exact sharedDiskP554Value4_3
  · exact sharedDiskP554Value4_4
  · exact sharedDiskP554Value4_5
  · exact sharedDiskP554Value4_6
  · exact sharedDiskP554Value4_7
private theorem sharedDiskP554Value5_0 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP554Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value5_1 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP554Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value5_2 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP554Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value5_3 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP554Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value5_4 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP554Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value5_5 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP554Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value5_6 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP554Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value5_7 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP554Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP554Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 5 j)=sharedDiskP554Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP554Value5_0
  · exact sharedDiskP554Value5_1
  · exact sharedDiskP554Value5_2
  · exact sharedDiskP554Value5_3
  · exact sharedDiskP554Value5_4
  · exact sharedDiskP554Value5_5
  · exact sharedDiskP554Value5_6
  · exact sharedDiskP554Value5_7
private theorem sharedDiskP554Value6_0 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP554Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value6_1 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP554Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value6_2 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP554Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value6_3 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP554Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value6_4 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP554Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value6_5 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP554Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value6_6 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP554Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value6_7 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP554Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP554Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 6 j)=sharedDiskP554Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP554Value6_0
  · exact sharedDiskP554Value6_1
  · exact sharedDiskP554Value6_2
  · exact sharedDiskP554Value6_3
  · exact sharedDiskP554Value6_4
  · exact sharedDiskP554Value6_5
  · exact sharedDiskP554Value6_6
  · exact sharedDiskP554Value6_7
private theorem sharedDiskP554Value7_0 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP554Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value7_1 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP554Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value7_2 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP554Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value7_3 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP554Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value7_4 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP554Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value7_5 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP554Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value7_6 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP554Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value7_7 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP554Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP554Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 7 j)=sharedDiskP554Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP554Value7_0
  · exact sharedDiskP554Value7_1
  · exact sharedDiskP554Value7_2
  · exact sharedDiskP554Value7_3
  · exact sharedDiskP554Value7_4
  · exact sharedDiskP554Value7_5
  · exact sharedDiskP554Value7_6
  · exact sharedDiskP554Value7_7
private theorem sharedDiskP554Value8_0 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP554Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value8_1 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP554Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value8_2 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP554Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value8_3 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP554Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value8_4 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP554Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value8_5 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP554Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value8_6 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP554Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP554Value8_7 : truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP554Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP554Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points 8 j)=sharedDiskP554Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP554Value8_0
  · exact sharedDiskP554Value8_1
  · exact sharedDiskP554Value8_2
  · exact sharedDiskP554Value8_3
  · exact sharedDiskP554Value8_4
  · exact sharedDiskP554Value8_5
  · exact sharedDiskP554Value8_6
  · exact sharedDiskP554Value8_7
theorem sharedDiskP554Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP554Params (sharedChord521Gauss8Points i j)=sharedDiskP554Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP554Values0_eq
  · exact sharedDiskP554Values1_eq
  · exact sharedDiskP554Values2_eq
  · exact sharedDiskP554Values3_eq
  · exact sharedDiskP554Values4_eq
  · exact sharedDiskP554Values5_eq
  · exact sharedDiskP554Values6_eq
  · exact sharedDiskP554Values7_eq
  · exact sharedDiskP554Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP554Box : HorizontalRectangle := ⟨(169/200),(677/800),(193516448749849/329853488332800),(193838571297049/329853488332800),(372490393594650223254694077621059/10384593717069655257060992658440192),(3988149617967815761154834414658371/10384593717069655257060992658440192),(-2082365962385133622938515923473437/649037107316853453566312041152512),(-1849327604951868082337536632624157/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP554Grid : CGrid := momentChordGrid sharedDiskP554Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP554Columns : containedInReported sharedDiskP554Grid.re sharedDiskP554Box.reLo sharedDiskP554Box.reHi=true ∧ containedInReported sharedDiskP554Grid.im sharedDiskP554Box.imLo sharedDiskP554Box.imHi=true := by
  rw [sharedDiskP554Grid,momentChordGrid_eq_tabulated sharedDiskP554Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP554Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP554Values_eq]
  decide +kernel
theorem sharedDiskP554Sound : sharedDiskP554Box.Sound := by
  intro t a tl tu al au
  change (((169/200):ℚ):ℝ)≤t at tl
  change t≤(((677/800):ℚ):ℝ) at tu
  change (((193516448749849/329853488332800):ℚ):ℝ)≤a at al
  change a≤(((193838571297049/329853488332800):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP554Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(169/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((677/800):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(193516448749849/329853488332800))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((193838571297049/329853488332800):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP554Columns.1 sharedDiskP554Columns.2
def sharedDiskP554Rows : List SignRow := [positive_554.toSignRow]
theorem sharedDiskP554Rows_actual : ∀ r∈sharedDiskP554Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP554Rows.all (sharedDiskP554Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP554Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP551Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP552Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP553Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP554Rows_actual
