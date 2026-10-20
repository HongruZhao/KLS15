import KLSConstantImprovement.WeightedOrbitBellmanTail
import KLSConstantImprovement.ExtendedSyntheticLossSlopes

/-! One extended conditional synthetic-budget scalar witness atCP13.068.
For14571/1250<=K<=3017/250, rawinitialenergy x=3017/250 gives normalized
Z1=x/K. Exactly56 capped payments min(z_(i+2),2Y_i) precede a constant
normalizedtail fromindex57. Every statement here concerns scalar recurrence,
cap and weightedbudget constraints. The generalN actual syntheticbudget
bridge is explicit in spend_le_budget and is NOT proved here. No admissible
law extremizer, universalKLSlowerbound or outermethodoptimum is claimed.
Root alone compiles this draft. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020
open KLSConstantImprovement.WeightedOrbitBellmanTail
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def x : ℝ := 3017/250

def y (i : ℕ) : ℝ :=
  if i=0 then 1 else
  if i=1 then (3017/250) else
  if i=2 then (143637/1000) else
  if i=3 then (424903/250) else
  if i=4 then (20044731/1000) else
  if i=5 then (58974561/250) else
  if i=6 then (346502766/125) else
  if i=7 then (16268706953/500) else
  if i=8 then (95396569279/250) else
  if i=9 then (4471994973321/1000) else
  if i=10 then (52379732314179/1000) else
  if i=11 then (613224224345301/1000) else
  if i=12 then (3588149851856661/500) else
  if i=13 then (83952098478981969/1000) else
  if i=14 then (981819867878746901/1000) else
  if i=15 then (5739674125669655691/500) else
  if i=16 then (134184052502522698311/1000) else
  if i=17 then (1568172203164255457787/1000) else
  if i=18 then (4580838843022526506011/250) else
  if i=19 then (107031721412572080536281/500) else
  if i=20 then (312552525856116584476403/125) else
  if i=21 then (3650331732493007097236383/125) else
  if i=22 then (85254156782137559479785729/250) else
  if i=23 then 3981779132018324518113502 else
  if i=24 then (46486954090342876174433692009/1000) else
  if i=25 then (67834532090217070123282283651/125) else
  if i=26 then (3167229039922071559659528317351/500) else
  if i=27 then (36966626277143475246629663712919/500) else
  if i=28 then (862848128120819281697772198169901/1000) else
  if i=29 then (10069209365874565053695717176041401/1000) else
  if i=30 then (58748244032754151326236690960853519/500) else
  if i=31 then (685479966096962527450661431243467713/500) else
  if i=32 then (15995458482901028160124772249778296391/1000) else
  if i=33 then (23326642811348508863875387359087692889/125) else
  if i=34 then (2177021815906856342482879324861651317483/1000) else
  if i=35 then (25395669202574817457562508478077874482009/1000) else
  if i=36 then (59246686047442070802333654868028209123341/200) else
  if i=37 then (3455310718083040414342089869739754631325381/1000) else
  if i=38 then (10075342415956841148331686389138686130137783/250) else
  if i=39 then (235019078716081155262958744329294331936792157/500) else
  if i=40 then (1096371943800048700462743900862405411842145753/200) else
  if i=41 then (63930048823596004173721295687379143562159169201/1000) else
  if i=42 then (745530194203312368832807321404812753299390509069/1000) else
  if i=43 then (8693791832085918355878391936907499387625406744647/1000) else
  if i=44 then (5068829810670734337178708359105536571921449446337/50) else
  if i=45 then (591045988864456901778290779725866430582446727860563/500) else
  if i=46 then (13783214648127864257577352115800694505274998047073133/1000) else
  if i=47 then (80353724457397127374387143738468971745665649632636727/500) else
  if i=48 then (1873735362659884377584674902929293629048337494793090853/1000) else
  if i=49 then (2730723711788782287329975726992052943500934860151454974/125) else
  if i=50 then (254691795730204200794904424143548181734814742640359518043/1000) else
  if i=51 then (1484637122069274556453920850004412724879180027073079335761/500) else
  if i=52 then (34615788483102161335427909342036321072637737647233760133757/1000) else
  if i=53 then (50442559048806677569870418895390941692994778313677257440789/125) else
  if i=54 then (4704238046892912446766330938014592237835481728023673607332443/1000) else
  if i=55 then (54837942990674597543905047969613614773361639336284452920560977/1000) else
  if i=56 then (639238653960125511655232589464872268955335539787913143544164089/1000) else
  (7451354483819832553281430620636280272879943498736203398856983439/1000)

def z (d : ℕ) : ℝ :=
  if d=2 then 2 else
  if d=3 then 10 else
  if d=4 then (265/4) else
  if d=5 then (1007/2) else
  if d=6 then (150043/36) else
  if d=7 then (16054601/441) else
  if d=8 then (1557296297/4704) else
  if d=9 then (393995963141/127008) else
  if d=10 then (53977446950317/1814400) else
  if d=11 then (829289866782143/2851200) else
  if d=12 then (10780768268167859/3732480) else
  if d=13 then (5422279898190935/186624) else
  if d=14 then (5406013058496362195/18289152) else
  if d=15 then (2498659235637018606529/823011840) else
  if d=16 then (6623945633673736325908379/210691031040) else
  if d=17 then (26106138673890607872697729/79594389504) else
  if d=18 then (88786977629901957375044976329/25788582199296) else
  if d=19 then (234387783050683006588415131417/6447145549824) else
  if d=20 then (66331742603343290864521482191011/171923881328640) else
  if d=21 then (155945926860460076822490004631066861/37909215832965120) else
  if d=22 then (36732354226859278095188327454463112441/834002748325232640) else
  if d=23 then (605285315303463756438103308923544331093/1278804214098690048) else
  if d=24 then (940008094666279213748374438758264346187429/184147806830211366912) else
  if d=25 then (940008094666279213748374438758264346187429/17020464251535360000) else
  if d=26 then (11786255340815654756998848732122852956042379/19668092023996416000) else
  if d=27 then (7790714780279147794376239011933205803944012519/1194836590457782272000) else
  if d=28 then (8328274100118408992188199503756597004416149382811/117093985864862662656000) else
  if d=29 then (5105232023372584712211366295802793963707099571663143/6565069474156633286246400) else
  if d=30 then (25173899107250215215914247204603577035039707987870958133/2954281263370484978810880000) else
  if d=31 then (33204372922463033869790892062872118109217374836001793777427/354883036762379508079656960000) else
  if d=32 then (24936484064769738436212959939216960700022248501837347126847677/24226681976311774418237915136000) else
  if d=33 then (27205704114663784633908339293685704123724273115504545715390815607/2398441515654865667405553598464000) else
  if d=34 then (49595998601032079387614902532389038617549349889564786839157456851561/396085484585289244502974279974912000) else
  if d=35 then (83966025631547310403232029987334642379511049363033184118693574449692773/60650589827122415564517936621158400000) else
  if d=36 then (1204996433838335451596782862348239452788363069408889225287371486927540985323/78603164415950650571615245861021286400000) else
  if d=37 then (1076061815417633558275927096076977831340008220982138078181622737826294099893439/6329866593260967096031839504925773004800000) else
  if d=38 then (454041451273850959826216185749954277571202416190200051199056288902810515728721077/240534930543916749649209901187179374182400000) else
  if d=39 then (40409689163372735424533240531745930703837015040927804556716009712350135899856175853/1925545417669986190612885577398420148060160000) else
  if d=40 then (5536127415382064753161053952849192506425671060607109224270093330591968618280296091861/23699020525169060807543207106442094129971200000) else
  if d=41 then (725232691415050482664098067823244218341762908939531308379382226307547888994718788033791/278587786732931407115245672349154966660710400000) else
  if d=42 then (1297441284941525313486071443335783906613413844092821510690714802864203173411551911792452099/44675350526990091104663033274900851017226649600000) else
  if d=43 then (8930288364252518732724629744480200629220127488890890458084189988114310442591711808867447797417/27534907708134892817507316175097224510284025036800000) else
  if d=44 then (32211550129858835068937739488340083669596999852429441882309673287128317766428304494584884205283119/8884596887158192082449027352498037775318312078540800000) else
  if d=45 then (364924651421170742495995650663404807892864411328173147084686288669876711975866261619152153161652455151/8995654348247669483479640194404263247509790979522560000000) else
  if d=46 then (364924651421170742495995650663404807892864411328173147084686288669876711975866261619152153161652455151/803224094897968968986535515712693941755874660843520000000) else
  if d=47 then (17477561496788411518265664034964345160996548721270590512502741187146648482078190529887478654614461203083/3431957496382231049306106294408783205684191732695040000000) else
  if d=48 then (451742532007490072512612618311723429376277794798680952976658351464179423316274990626001660785819978716086301/7907230071664660337601268902317836505896377752129372160000000) else
  if d=49 then (132360561878194591246195497165334964807249393876013519222160896979004571031668572253418486610245253763813286193/206361515239857059462833115592012233159317423726767636480000000) else
  if d=50 then (413097313621845319279376146653010425163425358287038193492364159471473266189837614002919096710575436996861266208353/57322643122182516517453643220003398099810395479657676800000000000) else
  if d=51 then (2416206187374173272465071081773457976780874920620886393736837968748647133944360204303073796660155730994641546052656697/29819238952159345092379385203045767691521367728517923471360000000000) else
  if d=52 then (2940522930034368872589991506518298357742324778395618741177731807967103562010286368636840810535409524620478761546083200249/3225248885065554765191754303561430233514951133516498602662297600000000) else
  if d=53 then (438692732222297258029604959283777077635255887222153912952685385011243167260666685222858496017046851154228784293299620082431/42734547727118600638790744522188950594073102519093606485275443200000000) else
  if d=54 then (7206405512215677057652320666154606054314348459398322328073762819579691508590971638155896514072028623910516239586032859094094037/62306970586138919731356905513351489966158583472838478255531596185600000000) else
  if d=55 then (245760047183091234697117091677870530270282225510860986354299533436126219517477905776030538819398392161220335318602478593685888943811/188478586023070232187354639177888257147629715005336396722983078461440000000000) else
  if d=56 then (16465923161267112724706845142417325528108909109227686085738068740220456707671019686994046100899692274801762466346366065776954559235337/1119448571530962591173379069056548436391982549728664659324384344801280000000000) else
  if d=57 then (3144991323802018530419007422201709175868801639862488042375971129382107231165164760215862805271841224487136631072155918563398320813949367/18943168796375507597512023934191280572070579708689747282004816334684160000000000) else
  0

def rawPayment (i : ℕ) : ℝ := min (z (i+2)) (2*y i)

def Z (K : ℝ) (i : ℕ) : ℝ :=
  if i ≤ 57 then y i/K^i else y 57/K^57

def c (K : ℝ) (i : ℕ) : ℝ :=
  if i < 56 then rawPayment i/K^(i+2) else 0

def syntheticSpend (K : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range 56,w i*(z (i+2)/K^(i+2))

/-- Evaluate the constant table tail one outer conditional at a time. -/
theorem y_tail_eval (i : ℕ) (hi : 57 ≤ i) :
    y i = (7451354483819832553281430620636280272879943498736203398856983439/1000 : ℝ) := by
  unfold y
  repeat' rw [if_neg (by omega)]

/-- Evaluate the zero table tail without splitting the symbolic table. -/
theorem z_tail_eval (d : ℕ) (hd : 58 ≤ d) : z d = 0 := by
  unfold z
  repeat' rw [if_neg (by omega)]

theorem y_positive (i : ℕ) : 0 < y i := by
  by_cases hi : i < 57
  · interval_cases i <;> norm_num [y]
  · rw [y_tail_eval i (by omega)]
    norm_num

theorem y_le_last (i : ℕ) : y i ≤ y 57 := by
  rw [y_tail_eval 57 (by omega)]
  by_cases hi : i < 57
  · interval_cases i <;> norm_num [y]
  · rw [y_tail_eval i (by omega)] <;> exact le_rfl

theorem z_nonnegative (d : ℕ) : 0 ≤ z d := by
  by_cases hd : d ≤ 57
  · interval_cases d <;> norm_num [z]
  · rw [z_tail_eval d (by omega)] <;> exact le_rfl

theorem z_two : z 2=2 := by norm_num [z]
theorem z_three : z 3=10 := by norm_num [z]
theorem z_four : z 4=(265/4 : ℝ) := by norm_num [z]

theorem z_coupling (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 57) :
    (d : ℝ)^2*z d ≤ ExtendedSyntheticLossSlopes.slope (d-1)*z (d-1) := by
  interval_cases d <;> norm_num [z,ExtendedSyntheticLossSlopes.slope]

theorem z_generator_admissible : z 2=2 ∧ z 3=10 ∧ z 4=(265/4 : ℝ) ∧
    (∀ d : ℕ,2 ≤ d → d ≤ 57 → 0 ≤ z d) ∧
    (∀ d : ℕ,3 ≤ d → d ≤ 57 →
      (d : ℝ)^2*z d ≤ ExtendedSyntheticLossSlopes.slope (d-1)*z (d-1)) := by
  exact ⟨z_two,z_three,z_four,fun d _ _=>z_nonnegative d,z_coupling⟩

theorem rawPayment_nonnegative (i : ℕ) : 0 ≤ rawPayment i :=
  le_min (z_nonnegative _) (mul_nonneg (by norm_num) (y_positive i).le)

theorem raw_recurrence (i : ℕ) (hi : i < 56) :
    (y (i+1))^2/y i-rawPayment i ≤ y (i+2) := by
  interval_cases i <;> norm_num [y,z,rawPayment]

theorem raw_cap (i : ℕ) (_hi : i < 56) : rawPayment i ≤ 2*y i :=
  min_le_right _ _

theorem raw_payment_le_synthetic (i : ℕ) : rawPayment i ≤ z (i+2) :=
  min_le_left _ _

theorem raw_upper (i : ℕ) (hi : i < 57) : y (i+1) ≤ x*y i := by
  interval_cases i <;> norm_num [y,x]

theorem last_ratio_bound : y 57 ≤ (14571/1250 : ℝ)*y 56 := by
  norm_num [y]

theorem K_positive {K : ℝ} (hK : (14571/1250 : ℝ) ≤ K) : 0 < K := by
  linarith

theorem Z_prefix (K : ℝ) (i : ℕ) (hi : i ≤ 57) : Z K i=y i/K^i := by
  simp only [Z,if_pos hi]

theorem Z_tail (K : ℝ) (i : ℕ) (hi : 57 ≤ i) : Z K i=y 57/K^57 := by
  by_cases he : i ≤ 57
  · have heq : i=57 := by omega
    subst i
    simp only [Z,le_refl,if_true]
  · simp only [Z,if_neg he]

theorem c_tail (K : ℝ) (i : ℕ) (hi : 56 ≤ i) : c K i=0 := by
  simp only [c,if_neg (show ¬i < 56 by omega)]

theorem Z_positive (K : ℝ) (hK : 0 < K) (i : ℕ) : 0 < Z K i := by
  by_cases hi : i ≤ 57
  · rw [Z_prefix K i hi]
    exact div_pos (y_positive i) (pow_pos hK i)
  · rw [Z_tail K i (by omega)]
    exact div_pos (y_positive 57) (pow_pos hK 57)

theorem c_nonnegative (K : ℝ) (hK : 0 < K) (i : ℕ) : 0 ≤ c K i := by
  by_cases hi : i < 56
  · rw [c,if_pos hi]
    exact div_nonneg (rawPayment_nonnegative _) (pow_nonneg hK.le _)
  · simp only [c,if_neg hi,le_refl]

theorem normalized_recurrence_identity (K x0 x1 u : ℝ) (i : ℕ)
    (hK : K≠0) (hx0 : x0≠0) :
    (x1/K^(i+1))^2/(x0/K^i)-u/K^(i+2)=
      (x1^2/x0-u)/K^(i+2) := by
  simp only [pow_add,pow_one]
  field_simp [hK,hx0,pow_ne_zero i hK] <;> ring

theorem last_step_nonincrease (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K) :
    Z K 57 ≤ Z K 56 := by
  have hK0 : 0 < K := K_positive hK
  have hraw : y 57 ≤ K*y 56 :=
    last_ratio_bound.trans (mul_le_mul_of_nonneg_right hK (y_positive 56).le)
  rw [Z_prefix K 57 (by omega),Z_prefix K 56 (by omega)]
  apply (div_le_iff₀ (pow_pos hK0 57)).mpr
  calc
    y 57 ≤ K*y 56 := hraw
    _ = (y 56/K^56)*K^57 := by
      rw [show K^57=K^56*K from pow_succ K 56]
      field_simp [ne_of_gt hK0,pow_ne_zero 56 (ne_of_gt hK0)] <;> ring

theorem normalized_recurrence (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K)
    (i : ℕ) : (Z K (i+1))^2/Z K i-c K i ≤ Z K (i+2) := by
  have hK0 : 0 < K := K_positive hK
  by_cases hi : i < 56
  · rw [Z_prefix K i (by omega),Z_prefix K (i+1) (by omega),
      Z_prefix K (i+2) (by omega),c,if_pos hi,
      normalized_recurrence_identity K (y i) (y (i+1)) (rawPayment i) i
        (ne_of_gt hK0) (ne_of_gt (y_positive i))]
    exact div_le_div_of_nonneg_right (raw_recurrence i hi) (pow_nonneg hK0.le _)
  · by_cases hi7 : i=56
    · subst i
      have hh : (Z K 57)^2/Z K 56 ≤ Z K 57 := by
        apply (div_le_iff₀ (Z_positive K hK0 56)).mpr
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_left (last_step_nonincrease K hK) (Z_positive K hK0 57).le
      simpa only [c_tail K 56 (by omega),sub_zero,
        Z_tail K 58 (by omega),Z_tail K 57 (by omega)] using hh
    · have hi8 : 57 ≤ i := by omega
      rw [Z_tail K i hi8,Z_tail K (i+1) (by omega),
        Z_tail K (i+2) (by omega),c_tail K i (by omega),sub_zero]
      have hv : y 57/K^57≠0 := ne_of_gt (div_pos (y_positive 57) (pow_pos hK0 57))
      have he : (y 57/K^57)^2/(y 57/K^57)=y 57/K^57 := by
        field_simp [hv] <;> ring
      exact he.le

theorem normalized_cap (K : ℝ) (hK : 0 < K) (i : ℕ) :
    c K i ≤ (2/K^2)*Z K i := by
  by_cases hi : i < 56
  · rw [c,if_pos hi,Z_prefix K i (by omega)]
    have he : (2/K^2)*(y i/K^i)=(2*y i)/K^(i+2) := by
      simp only [pow_add]
      field_simp [ne_of_gt hK,pow_ne_zero i (ne_of_gt hK)] <;> ring
    rw [he]
    exact div_le_div_of_nonneg_right (raw_cap i hi) (pow_nonneg hK.le _)
  · rw [c,if_neg hi]
    exact mul_nonneg (by positivity) (Z_positive K hK i).le

theorem normalized_upper (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K)
    (hKx : K ≤ x) (i : ℕ) : Z K (i+1) ≤ (x/K)*Z K i := by
  have hK0 : 0 < K := K_positive hK
  by_cases hi : i < 57
  · rw [Z_prefix K i (by omega),Z_prefix K (i+1) (by omega)]
    have he : (x/K)*(y i/K^i)=(x*y i)/K^(i+1) := by
      simp only [pow_add,pow_one]
      field_simp [ne_of_gt hK0,pow_ne_zero i (ne_of_gt hK0)] <;> ring
    rw [he]
    exact div_le_div_of_nonneg_right (raw_upper i hi) (pow_nonneg hK0.le _)
  · rw [Z_tail K i (by omega),Z_tail K (i+1) (by omega)]
    have hp : 1 ≤ x/K := (le_div_iff₀ hK0).mpr (by linarith)
    simpa only [mul_comm] using
      le_mul_of_one_le_right (div_pos (y_positive 57) (pow_pos hK0 57)).le hp

theorem Z_bounded (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K) (i : ℕ) :
    Z K i ≤ y 57 := by
  have hK1 : 1 ≤ K := by linarith
  by_cases hi : i ≤ 57
  · rw [Z_prefix K i hi]
    exact (div_le_self (y_positive i).le (one_le_pow₀ hK1)).trans (y_le_last i)
  · rw [Z_tail K i (by omega)]
    exact div_le_self (y_positive 57).le (one_le_pow₀ hK1)

theorem all_rate_envelope (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K) :
    ∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ i : ℕ,Z K i ≤ M*ρ^i := by
  intro ρ hρ
  refine ⟨y 57,fun i=>?_⟩
  exact (Z_bounded K hK i).trans
    (le_mul_of_one_le_right (y_positive 57).le (one_le_pow₀ hρ.le))

theorem spend_le_synthetic (K : ℝ) (hK : 0 < K) (w : ℕ → ℝ)
    (hw : ∀ i : ℕ,0 ≤ w i) (N : ℕ) :
    spend w (c K) N ≤ syntheticSpend K w := by
  have hnonneg (i : ℕ) : 0 ≤ w i*c K i := mul_nonneg (hw i) (c_nonnegative K hK i)
  have he : (∑ i ∈ Finset.range N ∩ Finset.range 56,w i*c K i)=
      (∑ i ∈ Finset.range N,w i*c K i) := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro i hi hnot
    have hi7 : 56 ≤ i := by
      by_contra hfail
      exact hnot (Finset.mem_inter.mpr ⟨hi,Finset.mem_range.mpr (by omega)⟩)
    rw [c_tail K i hi7,mul_zero]
  have hle : (∑ i ∈ Finset.range N,w i*c K i) ≤
      (∑ i ∈ Finset.range 56,w i*c K i) := by
    rw [←he]
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    intro i _ _
    exact hnonneg i
  unfold spend
  calc
    _ ≤ ∑ i ∈ Finset.range 56,w i*c K i := hle
    _ ≤ syntheticSpend K w := by
      unfold syntheticSpend
      apply Finset.sum_le_sum
      intro i hi
      rw [c,if_pos (Finset.mem_range.mp hi)]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (raw_payment_le_synthetic i) (pow_nonneg hK.le _)) (hw i)

theorem sum_Icc_two_fiftyseven (f : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 2 57,f d)=∑ i ∈ Finset.range 56,f (i+2) := by
  classical
  apply Finset.sum_bij (fun d _=>d-2)
  · intro d hd
    simp only [Finset.mem_Icc,Finset.mem_range] at hd ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro i hi
    refine ⟨i+2,?_,by omega⟩
    simp only [Finset.mem_Icc,Finset.mem_range] at hi ⊢
    omega
  · intro d hd
    have he : d-2+2=d := by
      have hd2 := (Finset.mem_Icc.mp hd).1
      omega
    rw [he]

theorem syntheticSpend_eq_Icc (K : ℝ) (t : ℕ → ℝ) :
    syntheticSpend K (fun i=>t (i+2))=
      ∑ d ∈ Finset.Icc 2 57,t d*z d/K^d := by
  rw [sum_Icc_two_fiftyseven]
  unfold syntheticSpend
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The analytic synthetic-budget bridge is an explicit premise here. -/
theorem spend_le_budget (K C : ℝ) (hK : 0 < K) (t : ℕ → ℝ)
    (ht : ∀ d : ℕ,2 ≤ d → 0 ≤ t d)
    (hbridge : (∑ d ∈ Finset.Icc 2 57,t d*z d/K^d) ≤ C) (N : ℕ) :
    spend (fun i=>t (i+2)) (c K) N ≤ C := by
  calc
    _ ≤ syntheticSpend K (fun i=>t (i+2)) :=
      spend_le_synthetic K hK (fun i=>t (i+2)) (fun i=>ht (i+2) (by omega)) N
    _ = _ := syntheticSpend_eq_Icc K t
    _ ≤ C := hbridge

/-- The uniform finite-payment witness, conditional only on a scalar
syntheticbudget bound when that bound is later supplied. -/
theorem uniform_scalar_orbit (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K)
    (hKx : K ≤ x) :
    Z K 0=1 ∧ Z K 1=x/K ∧ (∀ i : ℕ,0 < Z K i) ∧
      (∀ i : ℕ,0 ≤ c K i) ∧
      (∀ i : ℕ,(Z K (i+1))^2/Z K i-c K i ≤ Z K (i+2)) ∧
      (∀ i : ℕ,c K i ≤ (2/K^2)*Z K i) ∧
      (∀ i : ℕ,Z K (i+1) ≤ (x/K)*Z K i) ∧
      (∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ i : ℕ,Z K i ≤ M*ρ^i) := by
  exact ⟨by norm_num [Z,y],by norm_num [Z,y,x],
    Z_positive K (K_positive hK),c_nonnegative K (K_positive hK),
    normalized_recurrence K hK,normalized_cap K (K_positive hK),
    normalized_upper K hK hKx,all_rate_envelope K hK⟩

end KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020
#print axioms KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020.raw_recurrence
#print axioms KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020.normalized_recurrence
#print axioms KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020.normalized_cap
#print axioms KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020.spend_le_synthetic
#print axioms KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020.spend_le_budget
#print axioms KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020.uniform_scalar_orbit

#print axioms KLSConstantImprovement.SyntheticThirteen068FiniteOrbit20261020.z_generator_admissible
