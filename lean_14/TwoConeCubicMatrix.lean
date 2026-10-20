import CubicFourByFourPositivity

/-! Exact polynomial full-cubic slack for the two-cone family. The
Bernstein coefficients are integers and are checked by the kernel.
Actual exponential integrals are connected in a separate module. -/
noncomputable section
namespace KLSImprovement.TwoConeCubic
open KLSImprovement.CubicFourByFour
set_option maxHeartbeats 12000000
set_option maxRecDepth 5000
set_option linter.unusedVariables false

def m00 (d g:ℝ):ℝ :=
  -576*d^4*g^6+576*d^4*g^4-2232*d^3*g^6+2304*d^3*g^4-72*d^3*g^3-2556*d^2*g^6+2196*d^2*g^4-216*d^2*g^3+576*d^2*g^2-720*d*g^6-216*d*g^4-216*d*g^3+1152*d*g^2

def m01 (d g:ℝ):ℝ :=
  384*d^4*g^5-384*d^4*g^3+1116*d^3*g^5-1152*d^3*g^3+36*d^3*g^2+852*d^2*g^5-732*d^2*g^3+72*d^2*g^2-192*d^2*g+120*d*g^5+36*d*g^3+36*d*g^2-192*d*g

def m02 (d g:ℝ):ℝ :=
  -192*d^4*g^4+192*d^4*g^2-372*d^3*g^4+384*d^3*g^2-12*d^3*g-180*d^2*g^4+192*d^2*g^2-12*d^2*g

def m03 (d g:ℝ):ℝ :=
  0

def m11 (d g:ℝ):ℝ :=
  -192*d^4*g^4+256*d^4*g^2-240*d^3*g^4+512*d^3*g^2-16*d^3*g+80*d^2*g^4+256*d^2*g^2-16*d^2*g+64*d^2-24*d*g^4+280*d*g^2+64

def m12 (d g:ℝ):ℝ :=
  -128*d^4*g-264*d^3*g^3-128*d^3*g+4*d^3-256*d^2*g^3-140*d^2*g-140*d*g-4

def m13 (d g:ℝ):ℝ :=
  192*d^4*g^2+396*d^3*g^2+216*d^2*g^2+12*d*g^2

def m22 (d g:ℝ):ℝ :=
  192*d^4*g^2+64*d^4+528*d^3*g^2+212*d^2*g^2+140*d^2+144*d*g^2+64

def m23 (d g:ℝ):ℝ :=
  -384*d^4*g-420*d^3*g-228*d^2*g-192*d*g

def m33 (d g:ℝ):ℝ :=
  576*d^4+72*d^3+576*d^2

def slackQuadratic (d g x y z w:ℝ):ℝ :=
  quadratic (m00 d g) (m11 d g) (m22 d g) (m33 d g)
    (m01 d g) (m02 d g) (m03 d g) (m12 d g) (m13 d g) (m23 d g) x y z w

def p1 (d g:ℝ):ℝ :=
  32*(1-d)^3*(1-g)^3+
  122*(1-d)^3*g*(1-g)^2+
  168*(1-d)^3*g^2*(1-g)+
  98*(1-d)^3*g^3+
  112*d*(1-d)^2*(1-g)^3+
  424*d*(1-d)^2*g*(1-g)^2+
  643*d*(1-d)^2*g^2*(1-g)+
  462*d*(1-d)^2*g^3+
  128*d^2*(1-d)*(1-g)^3+
  480*d^2*(1-d)*g*(1-g)^2+
  840*d^2*(1-d)*g^2*(1-g)+
  752*d^2*(1-d)*g^3+
  48*d^3*(1-g)^3+
  178*d^3*g*(1-g)^2+
  381*d^3*g^2*(1-g)+
  420*d^3*g^3

theorem p1_pos {d g:ℝ} (hd:0  <  d) (hd1:d ≤ 1)
    (hg:0  <  g) (hg1:g ≤ 1):
    0  <  p1 d g := by
  have hdc : 0 ≤ 1-d := sub_nonneg.mpr hd1
  have hgc : 0 ≤ 1-g := sub_nonneg.mpr hg1
  unfold p1
  positivity

def p2 (d g:ℝ):ℝ :=
  512*(1-d)^7*(1-g)^7+
  4000*(1-d)^7*g*(1-g)^6+
  13568*(1-d)^7*g^2*(1-g)^5+
  26080*(1-d)^7*g^3*(1-g)^4+
  30720*(1-d)^7*g^4*(1-g)^3+
  22112*(1-d)^7*g^5*(1-g)^2+
  8960*(1-d)^7*g^6*(1-g)+
  1568*(1-d)^7*g^7+
  3584*d*(1-d)^6*(1-g)^7+
  28000*d*(1-d)^6*g*(1-g)^6+
  98279*d*(1-d)^6*g^2*(1-g)^5+
  201940*d*(1-d)^6*g^3*(1-g)^4+
  260958*d*(1-d)^6*g^4*(1-g)^3+
  210692*d*(1-d)^6*g^5*(1-g)^2+
  97767*d*(1-d)^6*g^6*(1-g)+
  19936*d*(1-d)^6*g^7+
  10752*d^2*(1-d)^5*(1-g)^7+
  84032*d^2*(1-d)^5*g*(1-g)^6+
  307198*d^2*(1-d)^5*g^2*(1-g)^5+
  677550*d^2*(1-d)^5*g^3*(1-g)^4+
  958994*d^2*(1-d)^5*g^4*(1-g)^3+
  864734*d^2*(1-d)^5*g^5*(1-g)^2+
  456898*d^2*(1-d)^5*g^6*(1-g)+
  108800*d^2*(1-d)^5*g^7+
  17920*d^3*(1-d)^4*(1-g)^7+
  140160*d^3*(1-d)^4*g*(1-g)^6+
  538007*d^3*(1-d)^4*g^2*(1-g)^5+
  1279160*d^3*(1-d)^4*g^3*(1-g)^4+
  1981247*d^3*(1-d)^4*g^4*(1-g)^3+
  1987484*d^3*(1-d)^4*g^5*(1-g)^2+
  1186771*d^3*(1-d)^4*g^6*(1-g)+
  330560*d^3*(1-d)^4*g^7+
  17920*d^4*(1-d)^3*(1-g)^7+
  140320*d^4*(1-d)^3*g*(1-g)^6+
  571768*d^4*(1-d)^3*g^2*(1-g)^5+
  1473190*d^4*(1-d)^3*g^3*(1-g)^4+
  2495590*d^4*(1-d)^3*g^4*(1-g)^3+
  2768150*d^4*(1-d)^3*g^5*(1-g)^2+
  1850236*d^4*(1-d)^3*g^6*(1-g)+
  604160*d^4*(1-d)^3*g^7+
  10752*d^5*(1-d)^2*(1-g)^7+
  84320*d^5*(1-d)^2*g*(1-g)^6+
  370240*d^5*(1-d)^2*g^2*(1-g)^5+
  1040220*d^5*(1-d)^2*g^3*(1-g)^4+
  1923803*d^5*(1-d)^2*g^4*(1-g)^3+
  2335736*d^5*(1-d)^2*g^5*(1-g)^2+
  1730228*d^5*(1-d)^2*g^6*(1-g)+
  664576*d^5*(1-d)^2*g^7+
  3584*d^6*(1-d)*(1-g)^7+
  28160*d^6*(1-d)*g*(1-g)^6+
  135912*d^6*(1-d)*g^2*(1-g)^5+
  418840*d^6*(1-d)*g^3*(1-g)^4+
  841562*d^6*(1-d)*g^4*(1-g)^3+
  1102624*d^6*(1-d)*g^5*(1-g)^2+
  898176*d^6*(1-d)*g^6*(1-g)+
  407552*d^6*(1-d)*g^7+
  512*d^7*(1-g)^7+
  4032*d^7*g*(1-g)^6+
  21920*d^7*g^2*(1-g)^5+
  74340*d^7*g^3*(1-g)^4+
  160858*d^7*g^4*(1-g)^3+
  223708*d^7*g^5*(1-g)^2+
  199760*d^7*g^6*(1-g)+
  107520*d^7*g^7

theorem p2_pos {d g:ℝ} (hd:0  <  d) (hd1:d ≤ 1)
    (hg:0  <  g) (hg1:g ≤ 1):
    0  <  p2 d g := by
  have hdc : 0 ≤ 1-d := sub_nonneg.mpr hd1
  have hgc : 0 ≤ 1-g := sub_nonneg.mpr hg1
  unfold p2
  positivity

def p3 (d g:ℝ):ℝ :=
  8160*(1-d)^9*(1-g)^9+
  80070*(1-d)^9*g*(1-g)^8+
  351900*(1-d)^9*g^2*(1-g)^7+
  911880*(1-d)^9*g^3*(1-g)^6+
  1537140*(1-d)^9*g^4*(1-g)^5+
  1747260*(1-d)^9*g^5*(1-g)^4+
  1337220*(1-d)^9*g^6*(1-g)^3+
  663000*(1-d)^9*g^7*(1-g)^2+
  192780*(1-d)^9*g^8*(1-g)+
  24990*(1-d)^9*g^9+
  73424*d*(1-d)^8*(1-g)^9+
  718236*d*(1-d)^8*g*(1-g)^8+
  3217913*d*(1-d)^8*g^2*(1-g)^7+
  8687644*d*(1-d)^8*g^3*(1-g)^6+
  15552451*d*(1-d)^8*g^4*(1-g)^5+
  19083438*d*(1-d)^8*g^5*(1-g)^4+
  15988447*d*(1-d)^8*g^6*(1-g)^3+
  8783072*d*(1-d)^8*g^7*(1-g)^2+
  2857845*d*(1-d)^8*g^8*(1-g)+
  417690*d*(1-d)^8*g^9+
  311520*d^2*(1-d)^7*(1-g)^9+
  3036560*d^2*(1-d)^7*g*(1-g)^8+
  13849582*d^2*(1-d)^7*g^2*(1-g)^7+
  38769084*d^2*(1-d)^7*g^3*(1-g)^6+
  73060642*d^2*(1-d)^7*g^4*(1-g)^5+
  95676628*d^2*(1-d)^7*g^5*(1-g)^4+
  86694374*d^2*(1-d)^7*g^6*(1-g)^3+
  52196064*d^2*(1-d)^7*g^7*(1-g)^2+
  18867818*d^2*(1-d)^7*g^8*(1-g)+
  3104880*d^2*(1-d)^7*g^9+
  810192*d^3*(1-d)^6*(1-g)^9+
  7868798*d^3*(1-d)^6*g*(1-g)^8+
  36505075*d^3*(1-d)^6*g^2*(1-g)^7+
  105585128*d^3*(1-d)^6*g^3*(1-g)^6+
  208168565*d^3*(1-d)^6*g^4*(1-g)^5+
  288588396*d^3*(1-d)^6*g^5*(1-g)^4+
  280128719*d^3*(1-d)^6*g^6*(1-g)^3+
  183058322*d^3*(1-d)^6*g^7*(1-g)^2+
  72919229*d^3*(1-d)^6*g^8*(1-g)+
  13475220*d^3*(1-d)^6*g^9+
  1410976*d^4*(1-d)^5*(1-g)^9+
  13657494*d^4*(1-d)^5*g*(1-g)^8+
  64429432*d^4*(1-d)^5*g^2*(1-g)^7+
  192069628*d^4*(1-d)^5*g^3*(1-g)^6+
  394454514*d^4*(1-d)^5*g^4*(1-g)^5+
  575532392*d^4*(1-d)^5*g^5*(1-g)^4+
  594164430*d^4*(1-d)^5*g^6*(1-g)^3+
  418118822*d^4*(1-d)^5*g^7*(1-g)^2+
  182065624*d^4*(1-d)^5*g^8*(1-g)+
  37638000*d^4*(1-d)^5*g^9+
  1693680*d^5*(1-d)^4*(1-g)^9+
  16347400*d^5*(1-d)^4*g*(1-g)^8+
  78391895*d^5*(1-d)^4*g^2*(1-g)^7+
  240251056*d^5*(1-d)^4*g^3*(1-g)^6+
  512142475*d^5*(1-d)^4*g^4*(1-g)^5+
  783403414*d^5*(1-d)^4*g^5*(1-g)^4+
  856387395*d^5*(1-d)^4*g^6*(1-g)^3+
  645515960*d^5*(1-d)^4*g^7*(1-g)^2+
  305076316*d^5*(1-d)^4*g^8*(1-g)+
  70180080*d^5*(1-d)^4*g^9+
  1391904*d^6*(1-d)^3*(1-g)^9+
  13406356*d^6*(1-d)^3*g*(1-g)^8+
  65282918*d^6*(1-d)^3*g^2*(1-g)^7+
  205003732*d^6*(1-d)^3*g^3*(1-g)^6+
  452215408*d^6*(1-d)^3*g^4*(1-g)^5+
  723989108*d^6*(1-d)^3*g^5*(1-g)^4+
  837070842*d^6*(1-d)^3*g^6*(1-g)^3+
  674149596*d^6*(1-d)^3*g^7*(1-g)^2+
  343848368*d^6*(1-d)^3*g^8*(1-g)+
  87377280*d^6*(1-d)^3*g^9+
  750320*d^7*(1-d)^2*(1-g)^9+
  7217310*d^7*(1-d)^2*g*(1-g)^8+
  35623637*d^7*(1-d)^2*g^2*(1-g)^7+
  114148632*d^7*(1-d)^2*g^3*(1-g)^6+
  260006753*d^7*(1-d)^2*g^4*(1-g)^5+
  436155628*d^7*(1-d)^2*g^5*(1-g)^4+
  534535393*d^7*(1-d)^2*g^6*(1-g)^3+
  460051104*d^7*(1-d)^2*g^7*(1-g)^2+
  252157520*d^7*(1-d)^2*g^8*(1-g)+
  70061760*d^7*(1-d)^2*g^9+
  239232*d^8*(1-d)*(1-g)^9+
  2299808*d^8*(1-d)*g*(1-g)^8+
  11478520*d^8*(1-d)*g^2*(1-g)^7+
  37363564*d^8*(1-d)*g^3*(1-g)^6+
  87861846*d^8*(1-d)*g^4*(1-g)^5+
  155180592*d^8*(1-d)*g^5*(1-g)^4+
  202732064*d^8*(1-d)*g^6*(1-g)^3+
  186858944*d^8*(1-d)*g^7*(1-g)^2+
  109619520*d^8*(1-d)*g^8*(1-g)+
  32835840*d^8*(1-d)*g^9+
  34176*d^9*(1-g)^9+
  328544*d^9*g*(1-g)^8+
  1653832*d^9*g^2*(1-g)^7+
  5445428*d^9*g^3*(1-g)^6+
  13263386*d^9*g^4*(1-g)^5+
  24919584*d^9*g^5*(1-g)^4+
  35016080*d^9*g^6*(1-g)^3+
  34643216*d^9*g^7*(1-g)^2+
  21619904*d^9*g^8*(1-g)+
  6854400*d^9*g^9

theorem p3_pos {d g:ℝ} (hd:0  <  d) (hd1:d ≤ 1)
    (hg:0  <  g) (hg1:g ≤ 1):
    0  <  p3 d g := by
  have hdc : 0 ≤ 1-d := sub_nonneg.mpr hd1
  have hgc : 0 ≤ 1-g := sub_nonneg.mpr hg1
  unfold p3
  positivity

def p4 (d g:ℝ):ℝ :=
  65280*(1-d)^6*(1-g)^8+
  640560*(1-d)^6*g*(1-g)^7+
  2749664*(1-d)^6*g^2*(1-g)^6+
  6783552*(1-d)^6*g^3*(1-g)^5+
  10563648*(1-d)^6*g^4*(1-g)^4+
  10648432*(1-d)^6*g^5*(1-g)^3+
  6778048*(1-d)^6*g^6*(1-g)^2+
  2483936*(1-d)^6*g^7*(1-g)+
  399840*(1-d)^6*g^8+
  399712*d*(1-d)^5*(1-g)^8+
  3904278*d*(1-d)^5*g*(1-g)^7+
  17100740*d*(1-d)^5*g^2*(1-g)^6+
  44253064*d*(1-d)^5*g^3*(1-g)^5+
  74194298*d*(1-d)^5*g^4*(1-g)^4+
  82342734*d*(1-d)^5*g^5*(1-g)^3+
  58854284*d*(1-d)^5*g^6*(1-g)^2+
  24660028*d*(1-d)^5*g^7*(1-g)+
  4608870*d*(1-d)^5*g^8+
  1227728*d^2*(1-d)^4*(1-g)^8+
  11936692*d^2*(1-d)^4*g*(1-g)^7+
  52943041*d^2*(1-d)^4*g^2*(1-g)^6+
  141120732*d^2*(1-d)^4*g^3*(1-g)^5+
  247484761*d^2*(1-d)^4*g^4*(1-g)^4+
  291870652*d^2*(1-d)^4*g^5*(1-g)^3+
  225860710*d^2*(1-d)^4*g^6*(1-g)^2+
  104686074*d^2*(1-d)^4*g^7*(1-g)+
  22256910*d^2*(1-d)^4*g^8+
  2237024*d^3*(1-d)^3*(1-g)^8+
  21650076*d^3*(1-d)^3*g*(1-g)^7+
  97136322*d^3*(1-d)^3*g^2*(1-g)^6+
  265777052*d^3*(1-d)^3*g^3*(1-g)^5+
  483952792*d^3*(1-d)^3*g^4*(1-g)^4+
  598654852*d^3*(1-d)^3*g^5*(1-g)^3+
  491274344*d^3*(1-d)^3*g^6*(1-g)^2+
  245060932*d^3*(1-d)^3*g^7*(1-g)+
  57736080*d^3*(1-d)^3*g^8+
  2570992*d^4*(1-d)^2*(1-g)^8+
  24788158*d^4*(1-d)^2*g*(1-g)^7+
  112197461*d^4*(1-d)^2*g^2*(1-g)^6+
  312992816*d^4*(1-d)^2*g^3*(1-g)^5+
  585406061*d^4*(1-d)^2*g^4*(1-g)^4+
  748324966*d^4*(1-d)^2*g^5*(1-g)^3+
  638790902*d^4*(1-d)^2*g^6*(1-g)^2+
  335052566*d^4*(1-d)^2*g^7*(1-g)+
  84968040*d^4*(1-d)^2*g^8+
  1742976*d^5*(1-d)*(1-g)^8+
  16755744*d^5*(1-d)*g*(1-g)^7+
  76355160*d^5*(1-d)*g^2*(1-g)^6+
  216125148*d^5*(1-d)*g^3*(1-g)^5+
  412115598*d^5*(1-d)*g^4*(1-g)^4+
  538797048*d^5*(1-d)*g^5*(1-g)^3+
  471784476*d^5*(1-d)*g^6*(1-g)^2+
  255026520*d^5*(1-d)*g^7*(1-g)+
  67320000*d^5*(1-d)*g^8+
  580992*d^6*(1-g)^8+
  5585248*d^6*g*(1-g)^7+
  25451720*d^6*g^2*(1-g)^6+
  72041716*d^6*g^3*(1-g)^5+
  137371866*d^6*g^4*(1-g)^4+
  179599016*d^6*g^5*(1-g)^3+
  157261492*d^6*g^6*(1-g)^2+
  85008840*d^6*g^7*(1-g)+
  22440000*d^6*g^8

theorem p4_pos {d g:ℝ} (hd:0  <  d) (hd1:d ≤ 1)
    (hg:0  <  g) (hg1:g ≤ 1):
    0  <  p4 d g := by
  have hdc : 0 ≤ 1-d := sub_nonneg.mpr hd1
  have hgc : 0 ≤ 1-g := sub_nonneg.mpr hg1
  unfold p4
  positivity

theorem minor1_factor (d g:ℝ):
    m00 d g=36*d*g^2*(1-g)*p1 d g := by
  simp only [m00,p1]
  ring

theorem minor2_factor (d g:ℝ):
    minorTwo (m00 d g) (m11 d g) (m01 d g)=144*d*g^2*(1-g)*p2 d g := by
  simp only [minorTwo,m00,m11,m01,p2]
  ring

theorem minor3_factor (d g:ℝ):
    minorThree (m00 d g) (m11 d g) (m22 d g) (m01 d g) (m02 d g) (m12 d g)=576*d*g^2*(1-g)*p3 d g := by
  simp only [minorThree,m00,m11,m22,m01,m02,m12,p3]
  ring

theorem minor4_factor (d g:ℝ):
    minorFour (m00 d g) (m11 d g) (m22 d g) (m33 d g) (m01 d g) (m02 d g) (m03 d g) (m12 d g) (m13 d g) (m23 d g)=41472*d^3*g^2*(1-g)^2*p4 d g := by
  simp only [minorFour,m00,m11,m22,m33,m01,m02,m03,m12,m13,m23,p4]
  ring

theorem slackQuadratic_nonneg_interior {d g:ℝ}
    (hd:0  <  d) (hd1:d ≤ 1) (hg:0  <  g) (hg1:g < 1) (x y z w:ℝ):
    0 ≤ slackQuadratic d g x y z w := by
  have hp1 := p1_pos hd hd1 hg hg1.le
  have h1 : 0  <  m00 d g := by
    rw [minor1_factor]
    positivity
  have hp2 := p2_pos hd hd1 hg hg1.le
  have h2 : 0  <  minorTwo (m00 d g) (m11 d g) (m01 d g) := by
    rw [minor2_factor]
    positivity
  have hp3 := p3_pos hd hd1 hg hg1.le
  have h3 : 0  <  minorThree (m00 d g) (m11 d g) (m22 d g) (m01 d g) (m02 d g) (m12 d g) := by
    rw [minor3_factor]
    positivity
  have hp4 := p4_pos hd hd1 hg hg1.le
  have h4 : 0  <  minorFour (m00 d g) (m11 d g) (m22 d g) (m33 d g) (m01 d g) (m02 d g) (m03 d g) (m12 d g) (m13 d g) (m23 d g) := by
    rw [minor4_factor]
    positivity
  exact quadratic_nonneg_of_leading_minors
    (m00 d g) (m11 d g) (m22 d g) (m33 d g)
    (m01 d g) (m02 d g) (m03 d g) (m12 d g) (m13 d g) (m23 d g)
    x y z w h1 h2 h3 h4.le

theorem slackQuadratic_nonneg_small_d {d g:ℝ}
    (hd:0  <  d) (hd1:d ≤ 1) (hg:0 ≤ g) (hg1:g ≤ 1) (x y z w:ℝ):
    0 ≤ slackQuadratic d g x y z w := by
  apply continuous_nonneg_on_Icc (f:=fun g=>slackQuadratic d g x y z w)
      (by unfold slackQuadratic quadratic m00 m11 m22 m33 m01 m02 m03 m12 m13 m23; fun_prop)
      (by norm_num : (0:ℝ) < 1) _ g ⟨hg,hg1⟩
  intro g hg
  exact slackQuadratic_nonneg_interior hd hd1 hg.1 hg.2 x y z w

theorem slackQuadratic_reciprocal (d g x y z w:ℝ) (hd:d≠0):
    slackQuadratic d g x y z w=
      slackQuadratic (1/d) g x (3*((d+1)*g)*x-d*y)
        (3*((d+1)*g)^2*x-2*d*((d+1)*g)*y+d^2*z)
        (((d+1)*g)^3*x-d*((d+1)*g)^2*y+d^2*((d+1)*g)*z-d^3*w) := by
  unfold slackQuadratic quadratic m00 m11 m22 m33 m01 m02 m03 m12 m13 m23
  field_simp [hd]
  ring

theorem slackQuadratic_nonneg {d g:ℝ}
    (hd:0  <  d) (hg:0 ≤ g) (hg1:g ≤ 1) (x y z w:ℝ):
    0 ≤ slackQuadratic d g x y z w := by
  by_cases hd1:d ≤ 1
  · exact slackQuadratic_nonneg_small_d hd hd1 hg hg1 x y z w
  · have hdi : 0  <  1/d := by positivity
    have hdi1 : 1/d ≤ 1 := (div_le_one hd).mpr (by linarith)
    rw [slackQuadratic_reciprocal d g x y z w hd.ne']
    exact slackQuadratic_nonneg_small_d hdi hdi1 hg hg1 _ _ _ _

end KLSImprovement.TwoConeCubic
#print axioms KLSImprovement.TwoConeCubic.minor4_factor
#print axioms KLSImprovement.TwoConeCubic.slackQuadratic_reciprocal
#print axioms KLSImprovement.TwoConeCubic.slackQuadratic_nonneg
