"""Portable exact reconstruction from shipped Lean source, not producer JSON.

No producer is imported or executed. This does not replace the full Lean build.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse, ast, hashlib, json, math, re

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1],help='Shipped KLS15 source root.')
parser.add_argument('--output',type=Path,help='New JSON result path; existing evidence is preserved.')
args=parser.parse_args()
BASE=args.root.resolve()
OUTPUT=args.output if args.output else BASE/'verification/scalar-audit.json'
assert not OUTPUT.exists(), 'Choose a new --output path; preserve prior audit evidence.'
DATA=BASE/'SymmetricCenteredSeed245Data.lean'
NUM=BASE/'CoupledSub15Numerics.lean'
HEAD=BASE/'CoupledSub15HeadPolynomialCertificate.lean'
ds,ns,hs=DATA.read_text(),NUM.read_text(),HEAD.read_text()
checks=[]
def check(ok,name):
    assert ok,name
    checks.append(name)

class P:
    def __init__(self,v=0):
        if isinstance(v,P):self.v=v.v;return
        v=list(v) if isinstance(v,(tuple,list)) else [F(v)]
        while len(v)>1 and not v[-1]:v.pop()
        self.v=tuple(map(F,v))
    def __add__(self,b):
        b=P(b);return P([(self.v[i] if i<len(self.v) else 0)+(b.v[i] if i<len(b.v) else 0) for i in range(max(len(self.v),len(b.v)))])
    __radd__=__add__
    def __neg__(self):return P([-x for x in self.v])
    def __sub__(self,b):return self+-P(b)
    def __rsub__(self,b):return P(b)+-self
    def __mul__(self,b):
        b=P(b);r=[F(0)]*(len(self.v)+len(b.v)-1)
        for i,a in enumerate(self.v):
            for j,z in enumerate(b.v):r[i+j]+=a*z
        return P(r)
    __rmul__=__mul__
    def __truediv__(self,b):
        b=P(b);assert len(b.v)==1 and b.v[0]
        return P([x/b.v[0] for x in self.v])
    def __rtruediv__(self,b):return P(b)/self
    def __pow__(self,n):
        assert int(n)==n and n>=0
        r=P(1)
        for _ in range(int(n)):r=r*self
        return r
    def __eq__(self,b):return self.v==P(b).v
    def derivative(self):return P([i*x for i,x in enumerate(self.v)][1:] or [0])
    def at(self,t):
        r=F(0)
        for x in reversed(self.v):r=r*t+x
        return r

t=P([0,1])
def arithmetic(expr):
    node=ast.parse(expr.replace('^','**'),mode='eval').body
    def go(n):
        if isinstance(n,ast.Constant):assert isinstance(n.value,int);return F(n.value)
        if isinstance(n,ast.Name):assert n.id=='t';return t
        if isinstance(n,ast.UnaryOp):
            assert isinstance(n.op,(ast.USub,ast.UAdd));return -go(n.operand) if isinstance(n.op,ast.USub) else go(n.operand)
        assert isinstance(n,ast.BinOp)
        a,b=go(n.left),go(n.right)
        if isinstance(n.op,ast.Add):return a+b
        if isinstance(n.op,ast.Sub):return a-b
        if isinstance(n.op,ast.Mult):return a*b
        if isinstance(n.op,ast.Div):return a/b
        assert isinstance(n.op,ast.Pow);return a**int(b)
    return go(node)
def line_def(source,name):
    return re.search(r'^def '+re.escape(name)+r'[^\n]*? := ([^\n]+)',source,re.M).group(1)
def scalar(source,name):return F(arithmetic(line_def(source,name)))
def array(source,name):
    a=re.search(r'^def '+re.escape(name)+r'[^\n]* := !\[([^\]]+)\]',source,re.M).group(1)
    return list(map(F,a.split(',')))
def unnormalized(row,x):
    n=len(row)-1
    return sum((a*x**j*(18-x)**(n-j) for j,a in enumerate(row)),P(0))

B=scalar(ds,'B');Tend=scalar(ds,'seedT');Cseed=scalar(ds,'seedC');Rseed=scalar(ds,'seedR');az=scalar(ds,'alphaZero')
V=P(arithmetic(line_def(ds,'seedV')))
Vp=P(arithmetic(line_def(ds,'seedVp')));Vpp=P(arithmetic(line_def(ds,'seedVpp')))
check(V.derivative()==Vp,'seed_first_derivative')
check(Vp.derivative()==Vpp,'seed_second_derivative')
Slope=V+t*Vp
Con=-(3*V*Vp+t*(Vp*Vp+V*Vpp))
Pr=-16*(1-t*t)*V*Slope+F(9,2)*B*(1-t*t)+17*t*t*V*V
Nq=Rseed*V*Slope+(F(9,2)*B*Cseed+F(64,3)/Cseed)*t*V
Det=Pr*Pr-(1-t*t)*Nq*Nq
Alpha=4*(1-t*t)-9*Cseed*Cseed*t*t*V*V
polys={'seedV':V,'seedSlope':Slope,'seedConcavity':Con,'seedP':Pr,'seedNegQ':Nq,'seedDet':Det,'seedAlphaPoly':Alpha}
seed_min={}
for name,p in polys.items():
    row=array(ds,name+'Coefficients')
    integer=P(arithmetic(line_def(ds,name+'Integer')))
    multiplier=F(re.search(re.escape(name)+r'Integer t=\((\d+):ℝ\)\*'+name+r' t',ds).group(1))
    check(integer==multiplier*p,name+'_denominator_clear')
    check(integer==unnormalized(row,25*t),name+'_whole_interval_representation')
    for i,x in enumerate(row):check(x>0,name+'_positive_'+str(i))
    seed_min[name]=str(min(row))
check(B==F(49,2) and Tend==F(18,25),'seed_constants')
check(Tend*Tend*V.at(Tend)**2>1,'seed_inverse_range_endpoint')
check(Rseed*Rseed*B>=64,'seed_radical_majorant')
check((16+Rseed)*V.at(0)**2<az*F(9,2)*B,'seed_zero_strict_margin')
check(F(1,3)<=az<1 and Cseed>0 and Rseed>0,'seed_zero_alpha_range')

K=scalar(ns,'K');C=scalar(ns,'C');c=scalar(ns,'c');p=scalar(ns,'p')
# Parse the multiline alpha definition directly, avoiding any producer table.
alpha={int(i):F(arithmetic(x)) for i,x in re.findall(r'if d=(\d+) then ([^\n]+?) else',ns.split('def alpha',1)[1].split('def A',1)[0])}
check(set(alpha)==set(range(2,16)),'alpha_table_complete')
def al(d):return alpha.get(d,F(17,50))
def young(d):
    if d==2:return F(8563,10000)
    if d==3:return F(1061,1000)
    return F(3801,2000)+F(442,625)*(d-4) if d<=24 else F(81,5)
check('8563/10000' in line_def(ns,'young') and '1061/1000' in ns and '3801/2000+(442/625)' in ns and 'else 81/5' in ns,'young_source_profile')
def prefix(d):return sum((young(b) for b in range(2,d)),F(0))
def defined_prefix(d):
    if d==2:return F(0)
    if d==3:return F(8563,10000)
    if d<=25:return F(8563,10000)+F(1061,1000)+(d-4)*F(3801,2000)+F(221,625)*(d-4)*(d-5)
    return F(951699,5000)+F(81,5)*(d-25)
for d in range(2,50):check(prefix(d)==defined_prefix(d),'prefix_'+str(d))
for d in range(2,17):check(0<=al(d)<1,'alpha_range_'+str(d))
check(al(2)>=F(1,3),'symmetric_quadratic_alpha_gate')
def A(d):return 4/(1-al(d))-2
def f(d):return (K*al(d-1)-A(d)-K*C/young(d))*d*d-(A(d)-3)*d-1-prefix(d)
for d in range(4,26):check(f(d)>=c,'finite_coefficient_'+str(d))
qa=K*F(17,50)-A(26)-K*C/F(81,5)
qb=-(A(26)-3)-F(81,5)
qc=-1-F(951699,5000)+25*F(81,5)
check((qa,qb,qc)==(F(6767,14850),-F(2848,165),F(1068301,5000)),'tail_polynomial_literal')
check(qa>0 and 52*qa+qb>0 and f(26)>=c,'tail_all_real_degrees_ge26')
head=F(64,3)/(1-al(2))-17+4*K*C/young(2)
check(head==F(447391331,16980429),'head_literal')
check(f(3)==-F(2355275515819,74323050000),'cubic_coefficient_literal')
check(c+head>=0 and c-f(3)>=0,'head_substitution_signs')
HP=c*C-(c+head)*2/(K*K)*t*t*V*V-(c-f(3))*B/(K**3)*(1-t*t)
hm=F(re.search(r'theorem representation0[^\n]*\n\s*\((\d+) : ℝ\)',hs).group(1))
head_min=[]
for j in range(4):
    row=array(hs,'coefficients'+str(j))
    check(unnormalized(row,100*t-18*j)==hm*HP,'head_representation_'+str(j))
    for i,x in enumerate(row):check(x>0,'head_positive_'+str(j)+'_'+str(i))
    head_min.append(str(min(row)))
check(4*F(18,100)==Tend,'head_closed_interval_cover')
a,b=2/(K*K),B/(K**3)
u=p*p-a;v=u*(p-a/p)-b
ratio=p-a/p-b/u-(C-a-b)/v
check(a>=0 and b>=0 and a+b<=C,'operator_budget_caps')
check(1<p<=u<=v,'operator_anchor_denominators')
check(ratio>1,'operator_residual_ratio_strict')
check(1+K*p==F(149963,10000)<15,'strict_sub15_endpoint')

# These ten hashes bind the original frozen-source arithmetic audit.
# Historical log/object receipts are not rechecked by this portable script.
FROZEN_SOURCE_HASHES={'SymmetricCenteredSeed245Data': '55ccd288c07ac2456aecd45a92e58833ccf393a1caf88b9591359c444002ee35', 'CoupledSub15Numerics': 'ae2bbac9418e373f1a693873903cd0a2d0c2221d9d1ae59667d01a3306c72c7f', 'CoupledSub15HeadPolynomialCertificate': '66d71b94db1f522b58824ad1709505df24a64343eb1f04c975d82a86beba7114', 'SymmetricCenteredSeed245Scalar': '4af749a709f410c0995adc7b78373255fafd136945e3eea8d95c6ad8f0de3321', 'SymmetricCenteredSeed245Inverse': '43f905b1adcfac0a0a72e3fab944f7fd051e98759aee79f3cb792f609fb73c85', 'ActualSymmetricCenteredCubicSeed245': '37b0cc26e576a320a402f860b0b2b59f092100be5323b32ed65c707671850193', 'ActualWeightedGeneratorLowerSub15': '02eef7bf3cd9539f539fc7dddd5340e8704a8230cd69c13886459ae4b4754f6e', 'ActualWeightedAppellInductionSub15': '849721af01e654d302264a14d92c202223a87b304aa0daf06d0cefa4a2e4c28b', 'ActualRegularEndpointSub15': '5b7b310d23ad43160105266c51231862e3afc71347c13799ed9c67e5cf54adcf', 'ActualKLS149963Endpoints': 'd8d5aed4a4234c582db6f4f424a7c44c2fdcf7c9bbeb8b298a2731a236c2f6d4'}
manifest=json.loads((BASE/'verification/source-manifest.json').read_text())['source_provenance']
source_bindings=[]
for module,expected in FROZEN_SOURCE_HASHES.items():
    check(module in manifest,module+'_in_shipped_manifest')
    entry=manifest[module]
    check(entry['source_sha256']==expected,module+'_frozen_source_binding')
    src=BASE/(module+'.lean')
    check(hashlib.sha256(src.read_bytes()).hexdigest()==entry['source_sha256'],module+'_staged_source_hash')
    source_bindings.append({'path':module+'.lean','source_sha256':expected})
result={'status':'PASS independent portable exact source arithmetic and source-manifest correspondence','scope':'No producer executed/imported. The 369 arithmetic checks plus 30 source provenance checks are separate from the whole Lean build and historical object/log receipts.','checks':len(checks),'arithmetic_checks':369,'source_provenance_checks':30,'check_names':checks,'seed_whole_interval_min_integer_coefficients':seed_min,'head_min_integer_coefficients':head_min,'K':str(K),'C':str(C),'p':str(p),'B':str(B),'endpoint':str(1+K*p),'tail_polynomial':[str(qa),str(qb),str(qc)],'residual_ratio_margin':str(ratio-1),'source_bindings':source_bindings,'source_manifest_sha256':hashlib.sha256((BASE/'verification/source-manifest.json').read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
OUTPUT.parent.mkdir(parents=True,exist_ok=True)
OUTPUT.write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(checks),'exact arithmetic/source-provenance checks; strict endpoint',1+K*p)
