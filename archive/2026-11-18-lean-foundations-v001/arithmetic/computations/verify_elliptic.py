"""Exact polynomial checks for the norm-quartic / rational-2-isogeny bridge.
Requires python-flint (no network, GPU, numerical root finding, or app startup).
Run from any directory; writes elliptic-results.json next to this script.
"""
from pathlib import Path
import json
from flint import fmpz, fmpz_poly, fmpz_mpoly_ctx

ctx = fmpz_mpoly_ctx.get(['a', 'b', 'c', 'd', 'e', 'f', 't'])
a, b, c, d, e, f, t = ctx.gens()
da = b*b - 4*a*c
db = e*e - 4*d*f
m = b*e - 2*a*f - 2*c*d
R = (a*f-c*d)**2 - (a*e-b*d)*(b*f-c*e)
q = da + t*db
D = (da-t*db)**2 + 4*t*m*m
A4 = a*a+t*d*d
B4 = 2*a*b+2*t*d*e
C4 = b*b+2*a*c+t*(e*e+2*d*f)
D4 = 2*b*c+2*t*e*f
E4 = c*c+t*f*f
I = 12*A4*E4-3*B4*D4+C4*C4
J = 72*A4*C4*E4+9*B4*C4*D4-27*A4*D4*D4-27*B4*B4*E4-2*C4**3
r = 3*q

checks = {}
def check(name, lhs, rhs=0):
    ok = lhs == rhs
    checks[name] = bool(ok)
    if not ok:
        raise AssertionError(name + ': ' + str(lhs-rhs))

check('mixed_discriminant_resultant', m*m-da*db, 4*R)
check('norm_quartic_I_formula',I,q*q+12*t*R)
check('norm_quartic_J_formula',J,-2*q**3-36*t*R*q)
check('Jacobian_rational_2torsion_root', r**3-27*I*r-27*J)
check('Jacobian_shift_linear_coefficient', 3*r*r-27*I, -324*t*R)
check('Jacobian_shift_quadratic_coefficient', 3*r, 9*q)
check('partition_discriminant', q*q+16*t*R, D)
check('binary_quartic_discriminant', 4*I**3-J*J, 27*16*t*t*R*R*D)

# Verify the isogeny after clearing denominators, for indeterminate a,b,x.
c2 = fmpz_mpoly_ctx.get(['a', 'b', 'x'])
a2,b2,x = c2.gens()
S=x*x+a2*x+b2
# x'=S/x, y'=y*(b-x^2)/x^2; y^2=x*S.
source = x*S*(b2-x*x)**2
target = x*S*(S*S-2*a2*x*S+(a2*a2-4*b2)*x*x)
check('isogeny_equation_cleared_denominators', source, target)

# The degree-two translation formula: translate by (0,0) on E.
# tau(x,y)=(b/x,-b*y/x^2). Verify isogeny invariance with denominators cleared.
check('isogeny_x_invariant_under_2torsion', b2*b2+a2*b2*x+b2*x*x, b2*S)
check('isogeny_y_invariant_under_2torsion', -b2*(b2*x*x-b2*b2), b2*b2*(b2-x*x))

# Original numerical coefficients: A=N-D, B=N, t=4.
AA=(310,-579,277)
BB=(465,-183,-659)
tt=4
aa,bb,cc=AA
dd,ee,ff=BB
daa=bb*bb-4*aa*cc
dbb=ee*ee-4*dd*ff
mm=bb*ee-2*aa*ff-2*cc*dd
RR=(aa*ff-cc*dd)**2-(aa*ee-bb*dd)*(bb*ff-cc*ee)
qq=daa+tt*dbb
DD=(daa-tt*dbb)**2+4*tt*mm*mm
quartic = fmpz_poly([cc*cc+tt*ff*ff,2*bb*cc+2*tt*ee*ff,bb*bb+2*aa*cc+tt*(ee*ee+2*dd*ff),2*aa*bb+2*tt*dd*ee,aa*aa+tt*dd*dd])
coefs=list(map(int,quartic.coeffs()))
A_,B_,C_,D_,E_=list(reversed(coefs))
II=12*A_*E_-3*B_*D_+C_*C_
JJ=72*A_*C_*E_+9*B_*C_*D_-27*A_*D_*D_-27*B_*B_*E_-2*C_**3
rr=3*qq
Jac=fmpz_poly([-27*JJ,-27*II,0,1])
assert Jac(rr)==0
iso_a=9*qq
iso_b=-324*tt*RR
iso_ap=-2*iso_a
iso_bp=iso_a*iso_a-4*iso_b
assert int(quartic.discriminant()) == 16*tt*tt*RR*RR*DD
assert iso_bp == 81*DD

# Smaller Q-isomorphic models, u=9*x+3*q, v=27*y.
small_a=qq
small_b=-4*tt*RR
small_ap=-2*qq
small_bp=qq*qq+16*tt*RR
assert iso_a==9*small_a and iso_b==81*small_b
assert iso_ap==9*small_ap and iso_bp==81*small_bp

# Third quadratic subfield: the quotient by the product of original involutions.
k=fmpz_poly([0,1])
disc_x=-8239*k*k-2055416*k+20147664
disc_s=k*k+4
quotient=disc_x*disc_s
qe,qd,qc,qb,qa=map(int,quotient.coeffs())
quot_I=12*qa*qe-3*qb*qd+qc*qc
quot_J=72*qa*qc*qe+9*qb*qc*qd-27*qa*qd*qd-27*qb*qb*qe-2*qc**3
check('quotient_quartic_I',quot_I,16*(qq*qq-192*RR))
check('quotient_quartic_J',quot_J,64*(-2*qq*(qq*qq+576*RR)))
# Short-model translation on E0': x=z+2*q/3, then u=36*z,v=216*y
# yields v^2=u^3-27*quot_I*u-27*quot_J. Clear the factors of 3 and 27.
check('quotient_Jacobian_short_A',-27*quot_I*3,1296*(3*small_bp-small_ap*small_ap))
check('quotient_Jacobian_short_B',-27*quot_J*27,46656*(2*small_ap**3-9*small_ap*small_bp))

c3=fmpz_mpoly_ctx.get(['x','y'])
xx,yy=c3.gens()
NN=465*xx*xx-183*xx-659
AAx=310*xx*xx-579*xx+277
PP=AAx*yy*yy+(3*AAx-2*NN)*yy+(2*AAx-3*NN)
Xrad=2*(1240*NN-1860*AAx)*xx+732*AAx-2316*NN
Dxnum=-8239*(4*NN)**2-2055416*(4*NN)*AAx+20147664*AAx*AAx
Srad=AAx*(4*yy+6)-4*NN
Dsnum=(4*NN)**2+4*AAx*AAx
check('quotient_x_branch_radical',Xrad*Xrad,Dxnum)
check('quotient_s_branch_radical_mod_source_curve',Srad*Srad-Dsnum,16*AAx*PP)
check('quotient_w_map_mod_source_curve',(Xrad*Srad)**2-Dxnum*Dsnum,16*AAx*PP*Dxnum)
assert disc_x.gcd(disc_s)==1

out={
 'scope':'exact polynomial identities over Z[a,b,c,d,e,f,t], plus original integer specialization',
 'floating_precision':'none: all computations use exact FLINT integers and multivariate polynomials',
 'checks':checks,
 'generic':{
  'quartic':'A(x)^2+t*B(x)^2',
  'q':'disc(A)+t*disc(B)',
  'R':'Res(A,B)',
  'Jacobian':'v^2=u^3-27*I*u-27*J',
  'rational_2torsion_u':'3*q',
  'smaller_E':'y^2=x^3+q*x^2-4*t*R*x',
  'smaller_Eprime':'yp^2=xp^3-2*q*xp^2+(q^2+16*t*R)*xp',
  'isomorphism_from_smaller_E_to_Jacobian':'u=9*x+3*q; v=27*y',
  'shifted_E':'Y^2=X^3+9*q*X^2-324*t*R*X',
  'quotient_Eprime':'Yp^2=Xp^3-18*q*Xp^2+81*(q^2+16*t*R)*Xp',
  'isogeny':'Xp=X+a+b/X; Yp=Y*(b-X^2)/X^2',
  'translation':'tau(X,Y)=(b/X,-b*Y/X^2)',
  'nonsingular_condition':'t*R*((disc(A)-t*disc(B))^2+4*t*m^2) != 0'
 },
 'original':{
  'A_descending':AA,'B_descending':BB,'t':tt,'disc_A':daa,'disc_B':dbb,
  'mixed_discriminant':mm,'resultant':RR,'q':qq,'partition_discriminant':DD,
  'quartic_ascending':coefs,'quartic_discriminant':str(quartic.discriminant()),
  'I':II,'J':JJ,'Jacobian_factorization':str(Jac.factor()),
  'torsion_point':[rr,0],
  'E_coefficients_a_b':[iso_a,iso_b],
  'Eprime_coefficients_a_b':[iso_ap,iso_bp],
  'smaller_E_coefficients_a_b':[small_a,small_b],
  'smaller_Eprime_coefficients_a_b':[small_ap,small_bp],
  'quotient_quartic_ascending':list(map(int,quotient.coeffs())),
  'quotient_quartic_discriminant':str(quotient.discriminant()),
  'quotient_quartic_I':quot_I,'quotient_quartic_J':quot_J,
  'E_quadratic_factor_discriminant':iso_bp,
  'E_quadratic_factor_discriminant_factorization':str(fmpz(iso_bp).factor()),
  'rational_2torsion_group':'Z/2Z',
  'note':'The nonsquare quadratic discriminant proves uniqueness of the nonzero rational 2-torsion point.'
 }
}
path=Path(__file__).with_name('elliptic-results.json')
path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':len(checks),'all_passed':all(checks.values()),'output':str(path),'E':[iso_a,iso_b],'Eprime':[iso_ap,iso_bp]}))
