\\ Exact 2-descent and Cassels-pairing calculation, PARI/GP 2.20.0 snapshot.
\\ Run headlessly: gp -q -f arithmetic.gp
setrand(1);
E=ellinit([0,5028677,0,-305545084240,0]);
P=[93082857946624000/911427267969,129969110503209045907820800/870127764175520703];
print("VERSION ",version());
print("POINT_ON_CURVE ",ellisoncurve(E,P));
print("TORSION ",elltors(E));
r=ellrank(E,0,[P]);
print("RANK_DATA ",r);
print("SELMER_BASIS_DIM ",#ell2cover(E));
print("MINIMAL_COEFFICIENTS ",Vec(ellminimalmodel(E))[1..5]);
print("GLOBAL_ROOT_NUMBER ",ellrootno(E));
quit();
