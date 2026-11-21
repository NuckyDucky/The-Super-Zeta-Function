\\ PARI/GP. A deterministic ideal-class calculation for the quartic.
\\ Run: gp -q -f class_check.gp
\\ Full class group certification is enabled by default. Set the environment
\\ variable QUARTIC_SKIP_CLASS_CERT=1 for a quick arithmetic-only replay.
default(parisizemax, 256000000);
setrand(1);
certify = getenv("QUARTIC_SKIP_CLASS_CERT") != "1";

\\ In Z[i], determine the two local signs by reducing the branch discriminant
\\ at the two square roots of -1 in F_p. This supplies only the calibration
\\ readings at 5 and 29. Other signs are read after the character is fixed.
split_trace(p, dr, di) = {
  my(t = lift(sqrt(Mod(-1,p))));
  kronecker(dr+di*t, p) + kronecker(dr-di*t, p);
};

class_exponent(v, c) = (v[1] + c[1]*v[2] + c[2]*v[3]) % 4;
character_trace(e) = [2, 0, -2, 0][1+(e%4)];
require(test, message) = if(!test, error(message));

\\ Multiply a truncated ideal-counting Euler product by (1-[j]T^f)^(-1)
\\ in the group ring of Z/4. Here q is the ideal norm, not necessarily prime.
add_ideal(M, q, j, limit) = {
  for(k=1, limit\q,
    for(v=0, 3, M[k*q, 1+(v+j)%4] += M[k, v+1]);
  );
  M;
};

run_checks() = {
  my(dr=-5045155, di=1027708, d=dr^2+di^2, limit=4096, B, primes, marks);
  my(candidates=List(), calibration=[5,29], e, v, c, rows, trace);
  my(split=0, inert=0, marked_trace, held=0, norm, positive);
  my(positive_mass=0, absolute_signed_mass=0, mixed_norms=0, first_mixed=0);
  my(M=matrix(limit,4), gauss=vector(limit), row, conjugate_primes);
  print("PARI ", version());
  B=bnfinit(x^2+d,1);
  require(B.cyc==[1111888,2,2],"unexpected class group basis orders");
  print("class group orders = ", B.cyc, "; class number = ", B.no);
  if(certify,
    require(bnfcertify(B)==1, "unconditional certification failed");
    print("full bnfcertify = 1");
  );
  primes=[41,457,1414835497];
  require(prod(j=1,#primes,primes[j])==d,"conductor");
  marks=vector(#primes,j,lift(Mod(-dr,primes[j])/di));

  \\ Up to inversion, the first cyclic generator of any surjection to C4
  \\ has image i. The two generators of order 2 have image +1 or -1.
  forstep(j=0,2,2, forstep(k=0,2,2, listput(candidates,[j,k])));
  for(j=1,#calibration,
    my(p=calibration[j]);
    v=bnfisprincipal(B,idealprimedec(B,p)[1],0);
    trace=split_trace(p,dr,di);
    candidates=List(select(k -> character_trace(class_exponent(v,k))==trace, Vec(candidates)));
    print("calibration ",p,": Gaussian trace ",trace,", ",#candidates," choices remain");
  );
  require(#candidates==1,"calibration did not identify the character");
  c=candidates[1];
  print("character exponent vector mod 4 = ", [1,c[1],c[2]]);

  \\ Compute the four class counts from K's prime ideals and their coordinates.
  M[1,1]=1;
  forprime(p=2,limit,
    if(kronecker(-4*d,p)==-1,
      \\ Inert prime: the unique ideal is the principal ideal (p).
      if(p*p<=limit,M=add_ideal(M,p*p,0,limit));
      if(p<=997,inert++);
    ,
      conjugate_primes=idealprimedec(B,p);
      for(j=1,#conjugate_primes,
        row=conjugate_primes[j];
        v=bnfisprincipal(B,row,0); e=class_exponent(v,c);
        require(row.f==1,"degree-one prime expected");
        M=add_ideal(M,p,e,limit);
        if(j==1 && p<=997 && d%p && p!=2,
          split++; if(!setsearch(calibration,p),held++);
          marked_trace=if(p%4==1,split_trace(p,dr,di),0);
          require(character_trace(e)==marked_trace,Str("failed holdout at ",p));
          if(p==13 || p==37,
            print("holdout ",p,": coordinates ",v,", exponent ",e,", predicted signed trace ",character_trace(e))
          );
        );
      );
    );
  );
  require(split==74 && inert==91 && held==72,"incorrect holdout count");
  print("good primes <=997: ",held," split holdouts, ", #calibration," calibrators, ",inert," inert");

  \\ Compare with a separate enumeration: one first-quadrant generator per
  \\ Gaussian ideal and the principal character formula at the conductor.
  for(x0=1,sqrtint(limit),for(y0=0,sqrtint(limit-x0^2),
    norm=x0^2+y0^2;
    gauss[norm]+=prod(j=1,#primes,kronecker(x0+marks[j]*y0,primes[j]));
  ));
  for(n=1,limit,
    require(M[n,2]==M[n,4],Str("conjugate class count mismatch at ",n));
    require(gauss[n]==M[n,1]-M[n,3],Str("signed norm coefficient mismatch at ",n));
    positive=0;
    fordiv(n,k,positive+=kronecker(-4*d,k)+kronecker(-4,k)*kronecker(d,n/k));
    require(2*(M[n,1]+M[n,3])==positive,Str("positive comparison mismatch at ",n));
    positive_mass+=M[n,1]+M[n,3];
    absolute_signed_mass+=abs(gauss[n]);
    if(min(M[n,1],M[n,3])>0,
      mixed_norms++;
      if(first_mixed==0, first_mixed=n);
    );
  );
  print("All ",limit," norms agree for both the signed Gaussian and the positive Dirichlet companion.");
  print("Equal-norm cancellation: absolute signed mass ",absolute_signed_mass," out of ",
        positive_mass," positive counts remain, ",mixed_norms," mixed norms. First mixed norm ",
        first_mixed," has class counts ",M[first_mixed,],".");
  print("At 73 the class counts are ",M[73,],", and at 73^2 the inert local coefficient is +1.");
};
iferr(run_checks(), err, print(err); quit(1));
quit(0);
