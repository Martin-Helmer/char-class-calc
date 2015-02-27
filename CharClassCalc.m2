-----------------------------------------------------------------
-- Preamble
-----------------------------------------------------------------

newPackage(
	"CharClassCalc",
	Version => "2.1", 
    	Date => "Dec. 8, 2014",
    	Authors => {{Name => "Martin Helmer", 
		  Email => "mhelmer2@uwo.ca", 
		  HomePage => "http://publish.uwo.ca/~mhelmer2/"}},
    	Headline => "Computes CSM classes, Segre classes and the Euler Char.",
    	DebuggingMode => true,
	Reload => true
    	)
--Try to load Bertini for numerical option
try loadPackage ("Bertini", Reload=>true) then (<<"Bertini Loaded"<<endl;) else (<<"Bertini not loaded (check configuration), only VspaceSymbolic (default) option available"<<endl;);


--Exported functions/variables
export{
   Segre,
   CSM,
   Euler,
   EulerAffine,
   GradMultiDegree,
   Alg,
   InEx,
   Composite,
   Method,
   VspaceDim,
   Sat,
   Num

}



----------------------------------------------
-- External functions
----------------------------------------------
-- Example:
    --n=4;
    --kk=ZZ/32749;-- can use either finite feild or the rationals, finite feild is faster for VspaceDimbolic (default)option,     
                  --for the rationals use --kk=QQ;
    --R=kk[y_0..y_n];
    --I=ideal(y_2^3-y_1^3,y_0*y_1*y_4);
    --Segre (I)
    -->>           4      3     2
    --    o1 = 243H  - 54H  + 9H
    --
    --         ZZ[H]
    --    o2 : -----
    --            5
    --           H
    -- -- can also do Segre(I,Method=>Num) for numeric calculation, but must use kk=QQ
    -- CSM(I)
    -->>           4      3     2
    --      o3 = 6H  + 12H  + 7H
    --
    --         ZZ[H]
    --    o4 : -----
    --            5
    --           H
    --Euler(I)
    -->>                   4      3     2
    -- The CSM class is: 6H  + 12H  + 7H
    -- The Euler charcteristic is: 6
    --  o5 = 6
--
-- Example 2
--   n=6;
--   kk=ZZ/32749; 
--   R=kk[x_0..x_n];
--   M = matrix{{x_1*x_4^2*x_3-x_1^4,random(4,R),random(4,R)},{random(4,R),x_0^2*x_5^2-x_6^3*x_0,random(4,R)}};
--   I=minors(2,M);
--   time Segre(I)
--   o1000000070 : Matrix R  <--- R

--   o1000000071 : Ideal of R

     -- used 5.36367 seconds
--                         6         5        4       3      2
--    o1000000072 = 327680H  - 49152H  + 6144H  - 640H  + 48H
--
--                  ZZ[H]
--    o1000000072 : -----
--                     7
--                    H 
------------------------------------

-- Input:
--    I - homogeneous polynomial ideal     
--    Euler does not have a numerical computation option (since it is usually slower to use the numeric option) 
-- Output:
    -- A Chow Ring element

Euler=method(TypicalValue => RingElement, Options => {Alg=>InEx, Method=>VspaceDim});

Euler Ideal:= opts-> I->(
    CSMClass:=CSM(I,Alg=>opts.Alg,Method=>opts.Method);
    <<"The CSM class is: "<<CSMClass<<endl;
    <<"The Euler charcteristic is: "<<leadCoefficient(CSMClass)<<endl;
    return leadCoefficient(CSMClass);
    )

-- Input:
--    I - homogeneous polynomial ideal     
--    Euler does not have a numerical computation option (since it is usually slower to use the numeric option) 
-- Output:
    -- A Chow Ring element
-- Uses the method of 2.8 of COMPUTING CHARACTERISTIC CLASSES OF PROJECTIVE SCHEMES, Aluffi
EulerAffine=method(TypicalValue => RingElement, Options => {Alg=>InEx, Method=>VspaceDim});

EulerAffine Ideal:= opts-> I->(
    R:=ring I;
    n:=numgens R;
    kk:=coefficientRing R;
    hv:=symbol hv;
    S:=kk[hv,gens R];
    Ih:=homogenize(substitute(I,S),hv);
    <<"Assuming the input ideal defines a subscheme of dimension "<<n<<" Affine space";
    Ih2:=substitute( sub(Ih,{hv=>0}), R);
    CSMProjClosure:=CSM(Ih,Alg=>opts.Alg,Method=>opts.Method);
    CSMLimitScheme:=CSM(Ih2,Alg=>opts.Alg,Method=>opts.Method);
    AffineEuler:=leadCoefficient(CSMProjClosure)-leadCoefficient(CSMLimitScheme);
    <<"The CSM class of the projective closure is: "<<CSMProjClosure<<endl;
    <<"The CSM class of the 'limit' scheme is: "<<CSMProjClosure<<endl;
    <<"The Affine Euler charcteristic is: "<<AffineEuler<<endl;
    return leadCoefficient(AffineEuler);
    )

-- Input:
--    I - homogeneous polynomial ideal     
--    opts - Method lets you choose VspaceDim, which is the method described in [1], Sat, which is similar except uses --a saturation instead of a vector space dimension and Num which uses Bertini. Both Vspace dim and Sat are symbolic -- 
-- methods, Num is numeric. For the numeric option the polynomial ring must be over the rationals
-- Output:
    -- A Chow Ring element

CSM = method(TypicalValue => RingElement,  Options => {Alg=>InEx, Method=>VspaceDim} );

CSM Ideal :=  opts ->  I -> (
    <<"Start csm, Alg= "<<opts.Alg<<", Method= "<<opts.Method<<endl;
    S:=ring I;
    m:=numgens I;
    kk:=coefficientRing S;
    if  (not (kk===QQ)) and (opts.Method==Num) then (
        error "Numerical calculations must be done over the rational number feild (QQ)."; 
        return;
        );
    n:=numgens S-1; 
    csmclass:=0;
    csmtotal:=0;
    Ssets:=0;
    h := symbol h;   
    ChowRingPn:=ZZ[h]/(h^(n+1));
    use(ChowRingPn);

    if(opts.Alg==Composite) then (
        --<<"Starting comp. "<<endl;
        Imin:=ideal(mingens(I));
        hyper:=0;
        W:=0;
        cfj:=0;

        if codim(Imin)==numgens(Imin) then (
            <<"Input is a complete intersection "<<endl;
            Igens:=gens(I);
            if isSmooth(I) then (
                <<"Input is smooth "<<endl;
                --cE:=product(0..(m-1), i->(1+((degree(Igens_i))_0)*h));
                --cfj=(1+h)^(n)*(product(0..(m-1),i->(((degree(Igens_i))_0)*h))//(1+(degree(Igens_i))_0*h));
               -- seg:=Segre(I);
		--seg = sub(seg, vars ChowRingPn);
		cfj=(1+h)^(n+1)*product(0..numgens(I)-1,i->((degree(I_i))_0*h//(1+(degree(I_i))_0*h)));
		csmclass=cfj;
                return csmclass;
            ) else (
                Zideal:=0;
                SingIdeal:= 0;
                cont:=true;
                --<<"Starting first loop, m= "<<m<<endl;
                for j from 1 to m-1 do(
                    if cont then (
                        Ssets=subsets(set(entries(gens(I)))_0,m-j);
                        --      <<"Subsets= "<<Ssets<<endl;
                        for s in Ssets do(
                            W=ideal(elements(s));
                            if isSmooth(W) then (
                                SingIdeal=(entries(gens(I)))_0-s;
                                Zideal=W;
                            
                                cont=false;
                                break;
                                );
                            );
                        )
                    else(
                        break; 
                        );   
                    );        
                Ssets=subsets(SingIdeal)-set{{}};
                --<<"Ssets= "<<Ssets<<endl;
                csmtotal=0;
                --<<"Sing Ideal= "<<SingIdeal<<endl;
                --<<"Ssets= "<<Ssets<<endl;
                for s in Ssets do(
                    --<<"s= "<<s<<endl;
                    hyper=product(s);
                    -- <<"Finished Loops, going to one sing gen, hyper= "<<hyper<<endl;
                    csmtotal=csmtotal+(-1)^(#(s)+1)*CSMOneSingGen((Zideal+ideal(hyper)),hyper,ChowRingPn,h,Method=>opts.Method);
                    );
                csmclass=csmtotal;
                return csmclass;
                );
            ) 
        else (<<"Input is not a complete intersection, cannot use hybrid algorithm. Proceeding with inclusion/exclusion"<<endl;
            opts.Alg=InEx;
            );
        );
    if (opts.Alg==InEx) then (
        Subset1:=new MutableList from {0..m};
        Subset2:=new MutableList from {0..m};
        Ienters:=(entries gens I)_0;
        for s from 1 to m do (
            Subset1#s=apply(subsets(Ienters,s),eq->csmHyper(n,ChowRingPn,h,product(eq),Method=>opts.Method));
            Subset2#s=sum(Subset1#s);
            );
        csmclass=sum(1..m,s->-(-1)^s*Subset2#s);
        );
    <<"The Chern-Schwartz-Macpherson class is: "<<csmclass<<endl;
    return csmclass;
    );

-- Input:
--    I - homogeneous polynomial ideal     
--    opts - the option of VspaceDimbolic or numeric degree calculation, VspaceDimbolic is default, denoted VspaceDim. Numeric with 
--           Bertini is denoted Num,for the numeric option the polynomial ring must be over the rationals
-- Output:
    -- A Chow Ring element

Segre = method(TypicalValue => RingElement,  Options => {Method=>VspaceDim} );
Segre Ideal :=  opts ->  I -> ( 
    S:=ring I;
    m:=numgens I;
    kk:=coefficientRing S;
    if  (not (kk===QQ)) and (opts.Method==Num) then (error "Numerical calculations must be done over the rational number feild (QQ)."; return;);
    n:=numgens S-1; 
    h := symbol h;   
    ChowRingPn:=ZZ[h]/(h^(n+1));
    --d:=(degree I_0)_0;
    d:=first max degrees I; 
    use(ChowRingPn);
    g:=projectiveDegree(I,Method=>opts.Method);
    poly:=sum(0..n,s->g_s*h^s*(1+d*h)^(n-s));
    segreclass:=1 - poly * sum(0..n,i->binomial(n+i,i)*(-d*h)^i);
    <<"The Segre Class is: "<<segreclass<<endl;
    return segreclass;
    );

GradMultiDegree=method(TypicalValue=> RingElement, Options=>{Method=>VspaceDim});
GradMultiDegree RingElement := opts-> f -> (
    n:=numgens (ring f)-1; 
    jac:=ideal jacobian ideal f; 
    --<<"enter pd"<<endl;
    g:=projectiveDegree(jac,Method=>opts.Method);
    --<<"exit pd"<<endl;
    s:=symbol s;
    t:=symbol t;
    DegreeRing:=ZZ[s,t];
    gradMulti:=sum(length(g),i->g_i*s^i*t^(n-i));
    return gradMulti; 
    )


----------------------------------------------
-- Internal functions
----------------------------------------------


--------------------------------------------
--check if the ideal defines a smooth scheme.
isSmooth=I->(
    <<"In is smooth"<<endl;
    S:=ring I;
    Igens:=gens(I);
    J1:=minors(numgens(I), jacobian I)+I;
   -- gbJ1:=MyGb(I,"MGB");
   -- dimJ1 := dim ideal leadTerm gbJ1 - 1;
   -- <<"gb dim"<<dimJ1<<", Proj dim"<<dim(Proj(S/(J1)))<<endl;
   -- if dimJ1<0 then (return true;) else (return false;);
   if dim(Proj(S/(J1)))<0 then (return true;) else (return false;);
);
----------------------
---csm for an ideal with one singular generator 
---
---
------------------------

CSMOneSingGen ={Method => VspaceDim} >> opts ->(I, hyper,ChowRingPn,h)->(
    --<<"startin csm direct"<<endl;
    S:=ring I;
    n:=numgens S; 
    r:=numgens I;
    kk:=coefficientRing S;
    csm:=0;
    cfj:=0;
    Se:=0;
    Ssum:=0;
    n1:=n-1;
    Igens:=gens(I);
    litk:=numgens(I);
    --<<"hyper= "<<hyper<<endl;
    --<<"degree hyper= "<<degree(hyper)<<endl;
    dk:=((degree(hyper))_0);
       
    use(ChowRingPn);
    --<<"just before ce"<<endl;
    cE:=product(0..(litk-1), i->(1+((degree(Igens_i))_0)*h));
    stuff:=sum(0..litk,p-> h^(p)*sum(0..p,i->(-1)^i*binomial(litk-i,p-i)*cE_(h^i)*(dk)^(p-i) ) );
    <<"Computing singularity subscheme"<<endl;
    time K:=saturate (minors(litk, jacobian I) + I);
    Milnor:=0;
    --<<"Dim k "<<dim(K)<<endl;
    if dim(K)<=0 then (
        Milnor=0;)
    else (
        --<<"computing Segre class of singularity subscheme J= "<<K<<endl;
        time Se=Segre(K,Method=>opts.Method);
        R12:=ring(Se);
        hl2:=gens(R12);
        h2:=hl2_0;
        Ssum=sum(0..n1,i-> (-1)^i*h^i*Se_(h2^i)//((1+dk*h)^i));
            
        Milnor=((1+h)^n//cE)*stuff*Ssum
        );
    --<<"Milnor: "<<Milnor<<endl;
    cfj=(1+h)^(n)*(product(0..(litk-1),i->(((degree(Igens_i))_0)*h))//cE);
    --<<"cfj: "<<cfj<<endl;
    csm=cfj-(-1)^litk*Milnor;
        
    return csm;
);

{*
MyGb is a wrapper function for the M2 groebner basis command which 
uses the fastest avalible GB algorithm depending on the users system and on the feild over which they are working
*}

MyGb =(I,stdgy)->(
   -- <<"In my GB"<<endl;
    gbI:=0;
    try (gbI = groebnerBasis(I, Strategy=>stdgy)) else ( gbI= groebnerBasis(I));
    return gbI;
    )
--The main calculation is done here
-- Input:
--    I - homogeneous polynomial ideal     
--    opts - the option of VspaceDimbolic or numeric degree calculation, VspaceDimbolic is default, denoted VspaceDim. Numeric with 
--           Bertini is denoted Num,for the numeric option the polynomial ring must be over the rationals
-- Output:
    -- A sequence of projective degrees
projectiveDegree = {Method => VspaceDim} >> opts -> I -> (    
    --<<"In Projective Degree method= "<<opts.Method<<endl;
    S:=ring I;
    m:=numgens I;
    kk:=coefficientRing S;
    n:=numgens(S) -1;
    -- gbI := groebnerBasis(I, Strategy=>"MGB");
    gbI:=MyGb(I,"MGB");
    --gbI := groebnerBasis(I, Strategy=>"F4");
    dimI := dim ideal leadTerm gbI - 1;
    --dimI:= dim Proj(S/I);
    t:=symbol t;
    R3:=kk[gens S,t];
    J:=substitute(I,R3) ;
    njac:=numgens J;
    g:=new MutableList from {0..n}; 
    g#0=1;
    Pol:=0;
    d:=first max degrees I;
    gensI:=0;
    minDegGen:=0;
    MinDegGen:=0;
    --I=trim(I);
    if opts.Method==Sat then (
        d=first max degrees I;
        gensI = flatten entries sort gens I; 
        minDegGen = first gensI;
        MinDegGen=substitute(minDegGen,R3);
        njac=numgens I;
        );
    Xs:=0;
    K:=0;
    EqT:=0;
    Wt:=0;
    Wg:=0;
    Wt3:=0;
    S1:=0;
    WtT:=0;
    Pol3:=0;
    m3:=0;
    Pol2:=0;
    tall:=0;
    ind:=0;
    val5:=0;
    solutions:=0;
    solutions1:=0;
    Sgens := (gens R3)_{0..n};
    val:=n-dimI;
    gbWt2:=0;
    tall2:=0;
    --<<"Method ="<<opts.Method<<endl;

    for k from 1 to n do (
        if k<val then (g#k=(d)^k) else (
            if opts.Method==VspaceDim then(
                Pol=sum ( k,jj-> ideal sum(njac,i->random(kk)*J_i*substitute(random(d-first(degree(J_i)),S),R3)));
                Xs=sum((n-k),jj->ideal sum(numgens S,i->random(kk)*Sgens_i))+ideal( sum(numgens S,i->random(kk)*Sgens_i)-1);
                EqT=ideal( sum((numgens J),i->(1-t*random(kk)*J_i)));
          
                Wt=Pol+Xs+EqT;
                --elapsedTime (gbWt2 := groebnerBasis(Wt, Strategy=>"F4");
		(gbWt2 = MyGb(Wt,"F4");    
                    tall2 = numColumns basis(cokernel leadTerm gbWt2););
                --elapsedTime (gbWt := groebnerBasis(Wt, Strategy=>"MGB");
                --tall1 := numColumns basis(cokernel leadTerm gbWt););
                --elapsedTime (
                --    gbWt0 := gens gb Wt;
                --    tall0 := numColumns basis(cokernel leadTerm gbWt0););
                --    tall= length (entries basis(R3/Wt))_0;);
                tall = tall2;
                --if tall != tall1 or tall != tall2 then error "screwed up line";
                --R9:=(R3/Wt)^1;
            
                --tall = degree(R9);
                --tall= length (entries gens gb Wt);
                );
            
            if opts.Method==Num then(
                -- <<"Using Bertini"<<endl;
                solutions=0;
                solutions1=0;
                Pol=sum ( k,jj-> ideal sum((numgens I),i->random(kk)*I_i*random(d-first(degree(I_i)),S)));
                Xs=sum((n-k),jj->ideal sum(numgens S,i->random(kk)*(gens(S))_i))+ideal( sum(numgens S,i->random(kk)*(gens(S))_i)-1);
           
                Wt=Pol+Xs;
                Wg=((entries gens(Wt))_0);
                try (
                    tall=0;
                    solutions= bertiniZeroDimSolve(Wg);
                    --solutions=bertiniRefineSols(Wg, solutions1, 20);
                    ind=length(solutions);
                    for j2 from 0 to ind-1 do (
                        for j3 from 0 to (numgens I)-1 do(
                            val5=sub(I_(j3),matrix({coordinates(solutions_(j2))}));
                            if (realPart(val5)>=1e-5 or imaginaryPart(val5)>=1e-5) then(
                                tall=tall+1;
                                break;
                                );
                            );
                        ); 
                    ) else tall =0;  
                );
           
            if opts.Method==Sat then(
                Pol2=sum ( k,jj-> ideal sum(njac,i->random(kk)*I_i*random(d-first(degree(I_i)),S)));
                K=saturate(Pol2,minDegGen);
                if K != ideal(vars(S)) then (tall=degree(K);) else (tall=0;);
                );
                 
            g#k=tall;
            ); 
        );
    ProjSeq:= toSequence g;
    --<<"g= "<<ProjSeq<<endl;
    return ProjSeq
    )
    
    
    
     
csmHyper = {Method => VspaceDim} >> opts-> (n,ChowRingPn,H,hyper) -> (
    jac:=ideal jacobian ideal hyper; 
    --<<"enter pd"<<endl;
    g:=projectiveDegree(jac,Method=>opts.Method);
    --<<"exit pd"<<endl;
    use(ChowRingPn);
    CSMHYP:=(1+H)^(n+1) - sum(0..n,d->g_d*(-H)^d*(1+H)^(n-d));
    return CSMHYP;
    )

beginDocumentation()

TEST ///
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=4;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    I=ideal((4*x_3*x_2*x_4-x_0^3)*x_1,(x_0*x_1*x_4-x_2^3)*x_3);
    J1=minors(numgens(I), jacobian I)+I;
    dim(Proj(R/(J1)))
    dim(Proj(R/I))
    time csm = CSM(I);
    time segre =Segre(I);
    


///

TEST ///
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=4;
    kk=ZZ/32749;
    R=kk[y_0..y_n];
    I=ideal(2*y_0^2+12*y_1^2+96*y_2^2 + 19*y_3^2+12*y_4^2, -y_0^2*y_4 + y_1*y_4^2);
    time csm = CSM(I);
    A = ring csm;
    h = (ring csm)_0;
    assert(csm == 8*h^4+6*h^3+6*h^2)
    seg = Segre I
    h = (ring seg)_0
    --Chern fulton class is
    CF=(1+h)^(n+1)*seg; 
    --unfortunately at the moment it is set up so that M2 will think that ring seg and ring csm are different rings... so if you wanted to 
    -- find the difference between the csm and CF class or something you would need to do:
    CF = sub(CF, vars (ring csm)) 
    csm-CF
///

TEST ///
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=4;
    kk=ZZ/32749;
    R=kk[y_0..y_n];
    I2=ideal(2*y_0^4+12*y_1^4+96*y_2^4 + 19*y_3^4+12*y_4^4, -y_0^2*y_4*y_0 + y_1*y_4^2*y_3);
    elapsedTime csm = CSM(I2);
    A = ring csm;
    h = (ring csm)_0;
    assert(csm == 148*h^4 - 28*h^3 + 16*h^2)
    seg = Segre I2
    h = (ring seg)_0
    --Chern fulton class is
    CF=(1+h)^(n+1)*seg; 
    assert(elapsedTime Euler I2 == 148)
    assert(seg == 768*h^4-128*h^3+16*h^2)
///

TEST ///
  -- This is a smooth example
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=4;
    kk=ZZ/32749;
    R=kk[y_0..y_n];
    I2 = ideal random(R^1, R^{-2,-2});
    elapsedTime csm = CSM(I2);
    e = Euler I2;
    seg = Segre I2
    A = ring csm;
    h = (ring csm)_0;
    seg = sub(seg, vars A) -- currently, seg and csm are in different rings
    assert((1+h)^(n+1) * seg == csm)
    assert(e == 8)
    assert(e==euler( variety I2))
    --FORMULA FROM FULTON FOR SEGRE
    segCI= product(0..numgens(I2)-1,i->((degree(I2_i))_0*h//(1+(degree(I2_i))_0*h)))
    assert(seg==segCI)
   
///

TEST ///
  -- This is another smooth example
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=11;
    kk=ZZ/32749;
    R=kk[y_0..y_n];
    I2 = ideal (random(3,R),random(3,R));
    seg = Segre I2
     A = ring seg;
    h = (ring seg)_0;
    --FORMULA FROM FULTON FOR SEGRE
    segCI= product(0..numgens(I2)-1,i->((degree(I2_i))_0*h//(1+(degree(I2_i))_0*h)))
    assert(seg==segCI)
  
    
   
///


TEST ///
  -- This is another smooth example
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=19;
    kk=ZZ/32749;
    R=kk[y_0..y_n];
    I2 = ideal (random(3,R),y_19*y_0*y_4-y_0^3,y_0*y_1*y_7-y_8^3,y_0*y_1*y_7-y_8^2*y_4-y_15^3);
    elapsedTime  seg = Segre I2
    A = ring seg;
    h = (ring seg)_0;
    --FORMULA FROM FULTON FOR SEGRE
    segCI= product(0..numgens(I2)-1,i->((degree(I2_i))_0*h//(1+(degree(I2_i))_0*h)))
    assert(seg==segCI)
  
    
   
///



TEST ///
  -- This is another smooth example
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=15;
    kk=ZZ/32749;
    R=kk[y_0..y_n];
    I2 = ideal (random(3,R),random(3,R),random(3,R));
   elapsedTime  seg = Segre I2
     A = ring seg;
    h = (ring seg)_0;
    --FORMULA FROM FULTON FOR SEGRE
    segCI= product(0..numgens(I2)-1,i->((degree(I2_i))_0*h//(1+(degree(I2_i))_0*h)))
    assert(seg==segCI)
  
    
   
///

TEST ///
  -- This is another smooth example
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=7;
    kk=ZZ/32749;
    R=kk[y_0..y_n];
    I2 = ideal (random(2,R),random(2,R),random(2,R));
    elapsedTime csm = CSM(I2);
    elapsedTime csm2=CSM(I2,Alg=>Composite);
    seg = Segre I2
    A = ring csm;
    h = (ring csm)_0;
    seg = sub(seg, vars A)
    csm2=sub(csm2,vars A)
     -- currently, seg and csm are in different rings
    --FORMULA FROM FULTON FOR SEGRE
    segCI= product(0..numgens(I2)-1,i->((degree(I2_i))_0*h//(1+(degree(I2_i))_0*h)))
    assert(seg==segCI)
    assert((1+h)^(n+1) * segCI == csm)
    assert((1+h)^(n+1) * segCI == csm2)
    
   
///

TEST ///
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=7;
    kk=ZZ/32003;
    R=kk[x_0..x_n];
    I=ideal(x_0*x_3-x_1*x_2, random(2,R),x_0^2*x_3-x_1*x_7^2);
    time p=CSM(I)
    h = (ring p)_0;
    assert(p == 22*h^7+14*h^6+36*h^5+26*h^4+12*h^3);
///

TEST ///
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=10;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    I=ideal(random(2,R),random(2,R),random(2,R));
    csm = time CSM(I,Alg=>Composite);
    h = (ring csm)_0;
    A = ring csm;
    seg=Segre(I)
    seg = sub(seg, vars A) --CSM from Fulton class (since this is a smooth CI)
    csmCI=(1+h)^(n+1) * seg
    assert(csm == csmCI)

    csm2 = time CSM(I);
    csm2=sub(csm2, vars A)
    assert(csm2==csmCI)
    
    

///

TEST ///
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=7;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    I=ideal((13/21)*x_0^2 + (7/5)*x_1^2 - (24/7)*x_2^2+ 13*x_3^2 + 8*x_4^2 -(17/6)*x_5^2 + 2*x_6^2 +(14/11)*x_7^2, x_1^2*x_5 - x_0^2*x_4);
    csm= time CSM(I)
    h = (ring csm)_0;
    assert(csm==26*h^6+34*h^5+36*h^4+20*h^3+6*h^2);
    

///

TEST ///
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=8;
    kk=ZZ/32749;
    R=kk[x_0..x_n];

    M = matrix{{random(1,R),random(1,R),random(1,R)},{random(1,R),random(1,R),random(1,R)},{random(1,R),random(1,R),random(1,R)},{random(1,R),random(1,R),random(1,R)}};
    I=minors(2,M);
    seg= time Segre(I)
    h = (ring seg)_0;
    assert(seg==405*h^8-84*h^7+10*h^6)
///

TEST ///
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=6;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    I=ideal((13/21)*x_0^2 + (7/5)*x_1^2 - (24/7)*x_2^2+ 13*x_3^2 + 8*x_4^2 -(17/6)*x_5^2 + 2*x_6^2,x_0*x_6-x_0^2,random(2,R));
    csmComp=time CSM(I,Alg=>Composite)
    A=ring csmComp;
    h = (A)_0;
    csmIE=time CSM(I);
    csmIE=sub(csmComp, vars A); 
    assert(csmComp==-8*h^6+20*h^5+12*h^4+8*h^3)
    h = (ring csmIE)_0;
    assert(csmIE==-8*h^6+20*h^5+12*h^4+8*h^3)
///

--Gardient multidegree (i.e. just projective degree) example. 
TEST ///
{*
  
    restart
    needsPackage "CharClassCalc"
*}
    n=7;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    f=random(1,R)*random(2,R);
    elapsedTime GradMultiDegree(f)
///

TEST ///
{*
  
    restart
    needsPackage "CharClassCalc"
*}
    n=9;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    I=ideal(random(3,R));
    elapsedTime CSM I
///    
