----------------------------------------------------
--Segre Examples
----------------------------------------------------


TEST ///
--Rational Normal curve in P^7
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=7;
    kk=ZZ/32749;
    R=kk[y_0..y_n];
    M = matrix{{y_0..y_n},{y_1..y_n,y_0}};
    I=minors(2,M);
    time Segre I
///
   
TEST ///
--Segre embedding of P^2xP^3 in P^11
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=11;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    M = matrix{{x_0,x_1,x_2,x_3},{x_4,x_5,x_6,x_7},{x_8,x_9,x_10,x_11}};
    I=minors(2,M);
    time Segre(I)
///    

TEST ///
--Smooth degree 81  variety in P^7
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=7;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    I = ideal(random(3,R),random(3,R),random(3,R),random(3,R));
    time Segre(I)
    
///
    
TEST ///
--Degree 10 variety in P^8 
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=8;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    M = matrix{{random(1,R),random(1,R),random(1,R)},{random(1,R),random(1,R),random(1,R)},{random(1,R),random(1,R),random(1,R)},{random(1,R),random(1,R),random(1,R)}};
    I=minors(2,M);
    degree I
    time Segre(I)
///

TEST ///
--Singular degree 21 variety in P^9
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=9;
    kk=ZZ/32749;
    R2=kk[x_0..x_n];
    I=ideal((4*x_3*x_2*x_4-x_0^3)*x_1^3,x_5^3*(x_0*x_1*x_4-x_2^3),x_9^3*(x_7*x_8*x_6-x_4^3)-x_7^5*x_0,7*x_1^3*(x_2*x_1*x_6-x_9^3)-3*x_2^3*x_0^3);
    degree I
    time Segre(I)
///

TEST ///
--Degree 48 in P^6
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=6;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    M = matrix{{random(4,R),random(4,R),random(4,R)},{random(4,R),random(4,R),random(4,R)}};
    I=minors(2,M);
    time Segre(I)
///



------------------------------------------------------------------------
--CSM Examples
------------------------------------------------------------------------

TEST ///
--Twisted Cubic
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=3;
    kk=ZZ/32749;
    R=kk[x_0..x_n];
    K=ideal(x_1*x_3-x_2^2, x_2*x_0-x_3^2,x_1*x_0-x_2*x_3)
    time CSM K
///

TEST ///
--Segre embedding of P^1xP^2 in P^5
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=5;
    kk=ZZ/32749;
    R=kk[y_0..y_n];
    I=ideal(y_0*y_4-y_1*y_3,y_0*y_5-y_2*y_3,y_1*y_5-y_4*y_2);
    time CSM I    
///

TEST ///
--Smooth degree 8 surface in P^4
{*
    restart
    needsPackage "CharClassCalc"
*}
    n=4;
    kk=ZZ/32749;
    R2=kk[z_0..z_n];
    K2=ideal(-11796*z_0^2 + 2701*z_0*z_1 + 10725*z_1^2 - 11900*z_0*z_2 - 11598*z_1*z_2+ 11286*z_2^2 + 5210*z_0*z_3 - 7485*z_1*z_3 + 11208*z_2*z_3 + 5247*z_3^2 -
4745*z_0*z_4 - 15915*z_1*z_4 + 14229*z_2*z_4 - 11236*z_3*z_4 + 10583*z_4^2,
6934*z_0^2 + 1767*z_0*z_1 + 9604*z_1^2 - 4343*z_0*z_2 - 10848*z_1*z_2 -
16357*z_2^2 + 8747*z_0*z_3 - 13140*z_1*z_3 - 7136*z_2*z_3 + 3115*z_3^2 -
3741*z_0*z_4 + 14969*z_1*z_4 + 10956*z_2*z_4 - 10016*z_3*z_4 + 13449*z_4^2,
12153*z_0^2 - 4789*z_0*z_1 - 9183*z_1^2 - 15107*z_0*z_2 - 5045*z_1*z_2 +
6082*z_2^2 - 13665*z_0*z_3 + 4455*z_1*z_3 - 3129*z_2*z_3 + 14146*z_3^2 -
1424*z_0*z_4 + 11305*z_1*z_4 + 4882*z_2*z_4 - 14665*z_3*z_4 - 10270*z_4^2)
    time CSM(K2)
    time euler Proj(R2/K2)
   
///

TEST ///
--Smooth degree 4 variety in P^10
{*
    restart
    needsPackage "CharClassCalc"
*}   
   n=10;
   kk=ZZ/32749;
   R=kk[x_0..x_n];
   I=ideal(random(2,R),random(2,R));
   time csm= CSM(I) 
   time euler Proj(R/I)
  
///

TEST ///
--Smooth degree 6 variety in P^7
{*
    restart
    needsPackage "CharClassCalc"
*}
   n=7;
   kk=ZZ/32749;
   R=kk[y_0..y_n];
   I=ideal(2*y_0^3+12*y_1^3+96*y_2^3 + 19*y_3^3+12*y_4^3+y_6^3+5*y_7^3, random(2,R));
   time euler Proj(R/I)
   time CSM(I)
   
///

TEST ///
--Degree 12 hypersurface in P^3
{*
    restart
    needsPackage "CharClassCalc"
*}
   n=3;
   kk=ZZ/32749;
   R4=kk[x_0..x_n];
   I4=ideal(x_2^6*x_3^6+3*x_1^2*x_2^4*x_3^4*x_0^2+3*x_1^4*x_2^2*x_3^2*x_0^4-3*x_2^4*x_3^4*x_0^4+x_1^6*x_0^6+21*x_1^2*x_2^2*x_3^2*x_0^6-3*x_1^4*x_0^8+3*x_2^2*x_3^2*x_0^8+3*x_1^2*x_0^10-x_0^12)
   time CSM(I4)
///

TEST ///
--Degree 3 surface in P^8
{*
    restart
    needsPackage "CharClassCalc"
*}
   n=8;
   kk=ZZ/32749;
   R=kk[x_0..x_n];
   M = matrix{{random(1,R),random(1,R),random(1,R)},{random(1,R),random(1,R),random(1,R)}};
   I=minors(2,M);
   time CSM(I)   
   degree I
///



TEST ///
--Singular degree 5 surface in P^10
{*
    restart
    needsPackage "CharClassCalc"
*}   
   n=10;
   kk=ZZ/32749;
   R=kk[x_0..x_n];
   M = matrix{{x_0^2-x_1^2,22*x_3-35*x_9-13*x_2,x_9-x_7+5*x_3},{x_8+9*x_0+4*x_1,7*x_1-33*x_5+23*x_6,random(1,R)}};
   I=minors(2,M);
   time csm= CSM(I)
   degree I
///
   


TEST ///
--Singular Degree 16 variety in P^5
{*
    restart
    needsPackage "CharClassCalc"
*}
   n=5;
   kk=ZZ/32749;
   R2=kk[x_0..x_n];
   I=ideal((4*x_3*x_2*x_4-x_0^3)*x_1,x_5*(x_0*x_1*x_4-x_2^3))
   time CSM(I)
///
