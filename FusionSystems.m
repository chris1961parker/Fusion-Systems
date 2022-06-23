//This file is created by Parker and Semeraro.
//It contains programs designed to calculate with fusion systems.  
//It also has programs to find all saturated fusion systems on 
//a given p-group with trivial $p$-core and $p$-quotient. 
//It can be easilly modified to find all saturated fusion systems if 
//so desired. Details can be found in  
//``Algorithms for fusion systems with applications 
//to $p$-groups of small order" by Parker and  Semeraro
//It also contains other functions that we found useful.
//It works on Magma V2.25-4.  Load the file by Attach("FusionSystems.m");

freeze;
declare type FusionSystem;
declare attributes  FusionSystem: prime, group, subgroups, borel, centrics, 
essentials, essentialautos, fusiongraph, maps, classes, AutF, saturated,
grpsystem, grppgrp, mapbackgrp;

declare attributes GrpMat: autogrp,  autoperm, autopermmap,autF;
declare attributes GrpPerm: autogrp, autoperm, autopermmap, autF;
declare attributes GrpPC: autogrp, autoperm, autopermmap, autF;
//////

////////////////////////////////////////////////////////////////////////////////
///A function which applies the inverse of an monomorphism  to a subgroup
/// j: W--> K
///////////////////////////////////////////////////////////////////////
intrinsic SubInvMap(j::Map,K::Grp,W::Grp)-> Grp
{applies inverse of a map to a subgroup}
k:= Inverse(j);
return sub<K| {k(x): x in Generators(W)},Kernel(j)>;
end intrinsic;


///////////////////////////////////////////////////////////// 
///A function which applies an homomorphism  to a subgroup
/// j: W--> K
//////////////////////////////////////////////////////////// 
intrinsic SubMap(j::Map,K::Grp,W::Grp)-> Grp{applies a map to a subgroup}
return sub<K| { j(x): x in Generators(W)}>;
end intrinsic;

//////////////////////////////////////////
//////A function which   creates a homomorphism 
//////from a conjugation map. 
//////Here $X \le G$, $Y \le G$ and  $g\in G$ with //////$X^g \le Y$.
/////////////////////////////////////////

intrinsic ConjtoHom(X::Grp, Y::Grp,g::GrpElt)->GrpHom
{Return the homomorphism induced by conjugation}

require  X^g subset Y: "X not conjugate in Y by g"; 
alpha:=hom<X->Y|x:->x^g>;
return alpha;
end intrinsic;
/////////////////////////////////////////////////
intrinsic ConjtoAuto(X::Grp,g::GrpElt,AA::GrpAuto)->GrpAutoElt

{Return the automorphism induced by conjugation}

require  X^g subset X: "X not not normalized by g"; 
MakeAutos(X);
alpha:=AA!hom<X->X|x:->x^g>;
return alpha;
end intrinsic;
//////////////////////////////////////////////
/////creates all the aspects of aut groups.
////////////////////////////////////////////
intrinsic MakeAutos(x::Grp)
{Makes an automorphism group and its permutation representation}
if assigned(x`autogrp) then return; end if;
 x`autogrp := AutomorphismGroup(x);
    x`autopermmap, x`autoperm:= PermutationRepresentation(x`autogrp); 
   // return x`autogrp;
end intrinsic;
/////////////////////////////////////////////////////////////
//A function which for $X$ normal in $Y$ creates $Aut_Y(X)$. 
////////////////////////////////////////////////////////////

intrinsic AutYX(Y::Grp,X::Grp)-> GrpAuto
{Creates the automorphism group of X induced by conjugation by elements of Y}
require IsNormal(Y,X):"X is not a normal subgroup of Y";
MakeAutos(X); 
A:= sub<X`autogrp|{ConjtoHom(X,X,y):y in Generators(Y)}>;
return A;
end intrinsic;

/////////////////////////////////////////////////////////////
//Creates Inn(X). 
////////////////////////////////////////////////////////////

intrinsic Inn(X::Grp)-> GrpAuto
{Creates the inner automorphism group of X}
 
 A:= AutYX(X,X);
return A;
end intrinsic;
////////////////////////////////////////////////////////////////////////
//////////// Making automizers of specified subgroups in group fusion systems.
/////////////////////////////////////////////////////////////////////////
intrinsic Automiser(G::Grp,P::Grp)->GrpAuto
{Given a subgroup of a group, determine the automiser of that subgroup}
H:= Normalizer(G,P);
A:=AutYX(H,P);
return(A);
end intrinsic;
///////////////////////////////////////////////////
intrinsic Automizer(G::Grp,P::Grp)->GrpAuto{Just another name for Automiser}
return Automiser(G,P);
end intrinsic;
////////////////////////////////////////////////////
intrinsic AutomiserGens(G::Grp,P::Grp)->SetEnum
{Given a subgroup of a group, determine the a set of automorphism which generate the automiser}
H:= Normalizer(G,P);
A:= {ConjtoHom(P,P,y):y in Generators(H)};
return A;
end intrinsic;
/////////////////////////////////////////////////////
/// IsCharacteristic(G,H): does what it suggests
////////////////////////////////////////////////////////

intrinsic IsCharacteristic(G::Grp,H::Grp)->Bool
{Checks if subgroup H of G is characteristic}
require H subset G:"second term is not a subgroup of first";
MakeAutos(G);
for a in Generators(G`autogrp) do
if (a(H) eq H) eq false then return false; end if;
end for;
return true;
end intrinsic;




intrinsic IsInvariant(A::GrpAuto,G::Grp,H::Grp)->Bool
{Checks if subgroup H is invariant under the automorphisms A of G }
require H subset G:"second term is not a subgroup of first";
MakeAutos(G);
for a in Generators(A) do
if (a(H) eq H) eq false then return false; end if;
end for;
return true;
end intrinsic;






///////////////////////////////////////
////// IsStronglypEmbeddedMod(G,Ker,p): 
//////does G contain a Strongly p-embedded subgroup?
////////////////////////


intrinsic IsStronglypEmbeddedMod(G::Grp,ker::Grp,p::RngIntElt)->Bool
{Determines whether G/ker has a strongly p-embedded subgroup}
Sylow:=sub<G|SylowSubgroup(G,p),ker>; 
  if IsNormal(G,Sylow) then return false; end if;
        SSylow:= {sub<G|x`subgroup,ker>:x in Subgroups(Sylow:OrderEqual:=p*#ker)}; 
        HS:= sub<G|{Normalizer(G,x):x in SSylow}>;
        HS:= sub<G|HS,Normalizer(G,Sylow)>;
       if #HS eq #G then return false; end if;
return true;
end intrinsic;


 
//////////////////////////////////////////////////////////////////////////////
////// IsStronglypEmbedded(G,p): does G contain a Strongly p-embedded subgroup?
////USES GLS2 Proposition 17.11
///////////////////////////////////////////////////////////////////////////

intrinsic IsStronglypEmbedded(G::Grp,p::RngIntElt)->Bool
{returns true if G has a strongly p-embedded subgroup}
require #G mod p eq 0:"the group has trivial Sylow p-subgroup";

Sylow:=SylowSubgroup(G,p);

 if #pCore(G,p) ne 1 then return false; end if;
 CCl:= ConjugacyClasses(Sylow); 
 XX:={x[3]: x in CCl|x[1] eq p}; 
 if #XX ne p-1 and  IsSoluble(G) then return false; end if; 
   RR:=[];
   HS:= Normalizer(G,Sylow);
   F:= ConjugacyClasses(HS); 
   for x in F do 
	   if x[1] eq p then 
	    	HS:=sub<G|HS, Normalizer(G,sub<G|x[3]>)>; 
	   end if;
       if HS eq G then return false; end if;
   end for; 
return true;
end intrinsic;

//////////////////////////////////
/////Selects a  random automorphism in Aut(Q). 
///////////////////////////////////

intrinsic RandomAuto(A::GrpAuto)->Map
{Selects a  random element from the automorphism group}
a,B:=  PermutationRepresentation(A);
alpha := Inverse(a)(Random(B));
return alpha;
end intrinsic;



////////////////////////////////////////////////////////////////////////////
/////// This makes orbits of automorphism group on subgroups.
///////Here Q is a subgroup of P and AFP \le Aut(P). We 
///////determine Q^A=[Q,Q2,\dots Qs] and N_A(Q)
////// Elt is a sequence of elements [w1,w2, dots, ws] 
////// which map elements of the Q to the corresponding element Qi.
///////////////////////////////////////////////////////////////////////////

intrinsic AutOrbit(P::Grp,Q::Grp,AFP::GrpAuto:Printing:=false)->SeqEnum,Grp,SeqEnum
{ Determines the orbits of a subgroup Q under the automorphism group AFPQ of 
of P}
   require Q subset P:"the second term in not a subgroup of the first";
    MakeAutos(P);
    N:= Normalizer(P,Q);
    gamma:= P`autopermmap;
    Pp:=P`autoperm;
    StB:= sub<AFP|{ ConjtoAuto(P,n,AFP):n in Generators(N)}>; 
    StBp:= sub<Pp| {gamma(ConjtoAuto(P,n,P`autogrp)):n in Generators(N)}>;
    T:= Transversal(P,N); 
    Elt:= [ConjtoAuto(P,n,AFP):n in T];
    EltOrig:=Elt;
    Orb:= [Q^n:n in T];

    afp:= #AFP;
    while afp ne #StB*#Orb do  if Printing then  afp,  #StB*#Orb; end if; 
        alpha:= RandomAuto(AFP);  
    
            Q:= Orb[1];
            Qwalpha :=  SubMap(alpha, P, Q);
             y:= Index(Orb,Qwalpha);
             //if y ne 0, then Qwalpha is in the orbit and we add a generator to StB. 
             if y ne 0 then
                alphanew :=   alpha*Elt[y]^-1; 
                alphanewp:=gamma(P`autogrp!alphanew); 
                if alphanewp in StBp eq false then
                    StB:= sub<AFP|StB,alphanew>; 
              StBp:= sub<P`autoperm|StBp,alphanewp>;
                    if  afp eq #StB*#Orb then  return Orb, StB, Elt; end if;
              end if;  
             end if;
             //if y eq 0, then we have a new element for the orbit.
             if y eq 0 then
                    Eltw:= [AFP!(e*alpha):e in EltOrig];
                    Orbw:= [e(Q): e in Eltw];       
                    Orb:= Orb cat Orbw;
                    Elt := Elt cat Eltw; 
                    if  afp eq #StB*#Orb then   return Orb, StB, Elt ;end if;
             end if;
   

    end while;    
    return Orb, StB, Elt;
end intrinsic;

intrinsic AutOrbitOld(P::Grp,Q::Grp,AFP::GrpAuto)->SeqEnum,Grp,SeqEnum
{ Determines the orbits of a subgroup Q under the automorphism group A of 
of P}
   require Q subset P:"the second term in not a subgroup of the first";
    MakeAutos(P); 
    N:= Normalizer(P,Q);
    gamma:= P`autopermmap;
    Pp:=P`autoperm;
    StB:= sub<AFP|{ ConjtoHom(P, P,n):n in Generators(N)}>; 
    StBp:= sub<Pp| {gamma(P`autogrp!ConjtoHom(P, P,n)):n in Generators(N)}>;
    T:= Transversal(P,N); 
    Elt:= [AFP!ConjtoHom(P, P,n):n in T];
    Orb:= [Q^n:n in T];

    afp:= #AFP;
    while afp ne #StB*#Orb do  
        alpha:= RandomAuto(AFP); 
        for w in [1..#Orb] do
            W:= Orb[w];
            Qwalpha :=  SubMap(alpha, P, W);
             y:= Index(Orb,Qwalpha);
             //if y ne 0, then Qwalpha is in the orbit and we add a generator to StB. 
             if y ne 0 then
                alphanew :=   Elt[w]*alpha*Elt[y]^-1; 
                alphanewp:=gamma(P`autogrp!alphanew); 
                 if alphanewp in StBp eq false then
                    StB:= sub<AFP|StB,alphanew>; 
               StBp:= sub<P`autoperm|StBp,alphanewp>;
                    if  afp eq #StB*#Orb then    return Orb, StB, Elt; end if;
              end if; 
             end if;
             //if y eq 0, then we have a new element for the orbit.
             if y eq 0 then 
                    Nwalpha:= Normalizer(P,Qwalpha); 
                    Tw:= Transversal(P,Nwalpha);
                    Eltw:= [AFP!(Elt[w]*alpha*ConjtoHom(P, P,n)):n in Tw];
                    Orbw:= [Qwalpha^n:n in Tw];
                    Orb:= Orb cat Orbw;
                    Elt := Elt cat Eltw; 
                    if  afp eq #StB*#Orb then   return Orb, StB, Elt; end if;
             end if;
        end for;  

    end while;
    
    return Orb, StB, Elt;
end intrinsic;
///////////////////////////////////
//////We do the same thing for elements
/////////////////////////////////////
intrinsic AutOrbit(P::Grp,Q::GrpElt,AFP::GrpAuto)->SeqEnum,Grp,SeqEnum
{ Determines the orbits of an element Q under the automorphism group A of 
of Aut(P)}
   require Q in P:"the second term in not a subgroup of the first";
    Orb:= [Q];
    Elt:= [Identity(AFP)];
    NN:= sub<AFP| >;
    while #AFP ne #NN*#Orb do
        xx:= RandomAuto(AFP);
        for W in Orb do
            Qwx :=  xx(W);
            w:= Index(Orb,W);
                if Qwx in Orb then y:= Index(Orb,Qwx);
                    NN:= sub<AFP|NN,Elt[w]*xx*Elt[y]^-1>;
                else
                    Orb := Append(Orb,Qwx);   Elt := Append(Elt,Elt[w]*xx); 
                end if;
        end for; 
    end while;
    return Orb, NN, Elt;
end intrinsic;


////////////////
/// IsSCentric(S,P)
//////////////////

intrinsic IsSCentric(S::Grp,P::Grp)->Bool
{Is the subgroup P of S  S-centric?}
require P subset S:" the second term is not a subgroup of the first";
 if Centralizer(S,P) subset P then return true; end if;
 return false;
end intrinsic;

///////////////////
intrinsic FocalSubgroupTest(B::Grp,S::Grp, Essentials::SeqEnum,AutF::Assoc)->
Bool,Grp{Tests if S eq Focal subgroup in potential system};
Foc:=sub<S|{(s,b):s in Generators(S),  b in Generators(B)}>;
for e in Essentials do  
Foc:= sub<S|Foc, {x^-1*aa(x): x in e, aa in Generators(AutF[e])}>;
end for;
return Foc eq S, Foc;
end intrinsic;

///////////////////////////////
intrinsic AutFCore(Es::SeqEnum,AutE::SeqEnum)->Grp,GrpAuto
{calculates F core and action on it}
F:= Es[1];
for i := 2 to #Es do  F:= F meet Es[i];end for; 
 Fn:= sub<F|>;
 while F ne Fn do
 Fn:= F;
 for i := 1 to #Es do
    A:= AutOrbit(Es[i],F,AutE[i]);
    for x in A do F := F meet x; end for;
 end for;
 end while;
MakeAutos(F); K:= Inn(F); 
    for i := 1 to #Es do  K:=  sub<F`autogrp|K,Generators(AutE[i])>; end for;
    return F,K;
end intrinsic;
//////////////////////////////
intrinsic RadicalTest(S::Grp,P::Grp)->Boolean{Checks if P could be a radical subgroup}
 A:=AutYX(Normalizer(S,P),P);
	Ap:= SubMap(P`autopermmap,P`autoperm ,A);
		Inner:= Inn(P);
	Innerp:= SubMap(P`autopermmap,P`autoperm ,Inner);
RadTest:=#(Ap meet pCore(P`autoperm, FactoredOrder(S)[1][1])) eq  #Innerp;
return RadTest;
end intrinsic;
//////////////////////////////
intrinsic CentreTest(B::Grp,S::Grp, Essentials::SeqEnum,AutF::Assoc)->
Bool{Tests is action on Z(S) by B and that induced by memebers of AutF is consistent};
Z:= Centre(S);
ZB:=  AutYX(B,Z);
ZA:= sub<Z`autogrp|>;
for e in Essentials do 
Orb, NN:=  AutOrbit(e,Z,AutF[e]);
ZA := sub<Z`autogrp|ZA,Generators(NN)>;
end for;
TT:={x in ZB: x in Generators(ZA)};
return TT eq {true};
end intrinsic;

///////////////////////////////

intrinsic CentreTest(B::Grp,S::Grp,P::Grp,A::GrpAuto)->
Bool{Tests is action on Z(S) by B and that induced by members of A is consistent};

ZS:= Centre(S);
SubZ:= Subgroups(ZS);
for zz in SubZ do 
    Z:= zz`subgroup; if #Z eq 1 then continue; end if;
    ZB:=  AutYX(Normalizer(B,Z),Z);
    Orb, NN:=  AutOrbit(P,Z,A);
    ZA:= sub<Z`autogrp|Generators(NN)>;
    TT:={x in ZB: x in Generators(ZA)};
    if TT ne {true} then return false; end if; 
end for;

return true;
end intrinsic;

///////////////////////////////

intrinsic FCoreTest(S::Grp,Essentials::SeqEnum, AutF::Assoc)->Bool, Grp
{Test is F core is trivial and returns FCore}
F:= S; FC:= sub<S|>; AA:=Append(Essentials,S);
for x in Essentials do F := F meet x; end for;
SF:=[x`subgroup:x in  NormalSubgroups(F)];
SF:= Reverse(SF);

  

for x in SF do 
 if IsNormal(S,x) eq false then continue x; end if;
    for E in AA do
        for y in Generators (AutF[E]) do
            for xx in Generators(x) do
                if y(xx) in x eq false   then 
                continue x; end if;
            end for;
        end for;
    end for;
    FC:= sub<S|x>; break;
 end for;
 
 
return #FC eq 1, FC;

end intrinsic;
 

/////////////////////////////////
///////can Q be a sylow of a group with s strongly p-embedded subgroup
/////////////////////////////////
intrinsic IsStronglypSylow(Q::Grp)->Bool, Bool
{Can Q be the Sylow subgroup of a group with a strongly p-embedded Sylow p? Also returns whether cyclic or quaternion}

p:= FactoredOrder(Q)[1][1];

QC:=IsQuaternionOrCyclic(Q);
    if QC eq false then
   
X:=PCGroup(CyclicGroup(p));
Y:=X;
Testers:={};
for i := 1 to 7 do 
Y:= DirectProduct(Y,X); Testers:= Testers join{Y};
end for;

Testers:= Testers join{
PCGroup(ClassicalSylow(SU(3,p), p)),
PCGroup(ClassicalSylow(SU(3,p^2), p))};
if p eq 3 then Testers:= Testers join {PCGroup(Sylow(PGammaL(2,8),3))}; end if;
if p eq 2   then Testers:= Testers join {PCGroup(Sylow(ChevalleyGroup("2B",2,8),2))}; end if;
if p eq 5   then Y:= sub<Sym(25)|
   (6, 10, 9, 8, 7)(11, 14, 12, 15, 13)(16, 18, 20, 17, 19)(21, 22, 23, 24, 25),
    (1, 11, 23, 10, 19, 2, 12, 24, 6, 20, 3, 13, 25, 7, 16, 4, 14, 21, 8, 17, 5,
        15, 22, 9, 18)>; 
Testers:= Testers join {PCGroup(Y)}; end if;

 
        ///If QC is not quaternion or cyclic, then Out_F(P) cannot be soluble. 
        //So there should be 3 or more prime factors by ///Burnside#s p^aq^b theorem. 
        //Next we know that if not quaternion or cyclic, then Q should be isomorphic to one of 
        //the Sylow's listed above. Because we are assuming that $|S|$ is small, testers suffices. Can easily add more.
        //// We check that |Q|\le p^7 just in case.
        if #Q le p^7 then TesT:= false;
            for SP in Testers do 
             if    IsIsomorphic(Q,SP) then TesT := true; break; end if;
            end for;
         if TesT eq false  then return false,_; end if;
        end if;
    end if;
return true, QC;
end intrinsic;
 

/////////////////////////////////
/////////////AutFPCandidates.
/////////////////
intrinsic AutFPCandidates(B::Grp,S::Grp,P::Grp,ProtoEssentials::SeqEnum,Cand::Assoc, FirstTime::BoolElt:Printing:=false)->Assoc
{determines possible automisers of possibly protoessentail subgroups}

p:= FactoredOrder(S)[1][1];
ZZ:= Integers();
NSP:= Normalizer(S,P);

 ///////////////////////////////////////////////////////
 /////This checks if the automiser of N_S(P) comes from B.
 /////if it does, then this forms the basis of a check for consistency
 ////For this we require that N_S(P) doesn't have any morphisms 
 ///from essentail subgroups. I.e |N_S(P)| > |E| for all E essential.
  //////////////////////////////////////////////////////////
max:= Max({#ee:ee in ProtoEssentials});
maxenough := false;
if #NSP gt max then maxenough:= true; end if;
 
if #NSP eq max and  not exists(t){x:x in ProtoEssentials| IsConjugate(B,NSP,x)}  then maxenough:= true; end if;
 
 
//The next test  
 
 PC:= Core(S,P);
 if Index(NSP,P) eq p and Index(S,NSP) eq p and 
    Index(P,PC) eq p and IsCharacteristic(NSP,PC) then 
        if p ge 5 then maxenough:=true;  end if;
        if p in {2,3} and exists(x){x:x in ProtoEssentials| IsConjugate(B,NSP,x)} 
        then a,b:= IsConjugate(B, x,NSP);
        beta:= ConjtoHom(x,NSP,b); 
        alpha:= ConjtoHom(NSP,x,b^-1);
        Z:= Conjugates(S,P);
        if 
        forall{mm: mm in x`autF |  
                    exists{gamma: gamma in Generators(mm)|not SubMap( beta*gamma*alpha,NSP,P) in Z}} 
                    then maxenough:= true; 
        end  if;
        end if;
 end if;      
        
    
         
 

 

MakeAutos(P);
AutP:=P`autogrp;
mapP:= P`autopermmap;
AutPp:= P`autoperm;
InnP:=AutYX(P,P);
InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
AutSP:=AutYX(Normalizer(S,P),P );
AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>;
AutBP:=AutYX(Normalizer(B,P),P );
AutBPp:=sub<P`autoperm|{mapP(g): g in Generators(AutBP)}>;
NormAutSPp:=Normalizer(AutPp,AutSPp);
 

Candidates :=[];
 

 
 ct:= 0;
for Ga in Cand[P] do ct:= ct+1;  
//if Printing then if ct mod 10 eq 1 then print "done (modulo 10)", ct, "of ", #Cand[P]; end if; end if;
    
    GG:=SubMap(mapP,AutPp,Ga);  
    NGSP:= Normalizer(GG,AutSPp);
    SubsNGSP := Subgroups(NGSP:OrderMultipleOf:= #AutSPp); 
    
    TGG:={};
    
    if FirstTime then
        if  maxenough  then vv, ww:= IsConjugate(NormAutSPp,NGSP,AutBPp); 
            if vv then TGG:= TGG join {GG^ww}; else continue Ga; end if;
            else flag:=false;
            for subNGSP in  SubsNGSP  do 
                sw:= subNGSP`subgroup;   
                vv, ww:= IsConjugate(NormAutSPp,sw,AutBPp); 
                if vv then  TGG:= TGG join {GG^ww}; flag := true; end if; 
            end for; 
            if flag eq false then  continue Ga; end if;
        end if;//maxenough
    NormAutBPp:=Normalizer(AutPp,AutBPp);
     
      
        for GG in TGG do  
          //This uses Sylow's Theorem 
          NGP:= Normalizer(GG,AutSPp);  
          GGa:=sub<AutP|{Inverse(mapP)(g):g in Generators(GG)}>;
          NGPa:=sub<AutP|{Inverse(mapP)(g):g in Generators(NGP)}>;  
           
          NormAutBPa:= sub<AutP|{Inverse(mapP)(g):g in Generators(NormAutBPp)}>;
          XX,YY:=AutFCore([S,P],[AutYX(B,S),sub<AutP|NGPa,NormAutBPa> ]);
          BBB:=SubMap(XX`autopermmap,XX`autoperm,AutYX(B,XX)); 
          SSS:=SubMap(XX`autopermmap,XX`autoperm,AutYX(S,XX));
          NGPap:=SubMap(XX`autopermmap,XX`autoperm,NGPa);
          NormAutBPXXa:= sub<XX`autogrp |{(Inverse(mapP)(alpha)): alpha in
            Generators(NormAutBPp)}>; 
          NormAutBPXXap:= SubMap(XX`autopermmap,XX`autoperm,NormAutBPXXa);
          Tran1:= Transversal(NormAutBPXXap,Normalizer(NormAutBPXXap,NGPap));
          
          if Printing then   print "Tran1 has ", #Tran1, "elements";  end if;
          ToB :={};
             for tr in Tran1 do 
                YY2:= sub<XX`autoperm|NGPap^tr,BBB>; 
                ToB:= ToB join {BBB eq Normalizer(YY2,SSS)}; 
                if true in ToB then   break tr; end if;
             end for; 
          if ToB eq {false} then continue GG; end if; 
           
          
          Transv:=Transversal(NormAutBPp,Normalizer(NormAutBPp,GG));  
          if Printing then   print "Transv has ", #Transv, "elements";  end if;

                for aa in Transv  do 
                    NGPxx:= NGP^aa;
                    NGPxxa:=sub<AutP|{Inverse(mapP)(alpha):alpha in Generators(NGPxx)}>;
                    YYY1:=SubMap(XX`autopermmap,XX`autoperm,sub<XX`autogrp|{w: w in Generators(NGPxxa)}>);
                    YYY:=sub<XX`autoperm|YYY1,BBB>; 
                    if  (Normalizer(YYY,SSS) eq BBB)  then 
                        NewSub:=sub<AutP|{Inverse(mapP)(gg^aa): gg in Generators(GG)}>; 
                        for xxx in Candidates do 
                        	if xxx eq NewSub then continue aa; end if; 
                        end for;
                        Append(~Candidates,NewSub); 
                    end if;
                end for;//aa
           end for;//GG
           end if;

    
    if FirstTime eq false then   
        if  maxenough  then 
            if AutBPp subset GG  
            then  
            Append(~Candidates,Ga);  
             
            end if; 
        else 
            Append(~Candidates,Ga); 
          
        end if;
    end if;
    
end for;//Ga
  
if Printing then print  "In AutFPCand we find", #Candidates, "candidates";end if;

return  Candidates; 
end intrinsic;



//////////////////////////////////////////////////////
////We now start to make some functions specific for fusion systems
//////////////////////////////////////////////////////////////////


intrinsic CreateFusionSystem(Autos::SeqEnum) -> FusionSystem
{Creates the FusionSystem from automiser sequence. 
The first term in always the group on which the fusion system is 
erected. We make everything into a PCGrp }
 
require forall{A:A in Autos|Type(A) eq GrpAuto}: 
"Tuple entries not all automorphism groups"; 
F:= New(FusionSystem);
  
S1:= Group(Autos[1]);
p:= FactoredOrder(S1)[1][1];
F`prime:=p;


bounds:=[8,6,6,6];
primes:=[2,3,4,4];
///Puts the essentials in the standard order using group names.  
//This will break if order of S is too big. Hence the else below
 
if p in primes and #S1 le p^bounds[Index(primes,p)]  then  
RO:=[IdentifyGroup( Group(x)):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos);
else
RO:=[#Group(x):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos); 
end if; 
    
  
InnS1:=AutYX(S1,S1);   
AutS1:=S1`autogrp;
map:=S1`autopermmap;
AutSp:= S1`autoperm;
  
   
//////////////////////////////////////////////////
///We now  make the Borel subgroup and make things into a PCgrp.
////////////////////////////////////////////////// 
InnFp:=sub<AutSp|{map(g): g in Generators(InnS1)}>;
AutFSp:=sub<AutSp|{map(g): g in Generators(Autos[1])}>;  
  C:=Random(Complements(AutFSp,InnFp));  
C:=SubInvMap(map,AutS1,C); 
if #C gt 1 then 
     Ba, phi1:= Holomorph(GrpFP,S1,C); 
     Sa:= sub<Ba|[phi1(x):x in Generators(S1)]>; 
     phi2:=iso<Sa->S1|[<phi1(S1.i),S1.i>: i in [1..#Generators(Sa)]]>; 
     L:= sub<Ba|{x: x in Generators(Ba)| not x in Sa}>;  
     theta, Bb:= CosetAction(Ba,L); B,thetaB:= PCGroup(Bb);
    phiB:= phi1*theta*thetaB; 
    S:= sub<B|[phiB(x):x in Setseq(Generators(S1))]>;
    InvphiB := Inverse(thetaB)*Inverse(theta)*phi2;
   
     else
     B:= S1; 
     B,phiB:= PCGroup(B); InvphiB := Inverse(phiB);
end if;
S:= phiB(S1); 
F`group:= S;    
F`borel:= B;  
  
  MakeAutos(S);
  F`essentialautos:= [];
   F`essentials:=[phiB(Group(Autos[i])):i in [1..#Autos]];
 for x in F`essentials do MakeAutos(x); end for;
    for ix in [1..#Autos] do
        x:= F`essentials[ix];  
   XX:=sub<x`autogrp|[InvphiB*w*phiB:w in Generators(Autos[ix])]>; 
    
    F`essentialautos:= Append( F`essentialautos,XX); 
    end for;
  
////////////////////////
////The essentials and essential autos have been assigned. 
////We treat S as an essential. 
////////////////////////

////////////////////////
//////We now create all the subgroups of the fusion system up to B conjugacy 
//////Perhaps this could be done later.
//////////////////////
subsBS:=Subgroups(B: OrderDividing:=#S);

////////////////////////
//////Perhaps the algorithm doesn't select our essentials as representatives of 
/////their B-conjugacy class. We correct this
//////////////////////

//
F`subgroups:=[x`subgroup:x in subsBS];
for ii := 1 to #F`essentials do
    X:= F`essentials[ii];
    if X in F`subgroups eq false then 
        for jj in [1..#F`subgroups] do
            w:= F`subgroups[jj];
            if IsConjugate(B,w , X) then   F`subgroups[jj]:= X; break jj; end if;
        end for;
    end if;
end for;
//////////////////////////////////////////
///////We initialise F`AutF and place in the automorphism of essentials 
///////////////////////////// 
F`AutF:= AssociativeArray(F`subgroups);

for x in F`essentials do 
   F`AutF[x] := F`essentialautos[Index(F`essentials,x)]; 
end for; 

//We make all autos of S-centric subgroups. Perhaps this is a place we can save
//memory
for ii in [1..#F`subgroups] do 
x:= F`subgroups[ii]; 
if IsSCentric(S,x) then 
MakeAutos(x);end if; end for;
 
return F;
end intrinsic;



///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////


intrinsic Print(F::FusionSystem)
{Print F}

E:= [(#F`essentialautos[i]*#Centre(F`essentials[i]))/#F`essentials[i]:i in [2.. #F`essentialautos]];
E1:= [#F`essentials[i]:i in [2.. #F`essentials]];
printf "Fusion System with %o", #F`essentials-1; printf "\ F-classes of essential subgroups", "\n"; 
printf "\nThey have orders: %o", E1, "\n"; 
printf "\Out_F(E)  have orders: %o", E; printf 
"\nOut_\F(S) has order  %o", #F`essentialautos[1]/#Inn(F`group);
if assigned(F`grpsystem) then
printf "\nThis is a group fusion system\n"; end if;
end intrinsic;
//////////////////////////////////////////////////////////////
 //////////////Are two fusion systems equal?
//////////////////////////////////////////////////////////////
intrinsic 'eq'(F1::FusionSystem, F2::FusionSystem) -> Bool
{checks if two fusion systems are equal}
    E1:= F1`essentialautos;
    E2:= F2`essentialautos;
    Eq := true;
    if #E1 ne #E2 then return false; end if; 
    for x in E1 do
        for y in E2 do
            if x eq y then continue x; end if;
        end for;
        Eq:= false;
        if Eq eq false then break x; end if;
    end for;
    
    return Eq;
end intrinsic;
//////////////////////////////////////////////////////////////////////////
 //Given a subgroup Q and a morphism Q -> S in F, calculate NPhi. 
////Requires various functions already to be loaded.
//////////////////////////////////////////////////////////////////////////


 intrinsic NPhi(S::Grp, Q::Grp,phi::Map)->Grp
 {for a subgroup and homomorphism from the second 
 term to the first create the control subgroup}
 P:=Image(phi);
 phii:=iso<Q->P|x:->phi(x)>;
 TSP:= Transversal(Normalizer(S,P),Centralizer(S,P));
 Nphi:= Q;
 T:= Transversal(Normalizer(S,Q),Q);
    for t in T do
            if t in Nphi then continue; end if;
        alpha:=ConjtoHom(Q,Q,t);
        beta :=iso<Q->P|x:-> phii(alpha(x))>;
            for g in TSP do
                gg:= ConjtoHom(P,P,g);
                betag :=iso<Q->P|x:-> gg(phii(x))>;
                    if homeq(beta,betag) then   
                        Nphi:= sub<S|Nphi,t>; break; 
                    end if;
            end for;
    end for;
return Nphi;
end intrinsic;

 
////////////////////////
////Determines O_p(\F). This is used when F is defined, 
////if testing if potential automiser sequence, then we use FCoreTest
/////////////////////////
//


intrinsic Core(F::FusionSystem)->Grp
{Returns  F core }
FF:= F`group; 

FC:= sub<FF|>; AA:=Append(F`essentials,FF);
for x in F`essentials do FF := FF meet x; end for;
SF:=[x`subgroup:x in  NormalSubgroups(FF)];
SF:= Reverse(SF);

  
AutF:= F`AutF;
for x in SF do 
 if IsNormal(F`group,x) eq false then continue x; end if;
    for E in AA do
        for y in Generators (AutF[E]) do
            for xx in Generators(x) do
                if y(xx) in x eq false   then 
                continue x; end if;
            end for;
        end for;
    end for;
    FC:= sub<FF|x>; break;
 end for;
 
 
return #FC eq 1, FC;
end intrinsic;
//
///////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
/////FocalSubgroup #Uses 1.8 from AOV to determine the focal subgroup. 
///////////////////////////////////////////////////////////////////////


intrinsic FocalSubgroup(F::FusionSystem)->Grp
{Creates the focal subgroup of the fusion system}
S:= F`group;  
Foc:=sub<S| >;
for e in F`essentials do 
    i:= Index(F`essentials,e);
    AutFE:= F`essentialautos[i];
    Foc:= sub<S|Foc, {x^-1*aa(x): x in e, aa in Generators(AutFE)}>;
end for;
return Foc;
end  intrinsic;
 

//////////////////////////////////////////////////////
///////////////////////////////////////////////
//This determines a graph with edges AB   for A and B 
// subgroups of an essential subgroup E with A and B Aut_F(E) 
//conjugate. The connects components are the S-classes which have 
//union the p-class. It then completes the connected components to complete 
//graphs Maps contains and element 
//Maps[i,j]:SS[i]->SS[j]
///////////////////////////////////////////////


intrinsic FusionGraph(F::FusionSystem)->GrphUnd, Assoc
{Returns the labeled fusion graph}

if assigned(F`fusiongraph)  then return F`fusiongraph,F`maps; end if;

Essentials := F`essentials;
SS:= F`subgroups;
S:= F`group;
B:=F`borel;
Gamma := Graph<#SS|>;
SSxSS:= [[n,m]:n in [1..#SS],m in [1..#SS]];
Maps:=AssociativeArray(SSxSS);


for E in Essentials do 
    	if E eq S then continue E; end if; 
    
	NBE := Normalizer(B,E);
    	SubsE := Subgroups(NBE:OrderDividing:= #E);
    	SSSE:={x`subgroup:x in SubsE|x`subgroup subset E};
	    while #SSSE ne 0 do
		Q:= Rep(SSSE);
		for X in SS do
		    a,h:= IsConjugate(B,X,Q); 
		    if a then
		        v:= Index(SS,X); 
		        g:=ConjtoHom( SS[v], Q,h); 
                g1 :=ConjtoHom(Q, SS[v],h^-1); 
		        break;
		    end if;
		end for;
	    Orb, NN, Elt := AutOrbit(E,Q,F`essentialautos[Index(F`essentials,E)]);
		for x in Orb do 
		    if IsConjugate(B,Q,x) then continue; 
		    end if;
		    for y in SS do
		        a,b:= IsConjugate(B,x,y);
		        if a  then w:= Index(SS,y); namex:= Index(Orb,x);
		        theta := g*Elt[namex]*ConjtoHom(x,y,b);
                theta1:= ConjtoHom(y,x,b^-1)*Elt[namex]^-1*g1;
		        break; end if;
		    end for;
		    if v ne w then
		        AddEdge(~Gamma,v,w);
		        Maps[[v,w]]:= theta;
		        //Maps[[w,v]]:= theta^-1;
            Maps[[w,v]]:= theta1;
		    end if;
		 end for;
		 SSSE := SSSE diff Set(Orb);
	    end while;
end for;
return  Gamma, Maps;
end intrinsic;


intrinsic FusionGraphSCentrics(F::FusionSystem)->GrphUnd, Assoc
{Returns the labeled fusion graph on S centrics}

if assigned(F`fusiongraph)  then return F`fusiongraph,F`maps; end if;

Essentials := F`essentials; 

S:= F`group;
B:=F`borel;
SS:=  F`subgroups;
Gamma := Graph<#SS|>;
SSxSS:= [[n,m]:n in [1..#SS],m in [1..#SS]];
Maps:=AssociativeArray(SSxSS);


for E in Essentials do 
    	if E eq S then continue E; end if; 
    
	NBE := Normalizer(B,E);
    	SubsE := Subgroups(NBE:OrderDividing:= #E);
    	SSSE:={x`subgroup:x in SubsE|(x`subgroup subset E) and (IsSCentric(S,x`subgroup))};
	    while #SSSE ne 0 do
		Q:= Rep(SSSE);
		for X in SS do
		    a,h:= IsConjugate(B,X,Q); 
		    if a then
		        v:= Index(SS,X); 
		        g:=ConjtoHom( SS[v], Q,h); 
                g1 :=ConjtoHom(Q, SS[v],h^-1); 
		        break;
		    end if;
		end for;
	    Orb, NN, Elt := AutOrbit(E,Q,F`essentialautos[Index(F`essentials,E)]);
		for x in Orb do 
		    if IsConjugate(B,Q,x) then continue; 
		    end if;
		    for y in SS do
		        a,b:= IsConjugate(B,x,y);
		        if a  then w:= Index(SS,y); namex:= Index(Orb,x);
		        theta := g*Elt[namex]*ConjtoHom(x,y,b);
                theta1:= ConjtoHom(y,x,b^-1)*Elt[namex]^-1*g1;
		        break; end if;
		    end for;
		    if v ne w then
		        AddEdge(~Gamma,v,w);
		        Maps[[v,w]]:= theta;
		        //Maps[[w,v]]:= theta^-1;
            Maps[[w,v]]:= theta1;
		    end if;
		 end for;
		 SSSE := SSSE diff Set(Orb);
	    end while;
end for;
return  Gamma, Maps;
end intrinsic;


//////////////////////////////////////////////
//Identifies the B-Class of an arbitrary subgroup.
/////////////////////////////////////////
 intrinsic IdentifyBClass(F::FusionSystem,P::Grp)->RngIntElt,GrpElt
 {Identifies a AutFS-conjugacy class}
 
 SS:= F`subgroups; B:= F`borel;
 for ii := 1 to #SS do 
    aa,bbb:=IsConjugate(B,P,SS[ii]);
    if aa then return ii,bbb; end if; 
 end for;
 end intrinsic;


 intrinsic IdentifyBClass(B::Grp,SS::SeqEnum,P::Grp)->RngIntElt,GrpElt
 {Identifies a AutFS-conjugacy class}
 
 for ii := 1 to #SS do 
    aa,bbb:=IsConjugate(B,P,SS[ii]);
    if aa then return ii,bbb; end if; 
 end for;
 end intrinsic;
 
 
 
//////////////////////////////////////
////Identify the F-orbit as a connected component of the fusion graph. 
///P is in SS
///////////////////////////////

  intrinsic IdentifyFOrbit(F::FusionSystem,P::Grp)->SetEnum
  {identifies the connected component of the fusion graph corresponding to P}    
      if assigned(F`fusiongraph) eq false then 
          F`fusiongraph, F`maps:= FusionGraph(F); 
      end if;   F`classes:= ConnectedComponents(F`fusiongraph);
      ii:= Index(F`subgroups,P);
                for C in F`classes do
                    if ii in C then D:= C; break; end if;
                end for;
      return D;
      end intrinsic;


//////////////////////////////////////////
////Suppose that P \le S. Determine the F-class of P
/////////////////////////////

intrinsic ConjugacyClass(F::FusionSystem,P:Grp)-> SetEnum
{Determines the F-conjugacy class of a subgroup}
SS:= F`subgroups;S:= F`group;
    if assigned(F`fusiongraph) eq false then 
        F`fusiongraph,F`maps:= FusionGraph(F);  
        
    end if; F`classes:= ConnectedComponents(F`fusiongraph);

ii:= IdentifyBClass(F,P);

Clss:= IdentifyFOrbit(F,SS[ii]);  
FCls:={};
for w in Clss do 
    FCls:= FCls join{ SS[Index(w)]^x:x in F`borel}; 
end for;
return FCls;
end intrinsic;


   //////////////////////////////////////////
////Suppose that P,Q \le S. Are P and Q F-conjugate? V:= Vertices(Gamma);
///Returns true or false and if true a map in F
/////////////////////////////

intrinsic IsConjugate(F::FusionSystem, P::Grp,Q::Grp)->Bool,Map 
{returns a homomorphism and true if the groups are F-conjugate}

SS:= F`subgroups; S:= F`group; B:= F`borel; 
if assigned(F`fusiongraph) eq false then 
    F`fusiongraph,F`maps:= FusionGraph(F);  
    
end if;
F`classes:= ConnectedComponents(F`fusiongraph); 
Maps:= F`maps; 
V:= Vertices(F`fusiongraph);

conj := false; gg:= Id(S);
    if #P ne #Q then return false, _; end if;
   
   
ii, b1:= IdentifyBClass(F,P);
jj, b2:= IdentifyBClass(F,Q);

            if Reachable(V!ii, V!jj) then
               gg:=  ConjtoHom(P,SS[ii],b1); 
               hh:=ConjtoHom(SS[jj],Q,b2^-1);
               Geo:=Geodesic(V!ii,V!jj);
               if #Geo eq 0 then conj eq false;
                    else conj := true;
                    for iii:= 1 to #Geo-1 do 
                        gg:= gg*Maps[[Index(Geo[iii]),Index(Geo[iii+1])]]; 
                    end for;
              end if;
              gg:=gg*hh;
          end if;
return conj,gg;
end intrinsic;

///////////////////////////////////////////////////////////////////////////
/////////IsConjugate for elements.
///////////////////////////////////////////////////////////////////////
intrinsic IsConjugate(F::FusionSystem, g::GrpElt,h::GrpElt)->Bool,Map 
{returns a homomorphism and true if the elements are F-conjugate}
S:= F`group;
B:= F`borel;

a,b := IsConjugate(B,g,h);
if a then b :=  ConjtoHom(B, B, b); return true,b;end if;


if assigned(F`fusiongraph) eq false then 
    F`fusiongraph,F`maps:= FusionGraph(F); 
end if;

G:= sub<B|g>; H:= sub<B|h>;
a,b:=IsConjugate(F , G,H);
if a eq false then return false; end if; 
g1:= b(g);
 
a1, bb:= IdentifyBClass(F,H);

P:= H^bb;

APH:= AutomorphismGroup(F,P);
g2 := g1^bb;
h1 := h^bb;

CC, JJ, KK:= AutOrbit(P, g2, APH);
if h1 in CC eq false then return false; 
    else k:= Index(CC,h1); mp:= KK[k];
    map := b*ConjtoHom(S,S,bb)*mp*ConjtoHom(S,S,bb^-1); return true, map;
    end if;
    
return false,_;
end intrinsic;

///////////////////////
/////// F-conjugacy class
///////////////////////////////
intrinsic FConjugacyClass(F::FusionSystem,x::GrpElt)->  Set
{Returns set of all F-conjugates of x}
B:= F`borel;
BC:= ConjugacyClasses(B);
CC:={};
for t in BC do
    s:= t[3]; 
    if Order (s) ne Order (x) then continue; end if;
    a:= IsConjugate(F,x,s); 
    if a then CC:= CC join Class(B,s); end if;
end for;
return CC;
end intrinsic;

/////////////////////////
// SizeFConjugacyClass
/////////////////////////
intrinsic  SizeFConjugacyClass(F::FusionSystem,x::GrpElt)->  RngElt
{Returns size of the F-class of x}
 return #FConjugacyClass(F,x);
end intrinsic;

/////////////////////////////////////
/// FConjugacyClasses
///////////////////////////////////


intrinsic  FConjugacyClasses(F)-> Set
{Returns FConjugacyClasses}
 B:= F`borel;
 BC:= ConjugacyClasses(B);
 CCC:={};kk:=0;
 for t in BC do
    s:= t[3]; for cc in CCC do if s in cc then continue; end if; end for;
    if s in F`group eq false then continue; end if;
    k:= #FConjugacyClass(F,s); kk:= kk+k;
    CCC:= CCC join {FConjugacyClass(F,s)};
    if kk eq #F`group then break; end if;
 end for;
 
return CCC; 
end intrinsic;

/////////////////////////////////////
///Number  FConjugacyClasses
///////////////////////////////////


intrinsic  SizeFConjugacyClasses(F)-> RngElt
{Returns Size of  FConjugacyClasses}
return #FConjugacyClasses(F);
end intrinsic;


///////////////////////////////////
///////IsCentric(P).
///////////////////////////////////

intrinsic IsCentric(F::FusionSystem,P::Grp)->Bool
{Returns true if P is F-centric}

SS:= F`subgroups; S:= F`group; B:= F`borel; 
if assigned(F`fusiongraph) eq false then 
    F`fusiongraph,F`maps:= FusionGraph(F); 
end if;
  F`classes:= ConnectedComponents(F`fusiongraph); 
Cent:= true;

ii:= IdentifyBClass(F,P);
P:= F`subgroups[ii];
C:=  IdentifyFOrbit(F,P);
     for jj in C do
        if Centre(SS[Index(jj)]) ne Centralizer(S,SS[Index(jj)]) 
            then return false;
        end if;
     end for;
 return Cent;
 end intrinsic;


///////////////////////////////////
///////IsFullyNormalized(P).
///////////////////////////////////

intrinsic IsFullyNormalized(F::FusionSystem, P::Grp)->Bool{Is the subgroup full F-Normalized}

SS:= F`subgroups; S:= F`group; B:= F`borel; 
if assigned(F`fusiongraph) eq false then 
F`fusiongraph,F`maps:= FusionGraph(F);  
end if;
 F`classes:= ConnectedComponents(F`fusiongraph); 
 
FN:= true;

ii:= IdentifyBClass(F,P);
P:= F`subgroups[ii];

n:=#Normalizer(S,P);
C:=IdentifyFOrbit(F,P);
for jj in C do 
    m:= #Normalizer(S,SS[Index(jj)]);    
    if m gt n then FN:= false;
        break jj; 
    end if; 
end for; 

return FN;
end intrinsic;


/////////////////////////////////////
/////////IsFullyCentralized(P).
/////////////////////////////////////


intrinsic IsFullyCentralized(F::FusionSystem, P::Grp)->Bool{Is the subgroup full F-Centralized}
SS:= F`subgroups; S:= F`group; B:= F`borel; 
if assigned(F`fusiongraph) eq false then F`fusiongraph,F`maps:=FusionGraph(F);  
end if;
 F`classes:= ConnectedComponents(F`fusiongraph); 

    FC:= true;
    n:=#Centralizer(S,P);

ii:= IdentifyBClass(F,P);
P:= F`subgroups[ii];

C:=IdentifyFOrbit(F,P);
for jj in C do 
    m:= #Centralizer(S,SS[Index(jj)]);    
    if m gt n then FC:= false;
        break jj; 
    end if; 
end for; 
return FC;
end intrinsic;


//////////////////////////////////////////////////////////////////////
///Transports for ww in SS and x B-conjugate to AutF(ww) to AutF(x). 
///The second one transports with known origin and X in SS.  
//So AY= AutF[SS[ii]] is known and X is F-conjugate to Y=SS[ii]
//////////////////////////////////////////////////////////////////////

intrinsic TransportAutomorphismsYtoX(F::FusionSystem,AutF::Assoc,Y::Grp,X::Grp)
                ->GrpAuto
{Transports the automorphism group of the first group to 
the second assuming they are F-conjugate}
require IsConjugate(F,Y,X):"The groups are not F-conjugate";
 MakeAutos(X);


    Ax:= X`autogrp;
    AY:= AutF[Y];
    SS:= F`subgroups; S:= F`group; B:= F`borel; 
if assigned(F`fusiongraph) eq false then 
    F`fusiongraph,F`maps:= FusionGraph(F);  
   
end if; F`classes:= ConnectedComponents(F`fusiongraph); 
    V:= Vertices(F`fusiongraph);
    Maps:=F`maps;
    jj:= Index(SS,X);
    ii:= Index(SS,Y);

    Geo:=Geodesic(V!ii,V!jj);
    alpha:= Identity(AY);
    beta:= Identity(Ax);
        for iii:= 1 to #Geo-1 do
            alpha:= alpha*Maps[[Index(Geo[iii]),Index(Geo[iii+1])]];
        end for;
        for iii:= #Geo to 2 by -1 do
            beta:= beta*Maps[[Index(Geo[iii]),Index(Geo[iii-1])]];
        end for;
    AutX:= sub<Ax|{beta*gen*alpha:gen in Generators(AY)}>;
return AutX;
end intrinsic;

/////////////////////////////////////////////////////////
////////////Making AutF[X] more generally for F-centric X. We do this on connected components.
////////////////////////////////////////////////////////
//
intrinsic MakeAllAutFCentric(FF::FusionSystem:saturationtest)->Assoc, Bool
{Makes all AutF for centric subgroups unless parameter saturated test eq true in which case it stops early when the system is not saturated .}

ZZ:=Integers();
SS:= FF`subgroups;
S:= FF`group; 
B:= FF`borel; 
AutF:= FF`AutF; 
Essentials:= FF`essentials; 

if assigned(FF`fusiongraph) eq false then FF`fusiongraph,FF`maps:= FusionGraph(FF);
   
end if;
 FF`classes:= ConnectedComponents(FF`fusiongraph);
if assigned(FF`centrics) eq false then FF`centrics:={x:x in FF`subgroups|IsCentric(FF,x)}; end if;
Maps:= FF`maps;  
ConComp:= FF`classes; 
Fac:= FactoredOrder(S);
ExpS:=Fac[1][2]; p:= FF`prime;
expP:= ExpS-1;

 
for x in SS do   
    if #x eq p^expP and ((x in Essentials) eq false) then
    	AutF[x]:= AutYX(Normalizer(B,x),x);
    end if;
end for;

  TTTn:={x:x in FF`centrics|   IsFullyNormalized(FF,x) and (x in Essentials) eq false};
for subexponent:=ExpS-2 to 2 by -1 do
  
    TTT :={x: x in TTTn|#x eq p^subexponent };
  
 
    while  #TTT ne 0 do 
        P:= Random(TTT);
	//If P is F-conjugate to a member of Essentials, then Aut_F(P) is F-conjugate to Aut_F(E). Transfer the data and move to next P.

        for E in Essentials do 
            aa,bb:=IsConjugate(FF,P,E); 
            aa,bbb:=IsConjugate(FF,E,P); 
            if aa  then  //bbb:= Inverse(bb);
                AutF[P]:=  sub<P`autogrp|{hom<P->P|gg:->bbb(hh(bb(gg)))> :hh in Generators(AutF[E])}>;
                TTT:= TTT diff {P};continue; 
            end if; 
        end for; //E
        
	///Now P is not F-conjugate to E.

           NBP:=Normalizer(B,P);
           AutF[P] :=  AutYX(NBP,P); 
	   AFSP:=AutF[P];
          
	   NBPoverP, a := NBP/P;
		///TTTS contains representative of all non-trivial $p$-subgroups in N_S(P)/P
 
            TTTS:= [sub<NBP|SubInvMap(a, NBP, x`subgroup),P>:x in Subgroups(NBPoverP:OrderDividing:=#S)|x`order ne 1];
                for ccc:= 1 to #TTTS do
                 x := TTTS[ccc]; 
                    MakeAutos(x);

                    if x in SS then
                        AutFx := AutF[x];
                        j:= x`autopermmap;  Ap:=x`autoperm;
                    else  
                           Ax:=x`autogrp;
                            for ww in SS do
                            aa, bb := IsConjugate(B,ww,x);
                                if aa then
                                    bbb:= ConjtoHom(ww,x,bb);  bbb1:= ConjtoHom(x,ww,bb^-1);
                                    AutFx:= sub<Ax|{bbb1*gen*bbb : gen in Generators(AutF[ww])}>; break ww;
                                end if;
                             end for;//for ww
                    j:=x`autopermmap; Ap:= x`autoperm; 
                    end if;// if x in ss, then, else, end if
                AFp:= sub<Ap|{j(pp):pp in Generators(AutFx)}>;
                jinverse:=Inverse(j);
                AA, NN, Elt:= AutOrbit(x,P,AutFx);
                MM:= sub<Ap|{j(n):n in Generators(NN)}>;
                Trp := Transversal(AFp,MM);
                Tr:= {jinverse(t):t in Trp};
                ////////////////////////////////
                //We look at maps between TTTS[ccc] and TTTS[ddd] that are extensions of maps in AutF[P].  
                ///We don't need to do it both ways around as adding an element is the same as adding its inverse.
                //////////////////////////////////////////////////
                    for ddd:= ccc to #TTTS do  
                        y := TTTS[ddd]; W:={};
                        if x eq y then 
                                for nn in Generators(NN) do  mmP:= iso<P->P| w:->nn(w)>; 
                                W:= W join {mmP};
                            end for;
                            AutF[P]:=sub<P`autogrp|AutF[P],W>;
                        else
                        aa, bb:= IsConjugate(FF,x,y);
                            if aa then 
                            W:={alpha*bb:alpha in Tr |(alpha*bb)(P) eq P}; 
                            AutF[P]:=sub<P`autogrp|AutF[P],W>;
                            end if;
                        end if;
                    end for;//ddd
                     if saturationtest then 
                        if ZZ!(#AutF[P]/#AFSP) mod p eq 0 then  
                        return AutF, false;
                        end if;  
                     end if; 
                end for; //ccc
                
              isp:=Index(SS,P);

                for C in FF`classes do
                    if isp  in C then D:= C; break; end if;
                end for;
                //Check that calculated data coincides with information from essentials. 
                //I.e if P if F-conjugate to some F`essential, then auto groups should be the same.
                
                 for iiii in [1..#Essentials] do E:= Essentials[iiii];
                    mm:= Index(SS,E); 
                    if mm in D then
                     TransP:=TransportAutomorphismsYtoX(FF,AutF,P,E);
                     if TransP ne FF`essentialautos[iiii] then 
                     if saturationtest then
                        return AutF, false; 
                      else print "the automiser sequence is not consistent in this system"; return AutF,_;
                      end if;
                      end if;
                     end if;
                end for;
                 //we now can define AutF for  all the F-conjugates of P
                 for kk in D do jj:= Index(kk); 
                    if jj eq isp then  TTT:= TTT diff {P};   continue; end if;
                    AutF[SS[jj]]:= TransportAutomorphismsYtoX(FF,AutF,P,SS[jj]);  
                    TTT:= TTT diff {SS[jj]};
                end for;  //
                
           end while; //TTT
     end for;//subexponent
delete TTT; delete TTTS;

return AutF, _;

end intrinsic;

////////////////////////////


intrinsic SurjectivityProperty(F::FusionSystem,P::Grp:saturationtest)->Bool, Bool
{Determines whether the surjectivity property hold for P}

if saturationtest and assigned(F`saturated) then 
return F`saturated, F`saturated; end if;

require IsCentric(F,P):"subgroup not F-centric";

SS:= F`subgroups; 
S:= F`group; 
B:= F`borel; 
Essentials:= F`essentials;

Maps:= F`maps; 
ConComp:= F`classes; 
AutF:= F`AutF;

 
 
SurP:= true;
NSP:= Normalizer(S,P);

NSPoverP, a := NSP/P; 
SSP:= [sub<NSP|SubInvMap(a, NSP, x`subgroup),P>:x in Subgroups(NSPoverP)|x`order ne 1];
   for OverGrpP in SSP do 
        BClassOverGrpP, alpha:= IdentifyBClass(F,OverGrpP);
        RepOverGrpP:= SS[BClassOverGrpP];
        MakeAutos(OverGrpP);
        Ax:=  OverGrpP`autogrp;
        beta:= ConjtoHom(RepOverGrpP,OverGrpP,alpha^-1);
        beta1:= ConjtoHom(OverGrpP,RepOverGrpP,alpha); 
        AutFx:= sub<Ax|{beta1*gen*beta : gen in Generators(AutF[RepOverGrpP])}>;      
        AA:= AutF[P]; 
        MakeAutos(P);
        AAp:= sub<P`autoperm|{P`autopermmap(gAA):gAA in Generators(AA)}>;
        action := AutYX (OverGrpP,P);
        actionp:= SubMap(P`autopermmap,AAp,action);
        Naction:= Normalizer(AAp,actionp);
        NBB:= SubInvMap(P`autopermmap,P`autogrp,Naction);
        Orb,NN, Elts:= AutOrbit(OverGrpP,P,AutFx);
        ResNN:=sub<P`autogrp|Generators(NN)>;
        if ResNN ne NBB then  SurP := false; break; end if;
    end for;
    if assigned(F`saturated) then
 return SurP, F`saturated; else return SurP, _;end if; 
 
 end intrinsic;
/////////////////////////
 /////////////////IsSaturated(F)
////////////////////////////////
 
intrinsic IsSaturated(F::FusionSystem)-> Bool{Determines if F is saturated}

if assigned(F`saturated) then return F`saturated; end if;
 
SS:= F`subgroups; 
S:= F`group; 
B:= F`borel; 
Essentials:= F`essentials;
 

if assigned(F`fusiongraph) eq false then  
F`fusiongraph,F`maps:= FusionGraphSCentrics(F);
end if;
F`classes:= ConnectedComponents(F`fusiongraph);

Maps:= F`maps; 
AutF:= F`AutF;

ConComp:= F`classes; 
 
 
for x in F`essentials do 
    if IsCentric(F,x) eq false then 
    F`saturated := false; return F`saturated; 
    end if; 
     if IsFullyNormalized(F,x) eq false then 
    F`saturated := false; return F`saturated; 
    end if; 
end for;

 

if assigned(F`centrics) eq false then F`centrics:={x:x in F`subgroups|IsCentric(F,x)}; end if;
  
    W:= {x: x in F`centrics|IsDefined(F`AutF,x) };
    i:=0;
     for x in Reverse(Setseq(F`centrics)) do  
        if x in W then continue; end if; 
        for w in W do
            a,b:=IsConjugate(F,x,w);
            if a then    aa,cc:=IsConjugate(F,w,x);    
            F`AutF[x] := sub<x`autogrp| {b*gamma*cc: gamma in Generators(F`AutF[w])} >; 
             W:= W join{x}; continue x; 
        end if;
        end for;
        
       F`AutF[x]:= AutomorphismGroup(F,x);  
       if IsFullyNormalized(F,x) then 
            if not IsFullyAutomised(F,x) then return false; end if;
       end if; 
       W:= W join{x};
     end for;
 

Saturated:= true;
for C in ConComp do
    for vv in C do
        PP:= SS[Index(vv)];
            if PP eq S then continue C; end if;
            if IsCentric(F,PP) eq false then continue C; end if;
            if IsFullyNormalized(F,PP) eq false then continue vv; end if;
            if RadicalTest(S,PP) eq false then   continue vv; end if;
            if IsFullyAutomised(F,PP) eq false then return false; end if;
        Saturated, sat := SurjectivityProperty(F,PP:saturationtest:=true);
        if  assigned(sat) then  return sat; end if;
            if Saturated then continue C; end if;
    end for;
    if Saturated eq false then break C; end if;
end for; 
delete F`fusiongraph;//This is a fix to make sure that IsConjugate works for non-centric subgroups



F`saturated := Saturated;
return Saturated;
end intrinsic;



//////////////////////////////////
intrinsic IsFullyAutomised(F::FusionSystem,P::Grp)->Bool{Is P fully F-automised}

 
 S:= F`group;   
 p:= F`prime;
 require #P gt 1 : "We require P non-trivial";
 
if  IsDefined(F`AutF,P) eq false then 
    F`AutF[P]:=  AutomorphismGroup(F,P);
end if;

ZZ:= Integers();
m:= #Normalizer(S,P)/#Centralizer(S,P);
m:= ZZ!m;
F:= FactoredOrder(F`AutF[P]); q:=1;
for x in F do 
    if x[1] eq p then q:= p^x[2]; end if; 
end for;
if q eq m then FA:= true; else FA:= false; end if;
return FA;
end intrinsic;
////////////////////////////////////////


intrinsic IsIsomorphic (F1::FusionSystem,F2::FusionSystem)->Bool{}

a, theta := IsIsomorphic(F1`borel,F2`borel);
if a eq false then return false; end if; 
p:= F1`prime;
bounds:=[8,6,6,6];
primes:=[2,3,4,4];

if p in primes and #F1`group le p^bounds[Index(primes,p)]  then
RO1:=[IdentifyGroup( x):x in F1`essentials];
RO2:=[IdentifyGroup(x):x in F2`essentials];
else
RO1:=[#x:x in F1`essentials];
RO2:=[#x:x in F2`essentials];
end if; 
if  RO1 ne RO2 then   return false; end if; 

 

//The automisers should have the same orders.
RO1:=[#x :x in F1`essentialautos];
RO2:=[#x :x in F2`essentialautos];
Sort(~RO1);
Sort(~RO2);
if RO1 ne RO2 then   return false; end if; 
 
 

AutBp:=(F2`essentials[1])`autoperm;

alpha:= (F2`essentials[1])`autopermmap;

NAutBp:= Normalizer(AutBp, SubMap(alpha,AutBp,F2`essentialautos[1]));
NAutB:= SubInvMap(alpha,F2`essentials[1]`autogrp,NAutBp);
TNB:= Transversal(NAutBp,SubMap(alpha,AutBp,F2`essentialautos[1]));
Trans:=[Inverse(alpha)(xxx):xxx in TNB];
 

//transfer to same group. And make an image for each transversal map.
ImEssentials:=[];

for mu in Trans do
ImEssentials:= Append(ImEssentials,[mu(theta(x)):x in F1`essentials] ); 
end for;

ImAutEssentials:= AssociativeArray({1..#Trans});

for zz in [1..#ImEssentials] do 
    ImEssentialsCalc:= ImEssentials[zz]; 
    mu:= Trans[zz];// theta. mu maps xin F1 essentials to a subgroup of F2`group
       //Initialize the automorphism group of the images
        for ii in [1..#ImEssentialsCalc] do  
            x:= ImEssentialsCalc[ii]; 
            x`autogrp :=AutomorphismGroup(x); 
            x`autopermmap, x`autoperm:= PermutationRepresentation(x`autogrp); 
        end for;     
    ImAutEssentialsCalc:=[];
    for x in ImEssentialsCalc do 
            AutF1:= F1`essentialautos[Index(ImEssentialsCalc,x)];
            XX:=[Inverse(mu)*Inverse(theta)*gen*theta*mu:gen in Generators(AutF1)];
            ImAutEssentialsCalc:=Append(ImAutEssentialsCalc, sub<x`autogrp| XX>); 
    end for;
    
ImAutEssentials[zz]:=ImAutEssentialsCalc;
 
end for;

for XXct in [1..#ImEssentials] do XX:=ImEssentials[XXct];
    for ii in [1..#XX] do e:= XX[ii]; if e in F2`subgroups then continue; end if;
            jj:= IdentifyBClass(F2,e);
            P:= F2`subgroups[jj];
            MakeAutos(P);
            a,b :=IsConjugate(F2`borel,e,P);
            bb:= ConjtoHom(e,P,b); 
            bbb:= ConjtoHom(P,e,b^-1);    
            XX[ii]:=P;
            ImAutEssentials[XXct][ii]:= sub<P`autogrp|
                {hom<P->P|gg:-> bb(gen(bbb(gg)))>:
                gen in  Generators(ImAutEssentials[XXct][ii])}>;
    end for;
end for;
            
 
        jj:= {1..#F2`essentials};
        for ii in [1..#ImAutEssentials] do 
            kk:= jj;
            for mm in ImAutEssentials[ii] do
                for aa in jj do
                    if mm eq F2`essentialautos[aa] then kk:= kk diff {aa}; end if;
                end for; 
             if #kk eq 0 then return true;end if;
            end for;
        end for; 
 return false;
end intrinsic;


//////////////////////////////////////////////////////////////
intrinsic 'eq'(F1::FusionSystem, F2::FusionSystem) -> Bool
{checks if two fusion systems are equal}
    E1:= F1`essentialautos;
    E2:= F2`essentialautos;
    Eq := true;
    for x in E1 do
        for y in E2 do
            if x eq y then continue x; end if;
        end for;
        Eq:= false;
        if Eq eq false then break x; end if;
    end for;
    
    return Eq;
end intrinsic;

/////////////////////////////////////
///////Make a fusion system from a specifeid p-subgroup S of a group G
////////////////////////////////////

intrinsic  GroupFusionSystem(G::Grp,T::Grp)->FusionSystem
{Creates the fusion system on the p-subgroup S of G}
p:= FactoredOrder(T)[1][1];
ZZ:= Integers();
B1:= Normalizer(G,T); T1:= Sylow(B1,p);
require  T1 eq sub<G|T,Centralizer(T1,T)>:"system cannot be saturated";   
 Testers:= {Sylow(SL(2,p^2), p),Sylow(SL(2,p^3), p),Sylow(SL(2,p^4), p),Sylow(SL(2,p^5), p),
Sylow(SL(2,p^6), p), Sylow(SU(3,p), p),Sylow(SU(3,p^2), p)};// Add more?
		



B2, PhiB:= PCGroup(B1);

SST:= [SubInvMap(PhiB,B1,x`subgroup):x in Subgroups(B2:OrderDividing:=#T)];
 
SS:= [x:x in SST|IsSCentric(T,x)];

EE:=[T];
GrpEssentialAutos:=AssociativeArray(SS);
GrpEssentialAutos[T]:=AutomiserGens(B1,T);

for x in SS do 

if x eq T then continue; end if;

NTx:= Normalizer(T,x);
Q:=NTx/x;
QC:= IsQuaternionOrCyclic(Q);
    if QC eq false then 
            if #Q le p^6 then TesT:= false;
               for SP in Testers do
                 if IsIsomorphic(Q,SP) then TesT := true; break; end if;
                end for;
             if TesT eq false  then continue; end if;
        end if;
    end if;  
    Nx:= Normalizer(G,x);
    
    if Index(Nx,NTx) mod p eq 0 then continue; end if;  
    kk := sub<G|Centralizer(G,x), x>;

    if QC eq false and #Factorisation(ZZ!(#Nx/#kk)) le 2 then continue; end if;


   ISPE:=IsStronglypEmbeddedMod(Nx,kk,p);
    if ISPE then 
    EE:= Append(EE,x);
 
    GrpEssentialAutos[x]:= AutomiserGens(Nx,x);
    
 
    end if; 
end for; 
 
 
 

B2, PhiB:= PCGroup(B1);
EEPC:=[SubMap(PhiB,B2,x):x in EE];
EEAA:=[];
for i := 1 to #EEPC do
Es:= EEPC[i];
MakeAutos(Es);
EEAA[i]:= sub<Es`autogrp|[Inverse(PhiB)*gamma*PhiB:gamma in GrpEssentialAutos[EE[i]]]>; 
end for;

F:=CreateFusionSystem(EEAA);
 
F`grpsystem:=G;
F`grppgrp:=T;
F`saturated := true;
return F;
end intrinsic
//////////////////////////////////////////////////////////////////////
intrinsic  GroupFusionSystem(G::Grp, p::RngIntElt)->FusionSystem
{Makes the group fusion system on the Sylow p-subgroup}
T:= Sylow(G,p);F:= GroupFusionSystem(G,T);F`saturated:= true;

return F;
end intrinsic;
//////////////////////////////////////////////////////////////////////////
intrinsic IsWeaklyClosed(F::FusionSystem, P::Grp)->Bool
{Returns true if the subgroups is weakly closed}
WC:= false;
if IsNormal(F`borel,P) eq false then return false; end if;
if #ConjugacyClass(F,P) eq 1 then WC := true; end if;
return WC;
end intrinsic;
/////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
intrinsic IsStronglyClosed(F::FusionSystem, P::Grp)->Bool
{Returns true if the subgroups is strongly closed}
SC:= true;
if IsWeaklyClosed(F,P) eq false then return false; end if;

X:= {x`subgroup: x in Subgroups(P)};
for x in X do 
    xC:= ConjugacyClass(F,x);  
    for w in xC do
        if w subset P eq false then return false; end if; 
    end for;
end for; 
return SC;
end intrinsic;

/////////////////////////////////////
intrinsic IsGroupFusionSystem(F::FusionSystem)->Bool
{Return true if F is constructed from G }
if assigned(F`grpsystem) then return true; end if;
return false; 
end intrinsic;
/////////////////////////////
//////////////////////////////////
////Given an automiser sequence Autos with Borel B, and a Fusion system F
////Check is the automniser sequence of F and the fusion system of EssA are
///Isomorphic 
/////////////////////////////////////
intrinsic IsIsomorphic(B::Grp,Autos::SeqEnum,F2::FusionSystem)->Bool{}


a, theta := IsIsomorphic(B,F2`borel);
if a eq false then return false; end if; 
p:= F2`prime;
bounds:=[8,8,6,6];
primes:=[2,3,4,4];



/////////////////////////////////////////////////////////
///F2 has its automiser sequence in the canonical order.
///We should reorder Autos.
//////////////////////////////////////////////////////////
if p in primes and #F2`group le p^bounds[Index(primes,p)]  then  
RO:=[IdentifyGroup( Group(x)):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos);
else
RO:=[#Group(x):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos); 
end if; 
  
  
  
F1essentials := [Group(x):x in Autos];

if p in primes and #F2`group le p^bounds[Index(primes,p)]  then
RO1:=[IdentifyGroup( x):x in F1essentials];
RO2:=[IdentifyGroup(x):x in F2`essentials];
else
RO1:=[#x:x in F1essentials];
RO2:=[#x:x in F2`essentials];
end if; 
if  RO1 ne RO2 then return false; end if; 

//The automisers should have the same orders.
RO1:=[#x :x in Autos];
RO2:=[#x :x in F2`essentialautos];
Sort(~RO1);
Sort(~RO2);
if RO1 ne RO2 then return false; end if; 
 
 
 
    


AutBp:= (F2`essentials[1])`autoperm;

alpha:= (F2`essentials[1])`autopermmap;

NAutBp:= Normalizer(AutBp, SubMap(alpha,AutBp,F2`essentialautos[1]));
NAutB:= SubInvMap(alpha,F2`essentials[1]`autogrp,NAutBp); 
TNB:= Transversal(NAutBp,SubMap(alpha,AutBp,F2`essentialautos[1]));
Trans:=[Inverse(alpha)(xxx):xxx in TNB];
 

//transfer to same group. And make an image for each transversal map.
ImEssentials:=[];

for mu in Trans do
ImEssentials:= Append(ImEssentials,[mu(theta(x)):x in F1essentials] ); 
end for;

ImAutEssentials:= AssociativeArray({1..#Trans});

for zz in [1..#ImEssentials] do 
    ImEssentialsCalc:= ImEssentials[zz]; 
    mu:= Trans[zz];// theta. mu maps x in F1essentials to a subgroup of F2`group
       //Initialize the automorphism group of the images
        for ii in [1..#ImEssentialsCalc] do  
            x:= ImEssentialsCalc[ii];
            MakeAutos(x); 
        end for;     
    ImAutEssentialsCalc:=[];
    for x in ImEssentialsCalc do 
            AutF1:= Autos[Index(ImEssentialsCalc,x)];
            XX:=[Inverse(mu)*Inverse(theta)*gen*theta*mu:gen in Generators(AutF1)];
            ImAutEssentialsCalc:=Append(ImAutEssentialsCalc, sub<x`autogrp| XX>); 
    end for;
     
ImAutEssentials[zz]:=ImAutEssentialsCalc;
 
end for;

for XXct in [1..#ImEssentials] do 
    XX:=ImEssentials[XXct];
    for ii in [1..#XX] do 
    e:= XX[ii]; 
     if e in F2`subgroups then continue; end if;
        jj:= IdentifyBClass(F2,e);
        P:= F2`subgroups[jj];
        MakeAutos(P);
        a,b :=IsConjugate(F2`borel,e,P);
        bb:= ConjtoHom(e,P,b); 
        bbb:= ConjtoHom(P,e,b^-1);    
        XX[ii]:=P;
        ImAutEssentials[XXct][ii]:= sub<P`autogrp|
            {hom<P->P|gg:-> bb(gen(bbb(gg)))>:
            gen in  Generators(ImAutEssentials[XXct][ii])}>;
end for;
end for;
            
 
        jj:= {1..#F2`essentials};
        for ii in [1..#ImAutEssentials] do 
            kk:= jj;
            for mm in ImAutEssentials[ii] do
                for aa in jj do
                    if mm eq F2`essentialautos[aa] then kk:= kk diff {aa}; end if;
                end for; 
             if #kk eq 0 then return true;end if;
            end for;
        end for; 
 return false;
end intrinsic;
////////////////////////////////////////////
intrinsic NormalizerTower(S::Grp,E::Grp)->SeqEnum
{Creates a normalizer tower}

NT:= [Normalizer(S,E)];
while NT[#NT] ne S do Append(~NT,Normalizer(S,NT[#NT])); end while;
return NT;
end intrinsic; 

 ///////////////////////////////////////////
 intrinsic FusionTower(F::FusionSystem,P::GrpPC, AFP::GrpAuto)-> SeqEnum
 {Determines the fusion systems on normalizer tower when possible}
 S:= F`group;
 B:= F`borel; 
 NBP:=Normalizer(B,P);
 L:=Random(Complements(NBP,Normalizer(S,P)));
 AFPS:=AutYX(NBP,P);
 
 
 require  {x in AFP: x in  Generators(AFPS)} eq {true}: "the system F isn't saturated"; 
 AFPS:= sub<AFP|Generators(AFPS)>;
 AFPp:= SubMap(P`autopermmap,P`autoperm, AFP);
 AFPSp:= SubMap(P`autopermmap,P`autoperm, AFPS);
 ASp:= SubMap(P`autopermmap,P`autoperm,AutYX(Normalizer(S,P), P));
 

 InnSp:=SubMap(S`autopermmap,S`autoperm,Inn(S));
 
if not AFPSp eq Normalizer(AFPp,ASp) then print "construction not applicable"; return []; end if;

Tower :=  NormalizerTower(S,P);
FF:=[];

for T in Tower do BT:= sub<B|L,T>; Autos:=[AutYX(BT,T),AFP]; 
Append(~FF,CreateFusionSystem(Autos));
end for;
return FF;
 
end intrinsic;
 
 ////////////////////////////////////////////
////////////////////////////////////////////////////////////
intrinsic SaveFS(FileName::MonStgElt, F::FusionSystem)
{Saves fusion system to FileName so that it can be loaded}

S:=Group(F`essentialautos[1]);
PrintFile(FileName,"S:=");PrintFileMagma(FileName,S);PrintFile(FileName,";");
PrintFile (FileName, "Autos:=[];\n");
for k := 1 to #F`essentials do
    A:=F`essentialautos[k];
    E:= Group(A);
    R := [S!w:w in PCGenerators(E)];
    PrintFile(FileName,"E:=sub<S|");
    PrintFile(FileName,R);
    PrintFile(FileName,">;\n");
    E:=sub<S|R>;
    PrintFile(FileName, "AE:= AutomorphismGroup(E);\n");
    PrintFile(FileName,"A:=sub<AE|>;\n");
    for ii := 1 to #Generators(A) do
        alpha:=A.ii;
        PrintFile(FileName,"A:=sub<AE|A, hom<E -> E |[ ");
        gens:=SetToSequence(PCGenerators(E));
        for i in [1..#gens-1] do
            x:= E!gens[i];
            PrintFile(FileName,"<");
            PrintFile(FileName,x);
            PrintFile(FileName,",");
            PrintFile(FileName,E!alpha(x));
            PrintFile(FileName,">");
            PrintFile(FileName,",");
        end for;
        x:= gens[#gens];
        PrintFile(FileName,"<");
        PrintFile(FileName,x);
        PrintFile(FileName,",");
        PrintFile(FileName,E!alpha(x));
        PrintFile(FileName,">");
        PrintFile(FileName," ]>>;\n");
    end for;
PrintFile(FileName,"Autos[");
PrintFile(FileName,k);
PrintFile(FileName,"]:=A;\n");
end for;
PrintFile(FileName,"FS:=CreateFusionSystem(Autos);");
PrintFile(FileName,"FS;");
end intrinsic;



intrinsic SaveFS(FileName::MonStgElt, FF::SeqEnum)
{Saves sequence of fusion systems to FileName so that it can be loaded}


PrintFile(FileName,"FFS:=[];");

for F in FF do      
    S:=Group(F`essentialautos[1]);
    PrintFile(FileName,"S:=");PrintFileMagma(FileName,S);PrintFile(FileName,";");
    PrintFile (FileName, "Autos:=[];\n");
    for k := 1 to #F`essentials do
        A:=F`essentialautos[k];
        E:= Group(A);
        R := [S!w:w in PCGenerators(E)];
        PrintFile(FileName,"E:=sub<S|");
        PrintFile(FileName,R);
        PrintFile(FileName,">;\n");
        E:=sub<S|R>;
        PrintFile(FileName, "AE:= AutomorphismGroup(E);\n");
        PrintFile(FileName,"A:=sub<AE|>;\n");
        for ii := 1 to #Generators(A) do
            alpha:=A.ii;
            PrintFile(FileName,"A:=sub<AE|A, hom<E -> E |[ ");
            gens:=SetToSequence(PCGenerators(E));
            for i in [1..#gens-1] do
                x:= E!gens[i];
                PrintFile(FileName,"<");
                PrintFile(FileName,x);
                PrintFile(FileName,",");
                PrintFile(FileName,E!alpha(x));
                PrintFile(FileName,">");
                PrintFile(FileName,",");
            end for;
            x:= gens[#gens];
            PrintFile(FileName,"<");
            PrintFile(FileName,x);
            PrintFile(FileName,",");
            PrintFile(FileName,E!alpha(x));
            PrintFile(FileName,">");
            PrintFile(FileName," ]>>;\n");
        end for;
    PrintFile(FileName,"Autos[");
    PrintFile(FileName,k);
    PrintFile(FileName,"]:=A;\n");
    end for;
    PrintFile(FileName,"FS:=CreateFusionSystem(Autos);");
    PrintFile(FileName, "FFS:=Append(FFS,FS);");
end for;
PrintFile(FileName,"FFS;");
end intrinsic;

//////////////////////////////////////////////////////////
intrinsic CharSbgrpTest(ProtoEssentials::SeqEnum,S::Grp)->Bool                     
{Checks if there's a characteristic subgroups of all essentials 
and S contained in the intersection of protop essentials}

Q:= S; 
for xx in ProtoEssentials do 
	Q := Q meet xx; 
end for;

QQ:= NormalSubgroups(Q);
SProtoEssentials := Append(ProtoEssentials,S);
for w in QQ do 
	ww:= w`subgroup;
	if #ww ne 1 then 
		for xx in SProtoEssentials do 
		wwChar := IsCharacteristic (xx,ww);
			if wwChar eq false then  continue w; end if; 
		end for;
		if wwChar eq true  then return true;end if;
	end if; 
end for;
return false;
end intrinsic; 

 
 
 /////////////////////////////////////

intrinsic AllMaximalSubgroups(G)-> SeqEnum
{Creates all maximal subgroups of G}
 
M:= MaximalSubgroups(G);
AM:=[];
for x in M do 
	m:= x`subgroup;Index(G,m); t:= Transversal(G,m); 
	for y in t do Append(~AM,m^y); end for;
end for; 
return AM;

end intrinsic;




intrinsic MaximalOverGroups(G::Grp,H::Grp, p::RngIntElt)-> SeqEnum
{Creates overgrps of H in G up to G conjugacy which have H as a sylow p-sugroup}
 
 
M:= MaximalSubgroups(G);
AM:=[];
for x in M do 
	m:= x`subgroup; Cm:= ConjugacyClasses(Sylow(m,p)); J:= Sylow(H,p);
	
	if #m mod #H eq 0 then  W:={xx[3]:xx in Cm|IsConjugate(G,xx[3],J.1)}; if #W ne 0 then
		t:= Transversal(G,m); 
		for y in t do Append(~AM,m^y); end for;
	end if; end if;
end for; 





AMH:=[];
for x in AM do
	if H subset x then Append(~AMH, x);end if;
end for;
return Set(AMH);
end intrinsic;


intrinsic OverGroups(G::Grp,H::Grp)-> SeqEnum
{Creates overgrps of H in G up to G conjugacy which have H as a sylow p-sugroup}

AllOvers:={};
ONew:={G};
while ONew ne {H} do 
	AllOvers := AllOvers join ONew;#AllOvers;
	Overs := ONew; 
	ONew:={H};
		for x in Overs do
			ONew:= ONew join MaximalOverGroups(x,H); 
		end for;
end while;

return AllOvers;


end intrinsic;


intrinsic OverGroupsSylowEmbedded(G::Grp,H::Grp,INN::Grp,p::RngIntElt)-> SeqEnum
{Creates overgrps of H in G which have H as a sylow p-subgroup and such that they are generated by conjugates of H. To get the full list we will use the Fratinni argument}

require IsPrime(p):"p is not a prime";
require #H mod p eq 0 :"H does not have order divisible by p";
require IsNormal(G,INN) :"Inn not normal in G";

J:= Sylow(H,p);
JJ, mp:= J/INN;

require IsCyclic(JJ) :"H/Inn does not have cyclic sylow subgroups";

NGH:= Normalizer(G,J);


JJJ:= Generators(JJ); JJJ:= {j: j in JJJ|Order(j) eq #JJ};
J1:= Inverse(mp)(Rep(JJJ)); // So J1 generates J mod INN and it is an element



AllOvers:={};
ONew:={SubnormalClosure(G,H)};
while ONew ne {H} do 
    Overs := ONew diff AllOvers;  j:= 0;
	AllOvers := AllOvers join ONew; 
	ONew:={H};
		for x in Overs do  j:= j+1;  
			  y:=SubnormalClosure(x,H); 
			M:= MaximalSubgroups(y);
			AM:=[];
			for mm in M do 
				m:= mm`subgroup; 
				if INN subset m then 
				    if #m mod #H eq 0 then  
					Cm:= ConjugacyClasses(m);
					for cc in Cm do  
						aa, bb := IsConjugate(y,cc[3],J1); 
						
						if aa then  mbb:= m^bb;  
							for am in AM do 
                                aaa, bbb := IsConjugate(NGH,am,mbb); 
                                if aaa then continue cc;  end if;
							end for;  
							AM:= AM cat [SubnormalClosure(mbb,H)]; 
						end if; 
					end for;//cc		 
				    end if;//#m mod #H
				end if;//II subset m
			end for; //mm in M

		 
	AM:= Seqset(AM);
			 
		for xx in AM do 
			xxin := false;
			for yy in ONew do 
				if xx subset yy then 
					xxin := true; 
					continue xx; 
				end if; 
			end for;
			if xxin eq false then
				ONew := ONew join {xx}; end if;
		end for; 

		ONew1 :={Rep(ONew)};
			for on in ONew do OUT := true;
				for on1 in ONew1 do  if IsConjugate(NGH,on,on1) then OUT := false; continue on; end if; end for;
			if OUT then ONew1 := ONew1 join{on}; end if;
			end for;
ONew :=ONew1;
 
		end for;
end while;
 




AllOvers1:= {Rep(AllOvers)};


for on in AllOvers do OUT := true;
				for on1 in AllOvers1 do  if IsConjugate(NGH,on,on1) then OUT := false; continue on; end if; end for;
			if OUT then AllOvers1 := AllOvers1 join{on}; end if;
			end for;
AllOvers:= AllOvers1;

AAM:=[x: x in AllOvers|Index(x,H) mod p ne 0];
return AAM;
end intrinsic;



////////////////////////////////////////////////////////////////////////

intrinsic AutomorphismGroup(F::FusionSystem,P::Grp)-> GrpAuto
{Calculates the automorphism group of P}
SS:= F`subgroups;
Essentials:= F`essentials;
B:= F`borel;
S:= F`group;
if assigned(F`fusiongraph) eq false then 
          F`fusiongraph, F`maps:= FusionGraph(F); 
      end if; 
Gamma:= F`fusiongraph;
Theta := F`maps; 

V:= Vertices(Gamma);
IP:= V!Index(SS,P);

ComponentP:= Setseq(IdentifyFOrbit(F,P));
 
for x in ComponentP do MakeAutos(SS[Index(x)]); end for;

AutP:= P`autogrp;

AP := sub<AutP|>;


//First we make all the maps between members of ComponentP
 


for v in ComponentP do 
Theta[[Index(v),Index(v)]]:= Identity(SS[Index(v)]`autogrp); 
end for;

for i in[1.. #ComponentP] do
    for j in [i+1.. #ComponentP] do
        ii:= ComponentP[i];jj:= ComponentP[j]; 
        Geo:=Geodesic(ii,jj); 
        gg := Identity(SS[Index(ii)]`autogrp); 
        for iii:= 1 to #Geo-1 do 
            gg:= gg*Theta[[Index(Geo[iii]),Index(Geo[iii+1])]];  
        end for;
         Theta[[Index(ii),Index(jj)]]:= gg;
        gg := Identity(SS[Index(jj)]`autogrp); 
        
        for iii:= #Geo to 2 by -1 do 
            gg:= gg*Theta[[Index(Geo[iii]),Index(Geo[iii-1])]];  
        end for;
        Theta[[Index(jj),Index(ii)]]:= gg; 
    end for;
end for;

TranB:= AssociativeArray(ComponentP);
for x in ComponentP do
    TranB[x]:= Transversal(B,Normalizer(B,SS[Index(x)])); 
end for;



CP:= CartesianProduct(Essentials,ComponentP);
PsinEs:=AssociativeArray(CP);
for E in Essentials do 
    if E eq S then continue; end if;
    for xx in  ComponentP do 
            PsinEs[<E,xx>]:= [b:b in TranB[xx]|SS[Index(xx)]^b subset E]; 
    end for;
end for;


 





//Now we start building AP=Aut_F(P)

AP:= AutYX(Normalizer(B,P),P);

for ii in ComponentP do
    R := SS[Index(ii)]; 
    if R eq P then continue; end if; 
    AR := AutYX(Normalizer(B,R),R);
        AP := sub<AutP|AP,{Theta[[Index(IP),Index(ii)]]*gg*Theta[[Index(ii),Index(IP)]]: gg in Generators(AR) }>; 
end for;
 
for ii in ComponentP do R := SS[Index(ii)]; 
    if R eq P then continue ii; end if; 
    for jj in ComponentP do T := SS[Index(jj)]; 
    if T in {P, R} then continue jj; end if; 
    AP := sub<AutP|AP, Theta[[Index(IP),Index(ii)]]*Theta[[Index(ii),Index(jj)]]*Theta[[Index(jj),Index(IP)]]>;
    end for;
end for;
    
 
  
 
    for ee in [2..#Essentials ] do 
         E:= Essentials[ee]; 
         AE:= F`essentialautos[ee];
Done:={};
         for ii in ComponentP do 
            R:= SS[Index(ii)];
            for b in PsinEs[<E,ii>] do
                Rb:= R^b; if Rb in Done then continue b; end if;
                cb:=ConjtoHom(R,Rb,b);
                cb1:=ConjtoHom(Rb,R,b^-1);
                OO,AFRb, TT:= AutOrbit(E,Rb,AE); 
                gamma:= {Theta[[Index(IP),Index(ii)]]*cb*gg*cb1*Theta[[Index(ii),Index(IP)]]:gg in Generators(AFRb)};
                AP:=sub<AutP|AP,gamma>;
                for tt in TT do
                    Rbtt:= SubMap(tt,S,Rb);
                    for jj in ComponentP do a,d:=IsConjugate(B,Rbtt,SS[Index(jj)]); 
                    if a then kk:= jj;break; end if; 
                    end for; //jj
                    cd1:= ConjtoHom(SS[Index(kk)], Rbtt, d^-1);
                    ThetaRbtoRbtt:= cb1*Theta[[Index(ii),Index(kk)]]*cd1;
                AP:=sub<AutP|AP, Theta[[Index(IP),Index(ii)]]*cb*ThetaRbtoRbtt*tt^-1*cb1*Theta[[Index(ii),Index(IP)]]>;
                end for; //tt
                Done := Done join Seqset(OO);
            end for; //b
        end for; //ii
    end for;//ee
    return AP;
end intrinsic;
  
/////////////////////////////////////////////////////////////////////
intrinsic SubgroupsAutClasses(S::PCGrp)-> SeqEnum
{Calculates centric subgroups of S up to Aut(S) conjugacy}
SS:= [x`subgroup:x in Subgroups(S)|IsSCentric(S,x`subgroup)];
A,beta:= Holomorph(S);
SSb :=[SubMap(beta,A,x):x in SS];
TT:=[];K:={1};k:=1;
for i := 1 to #SSb do T:= SSb[i]; if #K ne 0 then k:= Min(K); end if; K:={};
    for j := k to i-1 do print i,j;
        if #T ne #SSb[j] then continue j; else K:= K join {j};end if;
        if IsConjugate(A, T,SSb[j]) eq true then continue i; end if;
    end for;
    Append(~TT,SS[i]);
end for;
return TT;
end intrinsic;
//////////////////////////////////////////
intrinsic SemiDirectProduct(V::ModGrp:Perm:= false)-> Grp
{Constructs the semidirect product of a module and the module for the group}
G:= Group(V);
F:= Field(V);
T:= TrivialModule(G,F);
W:= DirectSum(T,V);
G1:= MatrixGroup(W);
n:= Dimension(W);
H:= GL(n,F);
K:= sub<H|G1>;

for k in [1..n-1] do J:= Identity(H);J:= Eltseq(J);
J[k*n+1]:= Identity(F);J:= H!J;  
K:= sub<H|J,K>;

end for;if Perm then K:= CosetImage(K,G1); end if;
return K;
end intrinsic;
//////////////////////////////////////////
intrinsic AutFCore(Es::SeqEnum,AutE::SeqEnum)->Grp,GrpAuto
{calculates F core and action on it}
F:= Es[1];
for i := 2 to #Es do  F:= F meet Es[i];end for; 
 Fn:= sub<F|>;
 while F ne Fn do
 Fn:= F;
 for i := 1 to #Es do
    A:= AutOrbit(Es[i],F,AutE[i]);
    for x in A do F := F meet x; end for;
 end for;
 end while;
MakeAutos(F); K:= Inn(F); 
    for i := 1 to #Es do  K:=  sub<F`autogrp|K,Generators(AutE[i])>; end for;
    return F,K;
end intrinsic;
 
////////////////////////////////////////////////
intrinsic AllProtoEssentials(S::Grp:OpTriv:=false, pPerfect:= false,Printing:= false)-> SeqEnum
{Makes all protosessentials up to automorphisms of S the parameters ask for  O_p(F)=1 and O^p(\F)= \F}

 
 
ZZ:= Integers(); //Integer Ring
 
p:= FactoredOrder(S)[1][1]; 
 nn:= Valuation(#S,p);



//Here are automorphisms of S and centric subgroups of S
S:= PCGroup(S);

MakeAutos(S);
InnS:=Inn(S);
AutS:= S`autogrp;
map:= S`autopermmap;
AutSp:= S`autoperm;
InnSp:= SubMap(map,AutSp, InnS);
Sbar, bar:= S/Centre(S);
TT:= Subgroups(Sbar);
SS:= [Inverse(bar)(x`subgroup):x in TT|IsSCentric(S,Inverse(bar)(x`subgroup))];
if Printing eq true then print "the group has", #SS, "centric subgroups"; end if;
 


///////////////////////////////////
///We precalculate certain properties of S. The objective here is to eliminate
///most  p-groups S before we calculate and construct the possible Borel subgroups 
///associated with S.
///We do this first as there may be many  of Borel subgroups which we don't need 
///to calculate in some circumstances.
/////////////////////////////////////

ProtoEssentials:=[];// This sequence will contain the ProtoEssential subgroups
//
if IsMaximalClass(S) and #S ge p^5 then 
    LL:= LowerCentralSeries(S);  
    T:=[];
     Append(~T,Centralizer(S, LL[2],LL[4]));
     C:= Centralizer(S, LL[nn-2]);
     if C in T eq false then 
        Append(~T,C); end if; 
     T:= T cat [x:x in SS| #x eq p^2 and LL[nn-1] subset x and not x subset  T[1]  and not x subset C ] 
     cat 
     [x:x in SS| #x eq p^3 and LL[nn-2] subset x  and not x subset  T[1]  and not x subset C ]; 
      TT:=[];
     for x in T do 
            Nx:=Normalizer(S,x);
        	A:=AutYX(Nx,x);
        	Ap:= SubMap(x`autopermmap,x`autoperm ,A);
        	Innerp:= SubMap(x`autopermmap,x`autoperm , Inn(x));
            RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
            if not RadTest then continue x; end if;
        	Append(~TT,x);
     end for;         
       ProtoEssentials:=   TT;
end if; 
        
if IsMaximalClass(S) eq false  or #S le p^4 then  
for x in SS do   
	if x eq S then continue x; end if; 
	if IsCyclic(x) then  continue x; end if;
	Nx:=Normalizer(S,x);
	A:=AutYX(Nx,x);
	Ap:= SubMap(x`autopermmap,x`autoperm ,A);
	Inner:= Inn(x);
	Innerp:= SubMap(x`autopermmap,x`autoperm ,Inner);
    RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
    if not RadTest then continue x; end if;
	P:= Index(Ap,Innerp);
	Frat:=FrattiniSubgroup(x);
	FQTest := Index(x,Frat) ge P^2;
        //This is a bound obtained by saying that $\Out_\F(x)$ acts faithfully on $x/\Phi(x)$.  
        //The order of such faithful modules is at least $|\Out_S(x)|^2$.
 	if FQTest eq false then continue x; end if; 
	SylTest, QC:=IsStronglypSylow(Ap/Innerp);print "here";
        //If $x$ is essential, then $\Out_F(x)$ should have a strongly $p$-embedded. 
        //Here we check that the Sylow $p$-subgroup is compatible with this.
	if SylTest eq false   then continue x; end if; 
	if QC eq false and IsSoluble(x`autoperm)  then   continue x; end if; 
	ProtoEssentials:= Append(ProtoEssentials,x); 
end for;
end if;
////////////////////////////////
///We need some subgroups in ProtoEssentials;
///////////////////////////////////
 
if  #ProtoEssentials eq 0 then return []; end if; 


///Notice that if E is protoessential, then so is E\alpha for alpha in AutS
ProtoEssentialAutClasses:= Setseq({Set(AutOrbit(S,PE,S`autogrp)):PE in ProtoEssentials});
ProtoEssentialAutClasses:= [Rep(x):x in ProtoEssentialAutClasses];
 
  
if OpTriv then if CharSbgrpTest(ProtoEssentials,S) eq true then return []; end if; end if;
   
 
    ///This test takes Q as the intersection of all the members of the members 
    //of ProtoEssentials and checks if any of them are characteristic in all members 
    //of ProtoEssentials and S. If some non-trivial subgroup is then O_p(\F)\ne 1.

   
if pPerfect then H:= sub<S|ProtoEssentials,{x^-1*a(x):a in Generators(S`autogrp), x in S}>; 
if  H ne S then return []; end if; end if;
 //This tests is with this set of protoessentials that O^p(\F) <F. 
   
/////////////////////
///////Here we  make all the candidates for Out_\F(x) for x in ProtoEssentials 
///////and check that they have strongly p-embedded subgroups.
///////////////////



for i in [1..#ProtoEssentialAutClasses] do 
	P:= ProtoEssentialAutClasses[i];
	MakeAutos(P);
	AutP:=P`autogrp;
	mapP:= P`autopermmap;
	AutPp:= P`autoperm;
	InnP:=Inn(P);
	InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
	AutSP:=AutYX(Normalizer(S,P),P );
	AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>;	
	Q:= AutSPp/InnPp;

	M:=SubnormalClosure(AutPp,AutSPp);
	
	Candidates :=[];
    	pVal:=Valuation(#AutPp,p);
    	NormVal:=Valuation(#AutSPp,p);
       
        QC:=IsQuaternionOrCyclic(Q); 
        if not QC  then
            Mbgs:= NonsolvableSubgroups(M:OrderDividing:= ZZ!(#AutPp/((p^(pVal-NormVal)))));
            ///So the elements of Mbgs have a Sylow subgroup which has the same order as AutSP
            AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#sub<AutPp|xx`subgroup,InnPp>,p) eq NormVal];
		APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
		for kk in [1..#AutPCandidates] do  
            		GG:= AutPCandidates[kk];
           		Sylow:=SylowSubgroup(GG,p);
            		a,b:=IsConjugate(AutPp,Sylow,AutSPp);
			if a then Append(~APC,GG^b); end if; 
		end for;
		AutPCandidates:= APC;
	    end if;//QC
                
    	if QC and IsCyclic(Q)  then
                     AutPCandidates:= OverGroupsSylowEmbedded(M,AutSPp,InnPp,p);
        end if;  
	
	    if QC and not IsAbelian(Q) then  
		Mbgs:= Subgroups(M, InnPp:   OrderDividing:= ZZ!(#AutPp/(p^(pVal-NormVal))));
              	AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#xx`subgroup,p) eq NormVal];
		APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
		for kk in [1..#AutPCandidates] do  
            		GG:= AutPCandidates[kk];
           		Sylow:=SylowSubgroup(GG,p);
            		a,b:=IsConjugate(AutPp,Sylow,AutSPp);
			if a then Append(~APC,GG^b); end if; 
		end for;
		AutPCandidates:= APC;
	end if;
        
	P`autF:=[];//This is where we store all potential Aut_F(P) up to Aut(P) conjugacy.

       	for GG in AutPCandidates do
		if  IsStronglypEmbeddedMod(GG,InnPp,p) eq false then continue GG; end if;
            NGG:= Normalizer(AutPp,GG);  
            NGGsubs:=[sub<AutPp|xx`subgroup> :xx in Subgroups(NGG: OrderMultipleOf :=#GG)| 
                                GG subset xx`subgroup and Index(xx`subgroup,GG) mod p ne 0];
            	for GGs in NGGsubs do 
            		Append(~P`autF,sub<AutP|{Inverse(mapP)(g): g in Generators(GGs)}>); 
		        end for; 
        end for;//GG  
end for;  // i in [1..ProtoEssentialAutClasses]  



ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|assigned(x`autF)];
ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|#x`autF ne 0];

if Printing then 
	print "The set ProtoEssentialAutClasses has", #ProtoEssentialAutClasses,"elements";  
end if;
if Printing then 
	for x in ProtoEssentialAutClasses do  
		print "the protoessential aut class  representaive have ", #x`autF, "potential automorphism groups"; 
	 end for; 
end if;

 

return ProtoEssentialAutClasses;
end intrinsic;

/////////
/////////////////////////////////////
///////////////////////////////////////


intrinsic Blackburn(p::RngIntElt,n::RngIntElt,alpha::RngIntElt,beta::RngIntElt,gamma::RngIntElt,delta::RngIntElt)->Grp
{constructs Blackburn's metaabelian maximal class group of order p^n}
require IsPrime(p) : "the first element must be a prime"; 
require n eq 6:"this is only implemented for n=6";


        S<s, s1,s2,s3,s4,s5> := Group<s, s1,s2,s3,s4,s5|
        (s1,s)*s2^(-1),
        (s2,s)*s3^(-1),
        (s3,s)*s4^(-1),
        (s4,s)*s5^(-1),
         (s,s5), 
        
        //(32) from Blackburn.
        (s1,s2)*s5^(-beta)*s4^(-alpha),//(33)
        (s1,s3)*s5^(-alpha),//(34)
        (s1,s4),//(35)
        (s1,s5),//(35)

        s^p*s5^(-delta),//(36)


        s1^p*s2^Binomial(p,2)*s3^Binomial(p,3)*s4^Binomial(p,4)*s5^Binomial(p,5)*s5^(-gamma),//(37)
        //s2^p,s3^p,s4^p, 
        
       s2^p*s3^Binomial(p,2)*s4^Binomial(p,3)*s5^Binomial(p,4),

        s3^p*s4^Binomial(p,2)*s5^Binomial(p,3),

        s4^p*s5^Binomial(p,2),

        s5^p>;S:= PCGroup(S);
 return S;
 
 end intrinsic;


/////////////////////////
/////We need to be able to detect when two homomorphisms are equal: 
//////////////////////

intrinsic homeq(x::Map,y::Map)->Bool{checks if two maps are equal}
 X:=Domain(x); X1:= Image(x);
Y:=Domain(y); Y1 := Image(y);
    if X ne Y  or X1 ne Y1 then return false; end if;
gens:=Generators(X);
     for gg in gens do
        if x(gg) ne y(gg) then return false; end if;
     end for;
 return true;
 end intrinsic;
 
 //////////
 intrinsic IsQuaternionOrCyclic(G::Grp)->Bool
 {Is a quaternion or a cyclic group}
 if #G eq 1 then return true;end if; 
 p:= FactoredOrder(G)[1][1];
 C:= ConjugacyClasses(G);
 if # {x: x in C|x[1] eq p} eq p-1 then return true; end if;
 return false;
 end intrinsic;
 
 ////////////////////////////////////////////////////////////////////////////////
///Functions which creates $O^pi(G)$.
///for various pi
///////////////////////////////////////////////////////////////////////
intrinsic piResidual(G::Grp, pi::SeqEnum)-> Grp
{Determine O^\pi(G)}
JJ:= PrimeFactors(#G);
Resid:=sub<G|>;
for x in JJ do 	
	if x in pi then continue x; end if;
	P:= Sylow(G,x);
	N:= NormalClosure(G,P);
	Resid:= sub<G|Resid,N>;
end for;
return Resid;

end intrinsic;
//////////////////////////////////////////////////////////////

intrinsic pResidual(G::Grp, p::RngIntElt)-> Grp
{Determine O^p(G)}
R:=piResidual(G,[p]);
return R;
end intrinsic;

intrinsic piprimeResidual(G::Grp, pi :: SeqEnum)-> Grp
{Determine O^p(G)}
 JJ:= PrimeFactors(#G);
pistar:= {w: w in JJ| (w in pi) eq false};
R:=piResidual(G,pistar);
return R;
end intrinsic;

intrinsic pprimeResidual(G::Grp, p::RngIntElt)-> Grp
{Determine O^p(G)}
P:= Sylow(G,p);
return NormalClosure(G,P);
end intrinsic;
/////////////////////////////
//// Is the p-group Maximal class
/////////////////////////////

intrinsic IsMaximalClass(G::Grp)-> Bool
{Check if G is maximal class}
f:= FactoredOrder(G);
require #f eq 1 : "the group  is not a p-group"; 
 n:= NilpotencyClass(G);

return n eq (f[1][2]-1);
end intrinsic;
/////////////////////////////
//// Does the p-group have an abelian subgroup of index p
/////////////////////////////

intrinsic  MaximalAbelian(G::Grp)-> Bool
{Check if G gas a maximal abelian subgroup}
f:= FactoredOrder(G);
require #f eq 1:"the group  is not a p-group"; 
M:= MaximalSubgroups(G);
for x in M do 
    y:= x`subgroup; 
    if IsAbelian(y) then return true; end if; 
end for;

return  false;
end intrinsic;

///////////////////////////////////////////////
/////sub normal closure of a subgroup
////////////////////////////////////////////////
intrinsic SubnormalClosure(G::Grp,T::Grp)-> Grp
{Determines the subnormal closure of $T$ in G}

SNew:= NormalClosure(G,T);
SN:= G;
while SN ne SNew do
SN:= SNew;
SNew:= NormalClosure(SN,T);
end while;
return SN;
end intrinsic;



////////////////////////////
////// IdentifyGroup3to7(S::GRP)->
////// 
////////////////////////


intrinsic IdentifyGroup3to7(S::Grp)->RngIntElt
{Identifies Group of Order 3^7}
require #S eq 3^7:"Group doesn't have order 3^7";
for i in [1..NumberOfSmallGroups(3^7)] do
        if IsIsomorphic(S,SmallGroup(3^7,i) ) then return i; end if;
end for; 
end intrinsic;

//////////////////////////////////////////////////////////
intrinsic AllFusionSystems(S::Grp:SaveEach:=false,Printing:=false,OutFSOrders:=[],OpTriv:=true,pPerfect:= true)-> SeqEnum
{Makes all fusion systems with O_p(F)=1 and O^p(\F)= \F}
 
 
 
FNumber:=0; //This is to help when saving fusion systems
ZZ:= Integers(); //Integer Ring
FF:=[]; //We will put the possible systems in here  

p:= FactoredOrder(S)[1][1]; 
 nn:= Valuation(#S,p);



//Use that we know fusion systems with an abelian subgroup

if IsAbelian(S) then return FF; end if;

///Lemma~7.1 shows that $S:Z(S) \gt p^2 or |S|\le p^3

if Index(S,Centre(S)) le p^2 and #S ge p^4  then return FF; end if; 
 
 

//Here are automorphisms of S and centric subgroups of S
S:= PCGroup(S);

MakeAutos(S);
InnS:=Inn(S);
AutS:= S`autogrp;
map:= S`autopermmap;
AutSp:= S`autoperm;
InnSp:= SubMap(map,AutSp, InnS);

//We use Cor 6.2 from ANTONIO Diaz, ADAM GLESSER, NADIA MAZZA, AND SEJONG PARK
if p ge 5 and #FactoredOrder(S`autogrp) eq 1 then return []; end if; 


Sbar, bar:= S/Centre(S);
TT:= Subgroups(Sbar);
SS:= [Inverse(bar)(x`subgroup):x in TT|IsSCentric(S,Inverse(bar)(x`subgroup))];
if Printing eq true then print "the group has", #SS, "centric subgroups"; end if;
 
 
 
 
///////////////////////////////////
///We precalculate certain properties of S. The objective here is to eliminate
///most  p-groups S before we calculate and construct the possible Borel subgroups 
///associated with S.
///We do this first as there may be many  of Borel subgroups which we don't need 
///to calculate in some circumstances.
/////////////////////////////////////

ProtoEssentials:=[];// This sequence will contain the ProtoEssential subgroups
//
if IsMaximalClass(S) and #S ge p^5 then 
    LL:= LowerCentralSeries(S);  
    T:=[];
     Append(~T,Centralizer(S, LL[2],LL[4]));
     C:= Centralizer(S, LL[nn-2]);
     if C in T eq false then 
        Append(~T,C); end if; 
     T:= T cat [x:x in SS| #x eq p^2 and LL[nn-1] subset x and not x subset  T[1]  and not x subset C ] 
     cat 
     [x:x in SS| #x eq p^3 and LL[nn-2] subset x  and not x subset  T[1]  and not x subset C ]; 
      TT:=[];
     for x in T do 
            Nx:=Normalizer(S,x);
        	A:=AutYX(Nx,x);
        	Ap:= SubMap(x`autopermmap,x`autoperm ,A);
        	Innerp:= SubMap(x`autopermmap,x`autoperm , Inn(x));
            RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
            if not RadTest then continue x; end if;
        	Append(~TT,x);
     end for;         
       ProtoEssentials:=   TT;
end if; 

        
if IsMaximalClass(S) eq false  or #S le p^4 then  
for x in SS do   
	if x eq S then continue x; end if; 
	if IsCyclic(x) then  continue x; end if;
	Nx:=Normalizer(S,x);
	A:=AutYX(Nx,x);
	Ap:= SubMap(x`autopermmap,x`autoperm ,A);
	Inner:= Inn(x);
	Innerp:= SubMap(x`autopermmap,x`autoperm ,Inner);
    RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
    if not RadTest then continue x; end if;
	P:= Index(Ap,Innerp);
	Frat:=FrattiniSubgroup(x);
	FQTest := Index(x,Frat) ge P^2;
        //This is a bound obtained by saying that $\Out_\F(x)$ acts faithfully on $x/\Phi(x)$.  
        //The order of such faithful modules is at least $|\Out_S(x)|^2$.
 	if FQTest eq false then continue x; end if; 
	SylTest, QC:=IsStronglypSylow(Ap/Innerp);
        //If $x$ is essential, then $\Out_F(x)$ should have a strongly $p$-embedded. 
        //Here we check that the Sylow $p$-subgroup is compatible with this.
	if SylTest eq false   then continue x; end if; 
	if QC eq false and IsSoluble(x`autoperm)  then   continue x; end if; 
	ProtoEssentials:= Append(ProtoEssentials,x); 
end for;
end if;
////////////////////////////////
///We need some subgroups in ProtoEssentials;
///////////////////////////////////
 
 


///Notice that if E is protoessential, then so is E\alpha for alpha in AutS
ProtoEssentialAutClasses:= Setseq({Set(AutOrbit(S,PE,S`autogrp)):PE in ProtoEssentials});
ProtoEssentialAutClasses:= [Rep(x):x in ProtoEssentialAutClasses];
 
  
if OpTriv and  CharSbgrpTest(ProtoEssentials,S)   then return FF; end if;  
   
 
    ///This test takes Q as the intersection of all the members of the members 
    //of ProtoEssentials and checks if any of them are characteristic in all members 
    //of ProtoEssentials and S. If some non-trivial subgroup is then O_p(\F)\ne 1.

   
if pPerfect then H:= sub<S|ProtoEssentials,{x^-1*a(x):a in Generators(S`autogrp), x in S}>; 
if  H ne S then return []; end if; end if;
 //This tests is with this set of protoessentials that O^p(\F) <F. 
     
/////////////////////
///////Here we  make all the candidates for Out_\F(x) for x in ProtoEssentials 
///////and check that they have strongly p-embedded subgroups.
///////////////////


for i in [1..#ProtoEssentialAutClasses] do 
	P:= ProtoEssentialAutClasses[i];
	MakeAutos(P);
	AutP:=P`autogrp;
	mapP:= P`autopermmap;
	AutPp:= P`autoperm;
	InnP:=Inn(P);
	InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
	AutSP:=AutYX(Normalizer(S,P),P );
	AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>;	
	Q:= AutSPp/InnPp;

	M:=SubnormalClosure(AutPp,AutSPp);
	
	Candidates :=[];
    	pVal:=Valuation(#AutPp,p);
    	NormVal:=Valuation(#AutSPp,p);
      
        QC:=IsQuaternionOrCyclic(Q); 
        if not QC  then
            Mbgs:= NonsolvableSubgroups(M:OrderDividing:= ZZ!(#AutPp/((p^(pVal-NormVal)))));
            ///So the elements of Mbgs have a Sylow subgroup which has the same order as AutSP
            AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#sub<AutPp|xx`subgroup,InnPp>,p) eq NormVal];
		APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
		for kk in [1..#AutPCandidates] do  
            		GG:= AutPCandidates[kk];
           		Sylow:=SylowSubgroup(GG,p);
            		a,b:=IsConjugate(AutPp,Sylow,AutSPp);
			if a then Append(~APC,GG^b); end if; 
		end for;
		AutPCandidates:= APC;
	    end if;//QC
                
    	if QC and IsCyclic(Q)  then  
                     AutPCandidates:= OverGroupsSylowEmbedded(M,AutSPp,InnPp,p);
        end if;  
	
	    if QC and not IsAbelian(Q) then  
		Mbgs:= Subgroups(M, InnPp:   OrderDividing:= ZZ!(#AutPp/(p^(pVal-NormVal))));
              	AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#xx`subgroup,p) eq NormVal];
		APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
		for kk in [1..#AutPCandidates] do  
            		GG:= AutPCandidates[kk];
           		Sylow:=SylowSubgroup(GG,p);
            		a,b:=IsConjugate(AutPp,Sylow,AutSPp);
			if a then Append(~APC,GG^b); end if; 
		end for;
		AutPCandidates:= APC;
	end if;
        
	P`autF:=[];//This is where we store all potential Aut_F(P) up to Aut(P) conjugacy.

       	for GG in AutPCandidates do
		if  IsStronglypEmbeddedMod(GG,InnPp,p) eq false then continue GG; end if;
            NGG:= Normalizer(AutPp,GG);  
            NGGsubs:=[sub<AutPp|xx`subgroup> :xx in Subgroups(NGG: OrderMultipleOf :=#GG)| 
                                GG subset xx`subgroup and Index(xx`subgroup,GG) mod p ne 0];
            	for GGs in NGGsubs do 
            		Append(~P`autF,sub<AutP|{Inverse(mapP)(g): g in Generators(GGs)}>); 
		        end for; 
        end for;//GG  
end for;  // i in [1..ProtoEssentialAutClasses]  



ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|assigned(x`autF)];
ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|#x`autF ne 0];

if #ProtoEssentialAutClasses eq 0 then return []; end if;
 
 

if OpTriv and CharSbgrpTest(ProtoEssentialAutClasses,S)   then return []; end if;  
if Printing then print "The set ProtoEssentialAutClasses has", #ProtoEssentialAutClasses,"elements";  end if;


//We calculate the possible Borel subgroups and S pairs.


pVal:= Valuation(#AutSp,p); m:= ZZ!(#AutSp/p^pVal);
BorelsandS:=[];
if m ne 1  then
    if IsSoluble(AutSp) then 
        PAut, tt:= PCGroup(AutSp); 
        H:=HallSubgroup(PAut,-p); 
        K:=[];
        if OutFSOrders eq [] then 
         K:= [wx`subgroup:wx in Subgroups(H)];
         else  
        for x in OutFSOrders do K:= K cat [wx`subgroup:wx in 
        Subgroups(H:OrderEqual:=x)]; 
        end for; 
        end if;
        BCand:=[]; 
       
    for k:= 1 to #K do  
        K1:= K[k]; 
            for K2 in BCand do 
            if IsConjugate(PAut,K1,K2) then   continue k;   end if;
            end for; 
        Append(~BCand,K1); 
    end for;
    BCand:= [SubInvMap(tt, AutSp, K1):K1 in BCand];
 else
  if OutFSOrders eq [] then OutFSOrders:= [1..m]; end if;
    SubsAutS:= Subgroups(AutSp:OrderDividing:=m);   
    BCand:=  [sub<AutSp|x`subgroup,InnSp>: x in SubsAutS|Index(x`subgroup,InnSp meet x`subgroup) mod p ne 0];
    BCand:= [Random(Complements(AA,InnSp)):AA in BCand];
    BCand:=[ AA:AA in BCand| #AA in OutFSOrders]; 
 end if;
 

 
    for CC in BCand do
    if not IsSoluble(CC) then print "Execution failed: The Borel group is not soluble ";   return []; end if;
        f:=hom<CC->AutS|g:->Inverse(map) (g)>;
        C:= SubMap(f,AutS,CC);  
        if #C ne 1 then B,phiB:= Holomorph(GrpFP,S, sub<AutS|C>); else B,phiB:= Holomorph(S, sub<AutS|C>);  end if; 
       // B,phiB:= Holomorph(S, sub<AutS|C>);  
        T:= phiB(S);  
       
         B, theta := PCGroup(B); T:= theta(T); ///This will not work if B is not soluble.
        BB:=[B,T];
        
        a, alpha:= IsIsomorphic(S,T); //phiB*theta does not work when Holomorph is calculcated with FP group
          for x in ProtoEssentialAutClasses do Append(~BB,SubMap(alpha,T,x)); end for;
        for ii in [3..#BB] do 
        xx:= BB[ii];
        yy:= ProtoEssentialAutClasses[ii-2];
        MakeAutos(xx);
          
            WW:=[];
            for jj in   [1..#yy`autF] do 
		    Wx:= yy`autF[jj]; 
		    WGens :=[
		    Inverse(alpha)*gamma*alpha: gamma in  Generators(Wx)];
		    WW[jj]:=sub<xx`autogrp|WGens>; 
            end for;
            xx`autF:= WW;
        end for;
     Append(~BorelsandS,BB);
end for;
else
 T, theta := PCGroup(S);
    BB:=[T,T];
    for x in ProtoEssentialAutClasses do Append(~BB,SubMap( theta,T,x)); end for;
        for ii in [3..#BB] do 
            xx:= BB[ii];yy:= ProtoEssentialAutClasses[ii-2]; MakeAutos(xx);WW:=[];
            for jj in   [1..#yy`autF] do 
                WGens:=[]; Wx:= yy`autF[jj]; 
                    for gamma in Generators(Wx) do  
                        Append(~WGens,Inverse( theta)*gamma* theta); 
                    end for;
                WW[jj]:=sub<xx`autogrp|WGens>; 
            end for;
            xx`autF:= WW; 
        end for;
     Append(~BorelsandS,BB);
end if;








if Printing then print "This group has ", #BorelsandS, " Borel groups";end if;

count:=0;
for Bor in BorelsandS do
   

    count := count+1;  
print "**********************************************";
print " Borel", count, "of", #BorelsandS, FactoredOrder(Bor[1]);
print "**********************************************";
 
  B:= Bor[1];    
S:= Bor[2];  

//We use the fact that if $B=S$ and p ge 5 then $O^p(\F)<\F$.
if p ge 5 and B eq S then continue; end if;
MakeAutos(S);
    
    	Bbar, bar:= B/Centre(S);
	subsBS:= Subgroups(Bbar:OrderDividing:=#bar(S));
	subsBS:= [Inverse(bar)(x`subgroup):x in subsBS];
	SS:= [x:x in subsBS|IsSCentric(S,x)]; 
    AutFS:=AutYX(B,S);
    InnS:=Inn(S);
    AutS:= S`autogrp;
    alpha:= S`autopermmap;
    AutSp:= S`autoperm; 
    InnSp:= SubMap(alpha,AutSp, InnS);
    AutBS:= AutYX(B,S);
    AutBp:= SubMap(alpha,AutSp, AutBS);
 
    NAutBp:= Normalizer(AutSp,AutBp);
    NAutB:= SubInvMap(alpha,AutS,NAutBp);
    ProtoEssentialAutClasses:=[Bor[j]:j in [3 ..#Bor]];

//We explode the autclasses to get all protoessentials and ajoin their potential autogrps.
ProtoEssentials:=[];
for x in ProtoEssentialAutClasses do
    Xx, Stx, Rx := AutOrbit(S,x,S`autogrp); 
    PNew := [];
    for y in SS do
        if y in Xx then 
            MakeAutos(y); 
            Append(~ProtoEssentials,y); 
            Append(~PNew,y);
        end if; 
    end for;
    
    if #PNew ne 0 then 
        for j := 1 to #PNew do
            y:= PNew[j];
            y`autF:=[];
            for AP in x`autF do
                        y`autF := Append(y`autF, sub<y`autogrp|[Inverse(Rx[Index(Xx,y)])*gamma*Rx[Index(Xx,y)]: gamma in Generators(AP)]>);
            end for;
        end for; 
    end if;
end for;//x


if OpTriv then 
//The next test uses Lemma 4.10 to show that P1 and P2 are not both essential.
// If P1 is essential, then P1' ne 1 and is normalized by Aut_\F(S) and Aut_F(E_1). This gives O_p(F) ne 1.
	if #ProtoEssentials eq 2 and p ge 5 and #S lt p^(p+3) then 
	    P1:= ProtoEssentials[1]; 
	    P2:= ProtoEssentials[2]; 
	    	if #P1 le #P2 then PP:= P2; P2:= P1; P2:= PP; end if; 
	    NSP2:= Normalizer(S,P2);  
	    PC:= Core(S,P2);
	 	if IsConjugate(B,P1,NSP2) and Index(NSP2,P2) eq p and Index(S,NSP2) eq p and 
	    Index(P2,PC) eq p and IsCharacteristic(NSP2,PC) and IsNormal(B,DerivedSubgroup(P1)) then 		ProtoEssentials:=[P2];
	    	end if;
	end if;    
end if; //OpTriv
    








Candidates:= AssociativeArray(ProtoEssentials);

for x in ProtoEssentials do Candidates[x]:= x`autF; end for; 

if pPerfect then 
//The next check is a preliminary focal subgroup check using that we know the Borel  subgroup. 
//This often gets rid of the case when $B=S$
	SB:= CommutatorSubgroup(S,B);
	S1:= sub<S|SB,ProtoEssentials>;
	if S1 ne S then   continue Bor; end if;
end if;

if OpTriv   and #ProtoEssentials eq 1   and IsNormal(B,ProtoEssentials[1]) then continue Bor; end if; 
  


if Printing then print "There are", #ProtoEssentials, "proto-essential subgroups before the extension test.\nThey have orders", 
 Explode([#ProtoEssentials[i]: i in [1..#ProtoEssentials]]);end if;

//We now make all the candidates for Aut_F(E) given our class representatives in 
//E`autF. This means that we check if the automorphisms in $Aut(N_B(E),E)$ restrict to members of $\Aut_\F(E)$.

FirstTime := true;
ProtoEssentialsT:= ProtoEssentials;
ProtoEssentialsTT:= [];

while #ProtoEssentialsT ne #ProtoEssentialsTT  do
    ProtoEssentialsTT:= ProtoEssentialsT; 
    
	if #ProtoEssentialsT eq 0 then
    if Printing then	print #ProtoEssentialsT, "proto-essentials which pass the  strongly p-embedded and extension test";
    end if;	continue Bor; 
    end if;
 
    Candidates1:=AssociativeArray(ProtoEssentialsT);
    
    Done :={};
    for i in [1..#ProtoEssentialsT] do
        P:=ProtoEssentialsT[i];
        if P in Done then continue i; end if;
        MakeAutos(P);
         if Printing then print "About to Apply AutFPC"; end if;
        Candidates1[P]:=AutFPCandidates(B,S,P,ProtoEssentialsT,Candidates,FirstTime:Printing:= Printing); 
        //next we transfer the automorphisms to everything in the AutOrbit.
         if Printing then print "AutFPC complete"; end if;
        OrbP, SSt, Repp:= AutOrbit(S,P, NAutB);
        if Printing then print "the set Repp has", #Repp, "Members"; end if;
        for nn in [2..#Repp] do
            P1:=OrbP[nn];
            MakeAutos(P1);
            beta:= Repp[nn]; 
            Candidates1[P1]:= [];
            for AP in Candidates1[P] do
                Append(~Candidates1[OrbP[nn]],
                        sub<P1`autogrp|[Inverse(beta)*theta*beta: theta in Generators(AP)]>);
            end for;
        end for;
    Done := Done join Seqset(OrbP);
     if Printing then print "the set Done", #Done, "Members"; end if;
    end for; //i
  ProtoEssentialsT:=[ProtoEssentialsT[Index(ProtoEssentialsT,x)]:x in ProtoEssentialsT| #Candidates1[x] ne 0];
Candidates:= Candidates1; FirstTime:=false;
end while;     

 

ProtoEssentials:= ProtoEssentialsT;
if #ProtoEssentials eq 0 then continue Bor; end if;

if Printing then print  #ProtoEssentialsT, 
"proto-essentials which pass both the  strongly p-embedded 
and extension test";end if;


D:= Subsets({1..#ProtoEssentials});



////////////////////////////////
///We look at the orbits of $N_Aut(S)(Aut_\F(S))$ on D. 
///As we will consider all possible automisers of members of protoessentials
///It suffices to look at $N_Aut(S)(Aut_\F(S))$ orbits and this will give us all 
///automorphism classes of fusion systems
//////////////////////////

NN:= NAutBp;
for Pr in ProtoEssentials do 
a, NNN:= AutOrbit(S,Pr,NAutB);
NN := NN meet SubMap(alpha,AutSp,NNN);
end for;

   // NN:= sub<NAutBp|NN>; 
TNB:= Transversal(NAutBp,NN);
TransAutSB:=[Inverse(alpha)(xxx):xxx in TNB];

DD:= D;
DNew:={};
while #DD ne 0 do 
    x:= Rep(DD); 
    DNew:= DNew join{x}; 
    DDD:={x};
   
    for beta in TransAutSB do 
	xnew := {beta(ProtoEssentials[w]):w in x};
   	L:={};
	for ll in xnew do
		for Proto in ProtoEssentials do 
		aa, bb:= IsConjugate(B, ll, Proto);
			if aa then L:= L join{Index(ProtoEssentials,Proto)}; end if;
		end for;
	end for;
  

DDD:= DDD join {L};   
   end for; //beta
DD := DD diff DDD;
end while; 

 
D:= DNew;
 
D:= Setseq(D);
 D1:= [#x:x in D];
ParallelSort(~D1,~D);
D:=Reverse(D);

 // this tests if there is a conjugate of essential x  which is $B$ conjugate to a subgroup of essential $y$ which using all posibilities for Aut_\F(y) is we can see $x$ is not fully Normalized
 Forbiddenpairs :={};
 
 for x in ProtoEssentials do 
    NSx := Normalizer(S,x);
    for y in ProtoEssentials do
         
        if exists(tt){ tt: tt in Conjugates(B,x)|tt subset y} then 
            if forall{w:w in Candidates[y]| exists{cc:cc in AutOrbit(y,tt,w)|#Normaliser(S,cc) gt #NSx}} 
            then Forbiddenpairs:= Forbiddenpairs join{{x,y}}; 
            end if;
        end if;
    end for;
end for;
if Printing then print "The number of forbidden pairs of essential subgroups is ", #Forbiddenpairs;end if;
/////


////////////////Main Search starts here. 



for ss in [1..#D] do//This is the main loop considering all subsets of ProtoEssentials
    EssSup:= D[ss];//This set specifies which essential subgroups we select from ProtoEssentials.

    if #EssSup eq 0 then continue ss;
    end if; //the fusion system must have rank at least one
    ssSequence:=SetToSequence(EssSup);
    
 	Essentials:=[ProtoEssentials[i]: i in EssSup];
   if OpTriv then if #EssSup eq 1 and IsNormal(B,Essentials[1]) then continue ss; end if;end if;
    if exists{w: w in Forbiddenpairs| w subset Essentials} then continue ss; end if;

  max:= Max({#e: e in Essentials});
Candidates1:=Candidates; 
Maxes:= {e:e in Essentials|#e eq max};

 
FLAG := false;
for P in Essentials do 
    if p*#P ge max and IsNormal(S,P) eq false  then  
         PB:= Conjugates(B,P); 
         Tst:={};  
         for M in Maxes do 
            Tst := Tst join {x subset M:x in PB};
         end for;
          if Tst eq {false} or P in Maxes then 
            MakeAutos(P);
            AutP:=P`autogrp;
            mapP:= P`autopermmap;
            AutPp:= P`autoperm;
            InnP:=AutYX(P,P);
            InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
            AutSP:=AutYX(Normalizer(S,P),P );
            AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>;
            AutBP:=AutYX(Normalizer(B,P),P );
            AutBPp:=sub<P`autoperm|{mapP(g): g in Generators(AutBP)}>;
            for II in [1.. #Candidates[P]] do AP:= Candidates[P][II]; 
                APp:=SubMap(P`autopermmap, P `autoperm,AP);
                 if Normalizer(APp,AutSPp) ne AutBPp then 
                     Candidates1[P][II]:=sub<AP|>; FLAG:= true; 
                 end if;
            end for;//II
        end if;// #Tst;
    end if;
end for;            
        
        
if FLAG then 
CandidatesNew:=AssociativeArray(ProtoEssentials); 
for x in ProtoEssentials do
CandidatesNew[x]:=[];
for y in Candidates1[x] do if #y ne 1 then Append(~CandidatesNew[x],y); end if; end for;
end for;
else CandidatesNew:=Candidates;
end if;
  

 
////This next test makes sure that if we have essential subgroups x<y then 
////|N_S(x)|\ge  N_S(x\alpha) for all alpha in $\Aut_F(y)$
Candidates1 := CandidatesNew;

FLAG := false;
for x in Essentials do 
    for y in Essentials do 
    if x subset y and x ne y then 
        for II in [1..#CandidatesNew[y]] do AutFy:= CandidatesNew[y][II];
            xOrb:= AutOrbit(y,x,AutFy);
            for w in xOrb do  
                if #Normalizer(S,w) gt #Normalizer(S,x) then     
                    Candidates1[y][II]:=sub<AutFy|>; FLAG:= true;
                end if;
            end for;
        end for;
    end if; 
    end for;
end for; 


if FLAG then 
CandidatesNew:=AssociativeArray(ProtoEssentials); 
for x in ProtoEssentials do
    CandidatesNew[x]:=[]; 
    for y in Candidates1[x] do 
        if #y ne 1 then Append(~CandidatesNew[x],y); 
        end if; 
    end for;
end for;
end if;
  
  
  
 
CandidatesNewp:= AssociativeArray(ProtoEssentials);


for xP in ProtoEssentials do
    CandidatesNewp[xP]:=[ SubMap(xP`autopermmap, xP`autoperm,CandidatesNew[xP][kk]): kk in [1..#CandidatesNew[xP]]];
    
end for;

 
 

 
 
  Cart:=[];
  for e in EssSup do
    Cart:=Append(Cart,[1..#CandidatesNew[ProtoEssentials[e]]]);
  end for;

 CPCart:=CartesianProduct(Cart);

     // now run through all possible fusion systems on the chosen set of essential subgoups
 
if Printing then print "Checking", #CPCart, "automizer sequences with", #EssSup, 
"essentials of orders:", Explode([#ProtoEssentials[i]: i in EssSup]);end if;


/////////////////////////////////////////////////////////////////////////////////
/////for each subset we make a cartesian product, where each element gives a
///// potential fusion system
///// The set EssSup, Essentials support, defines the essentials subgroups of the fusion system
/////  For each EssSup we run through the various assignments of automisers to the essentials
//////For example if EssSup<--> [S,E_1,dots, E_k] then we run through all the possibilities for
//// Aut_F(E_1) ...
/////////////////////////////////////////////////////////////////////////////////
 

//First we make the subgroup of Aut(S) which normalizes all the essential subgroups and B.

NAutBQp:=NAutBp;

for Q in Essentials do
Orb, NN:=AutOrbit(S, Q,NAutB);
NAutBQp:= NAutBQp meet SubMap(S`autopermmap, S`autoperm,NN);
end for;


T2:= Transversal(NAutBp,NAutBQp);
L:= Set(Essentials);
T3:= {y: y in T2|{Inverse(alpha)(y)(x): x in L} eq  L};
NAutBQp:= sub<NAutBp|NAutBQp,T3>;


NAutBQ:= SubInvMap( alpha, S`autogrp,NAutBQp); 


CPCart:= Set(CPCart); 

cpc:= #CPCart; 
 
//This defines an action of CPCart 
  alpha:=S`autopermmap;
  function Act(x)
     tup:= x[1];ff:= x[1];
     theta := x[2];
     for i in [1..#Essentials] do 
            	ee:= Essentials[i];  
            	jj:= Index(Essentials,SubMap(theta,S,ee));
            	eee:= Essentials[jj];  
                J:= sub<eee`autogrp|[Inverse(theta)*gen*theta:gen in 
                Generators(CandidatesNew[ee][ff[i]])]>; 
                Jp:= SubMap(eee`autopermmap, eee`autoperm,J);
                kk:= Index(CandidatesNewp[eee],Jp); 
                jjj:= Index(Essentials,eee);
                tup[jjj]:=kk;
            end for;
            return tup;
 end function;

  
  
  
  
  
  while #CPCart ne 0 do  
   Bob:= false; 
   possFSys:=Rep(CPCart); 
 
  //POrb is a partial orbit.  This speeds things up as finding large  full orbits seems to be more time consuming. This routine will with high probability find small orbits anyway. The strange choice to perform it twice is to get a balance between speed and getting enough elements of the orbit.

     POrb:= {possFSys, Act(<possFSys,NAutBQ.1>)  };
     for i:= 1 to 2 do 
      POrb2:= POrb;
     	for x in Generators(NAutBQ) do;
     		for ff in POrb2 do
	     		z:= Act(<ff,x>);
	     		if not z in CPCart then Bob := true; break i; end if;
	     		POrb:= POrb join {z};
	     	end for;
	end for;
     end for;
     if Bob then CPCart:= CPCart diff POrb;continue; end if;//continues while
   Bob:= false;
     POrb2:= POrb;
     for j := 1 to 3 do 
     	x:= Random(Generators(NAutBQ));
     	POrb2:= POrb;
     	for ff in POrb2 do
	     		z:= Act(<ff,x>);
	     		if not z in CPCart then Bob := true; break j; end if;
	     		POrb:= POrb join {z};
	     	end for;
     end for;
  
 
 	CPCart:= CPCart diff POrb; //removes the partial orbit
   if Bob then continue; end if;//continues while
   Bob:= false;
   
    AutF:=AssociativeArray(ProtoEssentials); //this is the fusion system we will make
    AutF[S]:=AutFS; // this was fixed at the start it is Aut_B(S)
    ////We now populate AutF with the appropriate candidate automisers
    for k in [1..#possFSys] do
       AutF[ProtoEssentials[ssSequence[k]]]:=CandidatesNew[ProtoEssentials[ssSequence[k]]][possFSys[k]];
    end for;
    Autos:=[AutF[S]]; ///Autos is the automiser sequence.
           
	for e in Essentials do 
        	Autos:= Append(Autos,AutF[e]);    
   	end for;
     
 	if Printing then print "Remains to do",#CPCart, "of",cpc; end if; 
     
	if pPerfect and not FocalSubgroupTest(B,S, Essentials,AutF) then  continue; //while
 	end if;  
 	
 	
  	if OpTriv and  not FCoreTest(S,Essentials,AutF) then  continue; end if;   


  //    This next test checks that if P is normal in S that its "obvious" automiser has $\Aut_S(P) as a Sylow.
    
    for xx in SS do 
        if IsNormal(S,xx) eq false or #xx eq 1 then continue xx; end if;
        Exx:={w:w in Essentials|xx subset w};
        if #Exx ne 0 then 
            MakeAutos(xx);
            Axx:= sub<xx`autogrp|AutYX(Normalizer(B,xx),xx)>;
            for yy in Exx do
                Oxx,xxStab := AutOrbit(yy, xx,AutF[yy]);
                Axx:= sub<xx`autogrp|Axx,Generators(xxStab)>;
            end for;
            if ZZ!(#Axx/#AutYX(S,xx)) mod p eq 0 then Bob:= true; break xx; end if;
        end if;
    end for;
   if Bob then continue; end if;//continues while
   Bob:= false;
     
//    

  
    N:= {1..#Essentials}; 
	NN:= Subsets(N);
	NN:= Setseq(NN);
	RO:=[#x:x in NN];
    	ParallelSort(~RO,~NN);
	NN:= Reverse(NN);
        
		for sNN in NN do
                    if #sNN eq 0 or #sNN eq #Essentials then continue sNN; end if;
                    Es:=[Essentials[ww]: ww in sNN];Append(~Es,S);
                    AutE:= [Autos[ww+1]:ww in sNN];Append(~AutE,AutF[S]);
                    Cor,AutCor:= AutFCore(Es,AutE);
                    n:=ZZ!(#AutCor/#AutYX(S,Cor));
                    if n mod p eq 0 then  Bob:=true; break sNN; end if;///Tests if Aut_S(x) a sylow p of AutCore.
        end for;//sNN
           
           if Bob then continue; end if;//continues while
            Bob:=false;
           
           
           
//We now create the fusion system. We don't use the standard call as we have already done most of the calculation



bounds:=[8,6,6,6];
primes:=[2,3,4,4]; 
///Puts the essentials in the standard order using group names.  
//This will break if order of S is too big. Hence the else below
 
if p in primes and #S le p^bounds[Index(primes,p)]  then  
RO:=[IdentifyGroup( Group(x)):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos);
else
RO:=[#Group(x):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos); 
end if; 
    
F:= New(FusionSystem);
F`prime:=p;
F`group:= S;    
F`borel:= B;
F`subgroups:=[x:x in subsBS];
F`essentialautos:= Autos;
F`essentials := [];
for x in Autos do
Append(~F`essentials, Group(x)); end for;
F`AutF:= AssociativeArray(F`subgroups);
for x in F`essentials do 
F`AutF[x] := F`essentialautos[Index(F`essentials,x)]; 
end for; 
       //We only need  to check saturation on centrics. So we make a partial fusion graph.       
if assigned(F`fusiongraph) eq false then  
    F`fusiongraph,F`maps:= FusionGraphSCentrics(F);
end if;
F`classes:= ConnectedComponents(F`fusiongraph);
        
        if assigned(F`centrics) eq false then 
            F`centrics:={x:x in F`subgroups|IsCentric(F,x)}; end if; 

                  for G in FF do 
                          if IsIsomorphic(F,G) then delete F; Bob:= true; break; end if; 
                  end for;
                  if Bob then continue; end if;Bob:=false;
            IS:= IsSaturated(F);
            if Printing then print "Executed saturation test: result is",IS; end if; 
                if assigned(F`essentials) and IS then  
                	if SaveEach then FNumber:= FNumber +1; 
                        SaveAsGo(FNumber, F);   
                	       else    
                        Append(~FF,F);
                    end if; 
                end if; 
 delete F; 
   end while; //  possFSys
 
end for;//ss
end for;//Bor

GG:= FF;
if #FF le 1 then return FF; end if; 
FF:= [FF[1]];
 for i in [2.. #GG] do
 	x:= GG[i];  
 	for y in FF do 
 		if IsIsomorphic(x,y) then continue i; end if;
 	end for; 
 	Append(~FF,x); 
 end for; 
 
return FF;
end intrinsic;

///////////////////////////////////////

intrinsic AllFusionSystems(ordergrp::RngIntElt)-> SeqEnum
{Makes all fusion systems with O_p(F)=1 and O^p(\F)= \F on all groups of order n}
 range:=[1..NumberOfSmallGroups(ordergrp)];
SatFS:=[];
for count in range do 
print "testing group ", count, "of ", NumberOfSmallGroups(ordergrp);
S:= SmallGroup(ordergrp,count);
if IsAbelian(S) eq false then
SatFS := SatFS cat AllFusionSystems(S:SaveEach:=false);
end if;
end for;
return SatFS;
end intrinsic;

///////////////////////////////////////////////////////////

intrinsic AllFusionSystems(ordergrp::RngIntElt, range::SeqEnum:Printing:=false)-> SeqEnum
{Makes all fusion systems with O_p(F)=1 and O^p(\F)= \F on all groups of order n from small groups library in the asserted range}
  
SatFS:=[];
for count in range do 
print "testing group ", count, "of ", NumberOfSmallGroups(ordergrp);
S:= SmallGroup(ordergrp,count);
if IsAbelian(S) eq false then
AA:=AllFusionSystems(S:Printing:=Printing,SaveEach:=false);
if #AA ne 0 then 
 FileName:="F" cat IntegerToString(#S) cat "-" cat IntegerToString(count)cat "-" cat IntegerToString(range[1]) cat "-" cat IntegerToString(range[#range]);
              SaveFS(FileName, AA);
              end if; 

 
end if;
end for;
return SatFS;
end intrinsic;

intrinsic SaveAsGo(  count::RngIntElt, F::FusionSystem)
{}
grp:= #F`group;
bor:= #F`borel;
FileName:="F" cat IntegerToString(grp) cat "-" cat IntegerToString(bor) cat "-" 
cat IntegerToString(count);
              SaveFS(FileName, [F]);
end intrinsic;



intrinsic Centralizer(G::Grp,A::Grp,B:Grp)->Grp
{Return the centralizer in G of the the quotient A/B}
require IsNormal(G,B): "B is not normalized by G"; 
K:= Normalizer(G,A);
 Q,a:= K/B;
C:= Centralizer(Q,a(A));
C:= SubInvMap(a,K,C); 
return C;
end intrinsic;





intrinsic AbelianPearls(S::Grp:fusion:=true)->SeqEnum
{Returns all fusion systems with just abelian Pearls provide anu such exists}
S:= PCGroup(S);

require IsMaximalClass(S): "S does not have maximal class";
p:= FactoredOrder(S)[1][1];
ZZ:= Integers();
 
L:= LowerCentralSeries(S);
gamma1:= Centralizer(S,L[2],L[4]);
Z2:= L[#L-2]; 
SS:= Subgroups(S:OrderEqual:=p^2);
PotPearls:= {x`subgroup: x in SS| Normalizer(S,x`subgroup) eq sub<S|Z2,x`subgroup> and Exponent(x`subgroup) eq p};
if #PotPearls eq 0 then return[]; end if;  
MakeAutos(S);
AutS:= S`autogrp;
AutSp:= S`autoperm;
map:= S`autopermmap;
pVal:= Valuation(#AutSp,p); m:= ZZ!(#AutSp/p^pVal);
BorelsandS:=[];
if m lt p-1 then return[]; end if;
        
PAut, tt:= PCGroup(AutSp); 
H:=HallSubgroup(PAut,-p); 
K:= [wx`subgroup:wx in Subgroups(H)|wx`order ge p-1];


BCand:=[];
for k:= 1 to #K do  
	K1:= K[k]; 
    	for K2 in BCand do 
    		if IsConjugate(PAut,K1,K2) then   continue k;   end if;
    	end for; 
	Append(~BCand,K1); 
end for;
BCand:= [SubInvMap(tt, AutSp, K1):K1 in BCand];
Z:= Centre(S);
MakeAutos(Z);
 
BCand:= [k: k in BCand|#sub<Z`autogrp|Generators(  SubInvMap(map, AutS,k))> eq p-1];





for CC in BCand do
         f:=hom<CC->AutS|g:->Inverse(map) (g)>;
          C:= SubMap(f,AutS,CC);  
          B,phiB:=Holomorph(GrpFP,S, sub<AutS|C>); 
        T:= phiB(S);  
         B, theta := PCGroup(B); T:= theta(T);
        BB:=[B,T];
         for x in PotPearls do Append(~BB,SubMap(phiB*theta,T,x)); end for;
     Append(~BorelsandS,BB);
end for;
        
        AllPearls:=[];
        
for Bor in  BorelsandS  do
	B:= Bor[1];
	S:= Bor[2];
	L:= LowerCentralSeries(S);
	PotPearls:=[Bor[j]: j in [3..#Bor]];   

	PotPearls2:=[];

		for PP in PotPearls do 
			for PP1 in PotPearls2 do
				if IsConjugate(B,PP,PP1) then continue PP; end if;
			end for;
			Append(~PotPearls2, PP); 
		end for;
	PotPearls:= PotPearls2;  

	Pearls:=[B];
	for PP in  PotPearls do 
		N:= Normalizer(B,PP); 
		
		MakeAutos(PP);
		AutN:= AutYX(N,PP);
		SL2:= SubInvMap(PP`autopermmap, PP`autogrp,DerivedSubgroup(PP`autoperm));
		AutSPP:= AutYX(Normalizer(S,PP),PP);
		D:=sub<PP`autogrp|AutN,SL2>;
		 if #Normalizer(SubMap(PP`autopermmap, PP`autoperm,D), SubMap(PP`autopermmap, PP`autoperm,AutSPP)) eq #AutN then
		 Append(~Pearls,PP); end if;
	
	end for;
	if #Pearls ne 1 then Append(~AllPearls,Pearls); end if;
end for;


FusSys:=[];
AutomiserSequences:=[];
for FS in AllPearls do
B:= FS[1]; 
S:= pCore(B,p);
A1:= AutYX(B,S);
AutSeq:=[A1];
	for ii in [2..#FS] do
		Pearl:= FS[ii];
		N:= Normalizer(FS[1],Pearl);
		A2:= AutYX(N,Pearl);
		SL2:= SubInvMap(Pearl`autopermmap, 	Pearl`autogrp,DerivedSubgroup(Pearl`autoperm));
		Append(~AutSeq, sub<Pearl`autogrp| SL2,A2>);
	end for;
	Autos:= AutSeq;

Append(~AutomiserSequences,AutSeq);
if fusion then
	
	Bbar, bar:= B/Centre(S);
	subsBS:= Subgroups(Bbar:OrderDividing:=#bar(S));
	subsBS:= [Inverse(bar)(x`subgroup):x in subsBS];
	 
bounds:=[8,6,6,6];
primes:=[2,3,4,4]; 
///Puts the essentials in the standard order using group names.  
//This will break if order of S is too big. Hence the else below
 
 
 
if p in primes and #S le p^bounds[Index(primes,p)]  then  
RO:=[IdentifyGroup( Group(x)):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos);
else
RO:=[#Group(x):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos); 
end if; 
    
F:= New(FusionSystem);
F`prime:=p;
F`group:= S;    
F`borel:= B;
F`subgroups:=[x:x in subsBS];
F`essentialautos:= Autos;
F`essentials := [];
for x in Autos do
Append(~F`essentials, Group(x)); end for;
F`AutF:= AssociativeArray(F`subgroups);
for x in F`essentials do 
F`AutF[x] := F`essentialautos[Index(F`essentials,x)]; 
end for; 
	
	
	
	
Append(~FusSys,F);
end if;
end for;
if fusion then
if #FusSys eq 0 then return []; end if;
FusSys1:=[FusSys[1]];
for x in FusSys do 
	for y in FusSys1 do
		if IsIsomorphic(x,y) then continue x; end if;
	end for;
	Append(~FusSys1,x); 
end for;

return FusSys;
else return AutomiserSequences;
end if;


end intrinsic;
         
