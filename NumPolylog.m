(* ::Package:: *)

(* basic functions*)
shorthand[vec_]:=Block[{nowm=1,mlist={}},Do[If[mem===0,nowm++;,AppendTo[mlist,nowm];nowm=1;],{mem,vec}];
If[nowm==1,{mlist,#},{Append[mlist,nowm],#}]&@DeleteCases[vec,0]]
longhand[v_,w_]:=Join@@(Append[ConstantArray[0,First[#]],Last[#]]&/@Transpose[{v-1,w}])
(*tailzero[vec_]:=With[{temp=shorthand[vec]},
If[Length[First@temp]>Length[Last@temp],Last[First[temp]]-1,0]]*)
tailzero[list_]:=If[Length[list]>0&&Last[list]===0,tailzero[Most[list]]+1,0]
headone[list_]:=If[Length[list]>0&&First[list]===1,headone[Rest[list]]+1,0]
(*Shuffle[s1_,s2_]:=Block[{p,tp,ord},p=Transpose[Permutations[Join[(1&)/@s1,(0&)/@s2]]];tp=BitXor[p,1];ord=Accumulate[p] p+(Accumulate[tp]+Length[s1]) tp;Transpose[Outer[Part,{Join[s1,s2]},ord,1]\[LeftDoubleBracket]1\[RightDoubleBracket]]]*)
Shufflep[s1_,s2_]:=Block[{p,tp,ord},p=Transpose[Rest@Permutations[Join[(1&)/@s1,(0&)/@s2]]];tp=BitXor[p,1];ord=Accumulate[p] p+(Accumulate[tp]+Length[s1]) tp;Transpose[Outer[Part,{Join[s1,s2]},ord,1][[1]]]]
poorsum[mm_,prezz_,preyy_,prec_]:=With[{zz=N[Rationalize[prezz,0],2prec],yy=N[Rationalize[preyy,0],2prec],bound=Max[250,1.25 * prec/Log[10,Abs[Min[Abs[prezz]]/preyy]]],len=Length[mm]},(-1)^len Last@Fold[Accumulate[#1(Table[(If[#2===1,yy,zz[[#2-1]]]/zz[[#2]])^(j+len-#2)(j+len-#2)^(-mm[[#2]]),{j,bound}])]&,1,Range[Length[mm],1,-1]]]
poorNG[{mm_Integer},{zz_},y_,prec_:50]:=-PolyLog[mm,y/zz]
poorNG[{mm__Integer},{zz__},y_,prec_:50]:=poorsum[{mm},{zz},y,prec]
poorNG[z_List,y_,prec_:50]:=With[{hh=Chop[z]},If[AnyTrue[DeleteCases[hh,0],Abs[y/#]>1&],0,poorNG[Sequence@@(shorthand[hh]),y,prec]]]
(*
(* use Levin's transformation to acc series : not so efficient *)
levincc[j_,k_,n_]:=levincc[j,k,n]=(n+j+1)^(k-1)/(n+k+1)^(k-1)
levintrans[n_,k_,list_,partialsum_]:=Sum[(-1)^j Binomial[k,j]levincc[j,k,n]partialsum[[n+j]]/list[[n+j+1]],{j,0,k}]/Sum[(-1)^j Binomial[k,j]levincc[j,k,n]/list[[n+j+1]],{j,0,k}]
levinsum[mm_,prezz_,preyy_,prec_]:=N[With[{zz=N[Rationalize[prezz,0],5prec],yy=N[Rationalize[preyy,0],5prec],bound=Floor@Max[250,1/2 prec/Log[10,Abs[Min[Abs[prezz]]/preyy]]],len=Length[mm]},-levintrans[Floor[bound]-Floor[2 bound/3]-1,Floor[2bound/3],#[[1]],#[[2]]]&@({#,Accumulate@#}&[Table[(yy/zz[[1]])^(j+len-1)(j+len-1)^(-mm[[1]]),{j,bound}]*Fold[Accumulate[#1(Table[(zz[[#2-1]]/zz[[#2]])^(j+len-#2)(j+len-#2)^(-mm[[#2]]),{j,bound}])]&,1,Range[Length[mm],2,-1]]])],2prec]
(*poorNG[z_List,y_,prec_:50]:=With[{hh=Chop[z]},With[{jj=Min[Abs[DeleteCases[hh,0]/y]],kk=shorthand[hh]},If[Length[kk]<3,poorsum[Sequence@@kk,y,prec],Which[jj<=1,0,jj\[GreaterEqual]1.2,levinsum[Sequence@@kk,y,prec],True,poorsum[Sequence@@kk,y,prec]]]]]*)
*)


(* 
myG is the general structure introduced in the section 5.3 of 0410259 :
    myG[y1,{b1,...,br},{z1,...,zn},y2,k] = int_0^y1 ds1/(s1-b1) ... int_0^s(r-1) dsr/(sr-br) G(z1,...,z(k-1),sr,z(k+1),...,zn;y2),
where k is the position of integral variable. For k=0, there's no integral variable, so
    myG[y1,{b1,...,br},{z1,...,zn},y2,k] = G(b1,...,br;y1)*G(z1,...,zn;y2).
It's clear that
    myG[_,{},{z1,...,zn},y2,0] = G(z1,...,zn;y2).
*)
mylog[1,___]=0;
mylog[x_,0]:=mylog[x];
mylog[x_,-1]:=mylog[x]-2*Pi*I;
mylog[x_,_]:=mylog[x];
myLi[_,0]:=0;
(* all zero, power of log *)
myG[y1_,b_,z_,y2_,0]/;MatchQ[z,{0..}]:=If[b==={},1,myG[0,{},b,y1,0]]mylog[y2]^Length[z]/Length[z]!;
(* ini : be careful First Position*)
myG[y1_,b_,z_,y_,0]/;(Last[z]=!=0):=(If[b==={},1,myG[0,{},b,y1,0]]*If[!AnyTrue[DeleteCases[z,0],Abs[#]<Abs[y]&],goodG[z/y,1],With[{pos=First@First@Position[Abs[z],Min[Abs@DeleteCases[Rationalize[z,0],0]],1]},myG[z[[pos]],{},ReplacePart[z,pos->0],y,pos]]])
(* remove tail zero *)
myG[y1_,b_,{zz___,0},y2_,w_]/;(w=!=Length[{zz,0}]):=(myG[y1,b,{zz,0},y2,w]=Expand[With[{z={zz,0}},With[{kk=If[Length[z]-#<w,Length[z]-w,#]&@tailzero[z],len=Length[z]},1/kk (If[y2===1,0,mylog[y2]myG[y1,b,{zz},y2,w]]-Sum[myG[y1,b,Join[z[[1;;m]],{0},z[[m+1;;len-kk-1]],{z[[len-kk]]},ConstantArray[0,kk-1]],y2,If[w!=0&&m<w,w+1,w]],{m,0,len-kk-1}])]]])
(* special values, assuming dG[1]=log[0]\[Rule]0*)
(* almost all zero, Li *)
myG[y1_,b_,z_,y_,0]/;MatchQ[Most[z],{0..}]:=-If[b==={},1,myG[0,{},b,y1,0]]*myLi[Length[z],y/Last[z]];
myG[y1_,b_,{z_},y_,0]:=If[b==={},1,goodG[b,y1]]*If[y===z,0,mylog[(-y+z)/z]];
myG[y1_,b_,{z1_,z2_},y_,0]/;(z2=!=0):=If[z1===y,-myG[y1,b,{z2,z1},y,0],If[b=={},1,goodG[b,y1]]*(-myLi[2,y/(y-z1)]-myLi[2,y/z2]+myLi[2,y (z1-z2)/((-y+z1) z2)])]
(* tail integral var *)
branchmyG[a_,b_,z_,y_,w_,branch_]/;(MatchQ[z,{0..}]&&w===Length[z]):=branchmyG[a,b,z,y,w,branch]=Expand@If[Length[z]===w===1,branchmyG[0,{},Append[b,y],a,0,branch]+mylog[-y,branch]If[b=={},1,branchmyG[0,{},b,a,0,branch]]-branchmyG[0,{},Append[b,0],a,0,branch],If[b=={},1,branchmyG[0,{},b,a,0,branch]](-myzeta[w]+branchmyG[y,{0},ConstantArray[0,w-1],y,w-1,branch])-branchmyG[a,Append[b,0],ConstantArray[0,w-1],y,w-1,branch]]
myG[a_,b_,z_,y_,w_]/;(MatchQ[z,{0..}]&&w===Length[z]):=branchmyG[a,b,z,y,w,Sign[Im[a]]]/.branchmyG[p__,q_]:>myG[p]
myG[y1_,b_,z_,y2_,w_]/;((!MatchQ[z,{0..}])&&w===Length[z]):=(myG[y1,b,z,y2,w]=Expand@With[{tz=tailzero[z]},(myG[0,{},z[[;;w-tz]],y2,0]myG[y1,b,ConstantArray[0,tz],y2,tz])-Total[myG[y1,b,(#/.Infinity->0),y2,First[FirstPosition[#,Infinity]]]&/@Shufflep[z[[;;w-tz]],longhand[{tz},{Infinity}]]]])
(* integral var in other pos *)
myG[y1_,b_,z_,y2_,w_]/;(w!=0&&w!=Length[z]):=(myG[y1,b,z,y2,w]=If[w===1,myG[y1,b,z,y2,0]+myG[y1,Append[b,y2],Delete[z,w],y2,0]+myG[y1,Append[b,z[[w+1]]],Delete[z,w+1],y2,w]-myG[y1,Append[b,z[[w+1]]],Delete[z,w],y2,0],myG[y1,b,z,y2,0]-myG[y1,Append[b,z[[w-1]]],Delete[z,w-1],y2,w-1]+myG[y1,Append[b,z[[w-1]]],Delete[z,w],y2,0]+myG[y1,Append[b,z[[w+1]]],Delete[z,w+1],y2,w]-myG[y1,Append[b,z[[w+1]]],Delete[z,w],y2,0]])
(* goodG, G functions which can be evaluated by series expansion, assuming dG[1]=log[0]\[Rule]0 *)
goodG[z_,y_]:=goodG[z/y];
(*goodG[z_,1]:=With[{kk=headone[z],len=Length[z]},If[len==1,dG[1],1/kk (dG[1]goodG[Rest[z],1]-Sum[goodG[Join[ConstantArray[1,kk-1],z[[kk+1;;m]],{1},z[[m+1;;]]],1],{m,kk+1,len}])]]/;First[z]===1;*)
goodG[z_]/;(First[z]===1):=With[{kk=headone[z],len=Length[z]},If[len==1,0,1/kk (-Sum[goodG[Join[ConstantArray[1,kk-1],z[[kk+1;;m]],{1},z[[m+1;;]]]],{m,kk+1,len}])]];
goodG[z_]/;(MatchQ[Most[z],{0..}]&&Last[z]=!=0):=-myLi[Length[z],1/Last[z]];
(* acc G, use Hölder convolution to accelerate convergence *)
accG[{z_},prec_:50]:=mylog[(-1+z)/z];
accG[{z1_,z2_},prec_:50]:=-myLi[2,1/(1-z1)]-myLi[2,1/z2]+myLi[2,(z1-z2)/((-1+z1) z2)];
accG[hh_,prec_:50]:=accG[hh,prec]=With[{z=Rationalize[hh,0]},If[AnyTrue[DeleteCases[z,0],Abs[#]<=1.05&],accG[2z,prec]+(-1)^Length[z]accG[2(1-Reverse[z]),prec]+Sum[(-1)^j accG[2(1-Reverse[z[[1;;j]]]),prec]accG[2z[[j+1;;]],prec],{j,1,Length[z]-1}],poorNG[z,1,prec]]];
numG[z_,y2_,prec_:50]:=N[Log[y2]^Length[z]/Length[z]!,prec+10]/;MatchQ[z,{0..}];
(* remove tail zero *)
numG[{zz___,0},y2_,prec_:50]:=N[Expand[With[{z={zz,0}},With[{kk=tailzero[z],len=Length[z]},1/kk (If[y2===1,0,Log[y2]numG[{zz},y2,prec]]-Sum[numG[Join[z[[1;;m]],{0},z[[m+1;;len-kk-1]],{z[[len-kk]]},ConstantArray[0,kk-1]],y2,prec],{m,0,len-kk-1}])]]],prec+10]
numG[z_,y_,prec_:50]/;(Last[z]!=0):=N[If[Rationalize[First[z]/y,0]===1,ComplexInfinity,myG[0,{},Rationalize[z/y,0],1,0]/.goodG[x_]:>goodG[Rationalize[x,0]]//.{goodG[x_]:>accG[x,prec],myLi->PolyLog,mylog->Log,myzeta->Zeta}],prec+10]
numLi[m_,x_,prec_:50]:=(-1)^Length[m]numG[longhand[m,Rest[FoldList[#1/#2&,1,x]]],1,prec]
numMZV[m_,prec_:50]:=numLi[m,ConstantArray[1,Length[m]],prec]

(*
TODO : Be careful!!!! Check!!!! Rename functions!!!
*)

(* 
add the support of 1d integral of G functions, based on the Newton-Leibniz formula :

Suppose we have a function G({a1(t),...,an(t)},z), we want to rewrite it into a sum of 
constants and G functions with the from
    G({b1,...,bn},t),
where bi is free of t. Then we can calcluate the 1d integral 
    int dt/(t-b0) G({a1(t),...,an(t)},z).

This reduction can be done if z-a1, ai-ai+1, an, an-z are all linear reducible in t,
i.e. they are products of linear functions of t. The algorithm is based on the 
Newton-Leibniz formula
    G({a1(t),...,an(t)},z) = G({a1(0),...,an(0)},z) + int_0^t dt1 partial_t1 
                                                            G({a1(t1),...,an(t1)},z)
and (from the definition of G function)
    dt1 partial_t1 G({a1(t1),...,an(t1)},z) 
                                    = dlog(z-a1)G({a2,...,an},z)+...+
                                      dlog(ai-ai+1)G({a1,...,\hat{ai+1},...,an},z)-
                                      dlog(ai-ai+1)G({a1,...,\hat{ai},...,an},z)+...+
                                      -dlog(an)G({a1,...,an-1},z),
Finally, we reduce it to 
    G({an},z) = log(1-z/an) = log(c) + sum_i n_i log(1-t/c_i) 
                            = log(c) + sum_i n_i G(ci,t), ...................... (1)
and then we can calculate all remaining integral 
    int dlog(t1-b1)dlog(t2-b1)...dlog(t(n-1)-b(n-1))G(ci,t) = G({b1,...,b(n-1),ci},t)
from the definition of G function. 

However, eq.(1) usually depands on the branch you choice, otherwise we can only get a 
funtion with the same symbol. The other steps are all algebraic, so if (1) is correct 
(on a given region), the whole reduction is correct (on the given region). In our 
realization, one could add a optional  function to support numerical checks of eq.(1) 
in the recursion, otherwise it will not check (1).
*)

(* islinearreducible[rationalfunc_, var_] := 
 With[{hh = FactorList[rationalfunc]}, {#, If[#, hh, {}]} &[
   NoneTrue[First /@ hh, D[#, {var, 2}] =!= 0 &]]]
ddG[y_, z_, var_] := If[Length[y] === 1, dlog[] G[y, z],
   -dlog[Last[y]] G[Most[y], z] + dlog[z - First[y]] G[Rest[y], z] + 
    Sum[dlog[
       y[[i]] - y[[i + 1]]] (G[Delete[y, i + 1], z] - 
        G[Delete[y, i], z]), {i, 1, Length[y] - 1}]] /. 
  dlog[x__] :> 0 /; FreeQ[{x}, var]
initGmove[G[x_, z_], var_, numerfunc_ : Identity] := 
 ordGmove[dlog[{}] G[x, z], var, numerfunc] /. 
  G[{}, _] -> 1 /; FreeQ[z, var]
ordGmove::notlinearred = "`1` is not linear reducible!";
ordGmove[a_ + b_, var_, numerfunc_ : Identity] := 
 ordGmove[a, var] + ordGmove[b, var]
ordGmove[a_ c_, var_, numerfunc_ : Identity] := 
 c ordGmove[a, var] /; FreeQ[c, G | dlog | var]
ordGmove[dlog[list_List] G[x_, z_], var_, numerfunc_ : Identity] := 
 If[Length[x] > 1, 
  Expand[G[list, var] G[x /. var -> 0, z] + 
      dlog[
        list] (ddG[x, z, var] /. 
           dlog[kk_] :> 
            Total[#[[2]] dlog[#[[1]]] & /@ (If[First@#, Last@#, 
                  Message[ordGmove::notlinearred, kk]; Abort[];] &@
                islinearreducible[kk, var])] /. 
          dlog[kk_] :> 0 /; FreeQ[kk, var] /. 
         dlog[a_. var + b_.] :> dlog[var + b/a])] /. 
    dlog[ll_List] dlog[var + kk_.] :> dlog[Append[ll, -kk]] /. 
   dlog[kk_List] G[xx_, zz_] :> 
    ordGmove[dlog[kk] G[xx, zz], var, numerfunc],
  lastGmove[dlog[list] G[x, z], var, numerfunc]
  ]
lastGmove[a_ + b_, var_, numerfunc_ : Identity] := 
 lastGmove[a, var, numerfunc] + lastGmove[b, var, numerfunc]
lastGmove[a_ c_, var_, numerfunc_ : Identity] := 
 c lastGmove[a, var, numerfunc] /; FreeQ[c, G | dlog | var]
lastGmove[dlog[list_List] G[{x_}, z_], var_, numerfunc_ : Identity] :=
  With[{hh = islinearreducible[1 - z/x, var]}, 
   If[hh[[1]], (Expand[
        dlog[list] ((If[numerfunc === Identity, 0, 
               Rationalize[
                 numerfunc[G[{x}, z] - #]/
                  Pi] Pi] + #) &@(Total[#[[2]] mylog[#[[1]]] & /@ 
                 hh[[2]]] /. 
               mylog[aa_] :> 
                With[{jj = CoefficientList[aa, var]}, 
                  If[First[jj] === 0, mylog[jj[[2]]] + G[{0}, var], 
                   mylog[jj[[1]]] + G[{-jj[[1]]/jj[[2]]}, var]]] /; ! 
                  FreeQ[{aa}, var] //. {mylog[a_] + mylog[b_] :> 
                mylog[Expand[a b]], 
               mylog[a_] - mylog[b_] :> mylog[Expand[a/b]], 
               mylog[1 - b_/a_] :> G[{a}, b]} /. 
             mylog[a_] :> mylog[Simplify[a]]))] /. 
       dlog[pp_List] G[qq_, var] :> G[Join[pp, qq], var] /. 
      dlog[pp_List] :> G[pp, var]), 
    Message[ordGmove::notlinearred, kk]; Abort[];]] /. {mylog[-1] -> 
    I Pi, G[{}, _] :> 1}
GIntegrate[dlog[x_] G[y_, var_], {var_, a_, b_}] := 
 With[{hh = islinearreducible[x, var]}, 
  If[First[hh], 
   Expand[(Total[#[[2]] dlog[#[[1]]] & /@ Last[hh]] /. 
         dlog[xx_] :> 0 /; FreeQ[xx, var] /. 
        dlog[aa_. var + bb_.] :> dlog[var + bb/aa]) G[y, var]] /. 
    dlog[var + aa_.] G[y, var] :> 
     G[Prepend[y, -aa], b] - G[Prepend[y, -aa], a], 
   Message[ordGmove::notlinearred, x];]] *)