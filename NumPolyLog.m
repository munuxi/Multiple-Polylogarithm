(* ::Package:: *)

(* basic functions*)
shorthand[vec_]:=Block[{nowm=1,mlist={}},Do[If[mem===0,nowm++;,AppendTo[mlist,nowm];nowm=1;],{mem,vec}];If[nowm==1,{mlist,#},{Append[mlist,nowm],#}]&@DeleteCases[vec,0]]
longhand[v_,w_]:=Join@@(Append[ConstantArray[0,First[#]],Last[#]]&/@Transpose[{v-1,w}])
readfirstnotinpos[list_,sublist_,direction_]:=Which[direction===1,If[Length[list]>0&&MemberQ[sublist,First[list]],readfirstnotinpos[Rest[list],sublist,direction]+1,0],direction===-1,If[Length[list]>0&&MemberQ[sublist,Last[list]],readfirstnotinpos[Most[list],sublist,direction]+1,0],True,0]
tailzero[list_]:=readfirstnotinpos[list,{0},-1]
headone[list_]:=readfirstnotinpos[list,{1},1]
Shuffle[{},{}]:={}
Shuffle[s1_,s2_]:=Block[{p,tp,ord},p=Transpose[Permutations[Join[(1&)/@s1,(0&)/@s2]]];tp=BitXor[p,1];ord=Accumulate[p] p+(Accumulate[tp]+Length[s1]) tp;Transpose[Outer[Part,{Join[s1,s2]},ord,1][[1]]]]
Shufflep[_,{}]:={}
Shufflep[{},_]:={}
Shufflep[s1_,s2_]:=Block[{p,tp,ord},p=Transpose[Rest@Permutations[Join[(1&)/@s1,(0&)/@s2]]];tp=BitXor[p,1];ord=Accumulate[p] p+(Accumulate[tp]+Length[s1]) tp;Transpose[Outer[Part,{Join[s1,s2]},ord,1][[1]]]]
minideg[f_,var_]:=minideg[f,var]=If[FreeQ[f,var],0,If[Limit[f,var->0]===0,minideg[f/var,var]+1,0]];
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
myG[y1_,b_,{0..},0,0]:=ComplexInfinity
myG[y1_,b_,z_,0,0]/;!MatchQ[z,{0..}]:=0
(* ini : be careful FirstPosition*)
myG[y1_,b_,z_,y_,0]/;(Last[z]=!=0):=(If[b==={},1,myG[0,{},b,y1,0]]*If[!AnyTrue[DeleteCases[z,0],Abs[#]<Abs[y]&],goodG[z/y,1],With[{pos=First@First@Position[Abs[Chop[z]],Min[Abs@DeleteCases[Chop[z],0]],1]},myG[z[[pos]],{},ReplacePart[z,pos->0],y,pos]]])
(* remove tail zero *)
myG[y1_,b_,{zz___,0},y2_,w_]/;(w=!=Length[{zz,0}]):=(myG[y1,b,{zz,0},y2,w]=Expand[With[{z={zz,0}},With[{kk=If[Length[z]-#<w,Length[z]-w,#]&@tailzero[z],len=Length[z]},1/kk (If[y2===1,0,mylog[y2]myG[y1,b,{zz},y2,w]]-Sum[myG[y1,b,Join[z[[1;;m]],{0},z[[m+1;;len-kk-1]],{z[[len-kk]]},ConstantArray[0,kk-1]],y2,If[w!=0&&m<w,w+1,w]],{m,0,len-kk-1}])]]])
(* special values, assuming dG[1]=log[0]->0*)
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
(* goodG, G functions which can be evaluated by series expansion, assuming dG[1]=log[0]->0 *)
goodG[z_,y_]:=If[y===0,0,goodG[z/y]];
(*goodG[z_,1]:=With[{kk=headone[z],len=Length[z]},If[len==1,dG[1],1/kk (dG[1]goodG[Rest[z],1]-Sum[goodG[Join[ConstantArray[1,kk-1],z[[kk+1;;m]],{1},z[[m+1;;]]],1],{m,kk+1,len}])]]/;First[z]===1;*)
goodG[z_]/;(First[z]===1):=With[{kk=headone[z],len=Length[z]},If[len==1,0,1/kk (-Sum[goodG[Join[ConstantArray[1,kk-1],z[[kk+1;;m]],{1},z[[m+1;;]]]],{m,kk+1,len}])]];
goodG[z_]/;(MatchQ[Most[z],{0..}]&&Last[z]=!=0):=-myLi[Length[z],1/Last[z]];
(* acc G, use Hölder convolution to accelerate convergence *)
accG[{z_},prec_:50]:=mylog[(-1+z)/z];
accG[{z1_,z2_},prec_:50]:=-myLi[2,1/(1-z1)]-myLi[2,1/z2]+myLi[2,(z1-z2)/((-1+z1) z2)];
accG[hh_,prec_:50]:=accG[hh,prec]=With[{z=Rationalize[hh,0]},If[AnyTrue[DeleteCases[z,0],Abs[#]<=1.05&],accG[2z,prec]+(-1)^Length[z]accG[2(1-Reverse[z]),prec]+Sum[(-1)^j accG[2(1-Reverse[z[[1;;j]]]),prec]accG[2z[[j+1;;]],prec],{j,1,Length[z]-1}],poorNG[z,1,prec]]];
numG[z_,0,prec_:50]/;(!MatchQ[z,{0..}]):=0
numG[{0..},0,prec_:50]:=ComplexInfinity
numG[z_,y2_,prec_:50]/;MatchQ[z,{0..}]&&(y2=!=0):=N[Log[y2]^Length[z]/Length[z]!,prec+10];
(* remove tail zero *)
numG[{zz___,0},y2_,prec_:50]/;(y2=!=0):=N[Expand[With[{z={zz,0}},With[{kk=tailzero[z],len=Length[z]},1/kk (If[y2===1,0,Log[y2]numG[{zz},y2,prec]]-Sum[numG[Join[z[[1;;m]],{0},z[[m+1;;len-kk-1]],{z[[len-kk]]},ConstantArray[0,kk-1]],y2,prec],{m,0,len-kk-1}])]]],prec+10]
numG[z_,y_,prec_:50]/;(Last[z]!=0):=N[If[Rationalize[First[z]/y,0]===1,ComplexInfinity,myG[0,{},Rationalize[z/y,0],1,0]/.goodG[x_]:>goodG[Rationalize[x,0]]//.{goodG[x_]:>accG[x,prec],myLi->PolyLog,mylog->Log,myzeta->Zeta}],prec+10]
numLi[m_,x_,prec_:50]:=(-1)^Length[m]numG[longhand[m,Rest[FoldList[#1/#2&,1,x]]],1,prec]
numMZV[m_,prec_:50]:=numLi[m,ConstantArray[1,Length[m]],prec]


(*
TODO : Be careful!!!! Check!!!! Rename functions!!! 
       Add the suppout of integrals on (0,infty).
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

However, G({a1(0),...,an(0)},z) usually diverges when a1(0)=1 or an(0)=0, we use the 
shuffle regularization used in [1403.3385] to get the finite result. On the other hand,
eq.(1) usually depands on the branch you choice, otherwise we can only get a 
funtion with the same symbol. The other steps are all algebraic, so if (1) is correct 
(on a given region), the whole reduction is correct (on the given region). In our 
realization, one could add fitting values to support numerical checks of eq.(1) 
in the recursion, otherwise it will not check (1).
*)


Off[N::meprec]

(* shuffle regularization *)

regwordbelow[word_myword, removelist_] := 
 With[{hh = readfirstnotinpos[List @@ word, removelist, -1]}, Which[
   hh === 0, word,
   Length[word] === hh, 0,
   True, (-1)^hh Total[
     myword @@@ (Append[#, word[[-hh - 1]]] & /@ 
        Shuffle[List @@ word[[;; -hh - 2]], 
         Reverse[List @@ word[[-hh ;;]]]])]]]

regwordabove[word_myword, removelist_] :=
 If[removelist === Infinity,
  Sum[(-1)^(k - 1) With[{jj = 
       If[# === {}, myword[], Total[myword @@@ #]] &@(Shuffle[
          ConstantArray[-1, 
           k - 1], (List @@ word)[[k + 1 ;;]]])}, (jj /. 
        myword[x___] :> myword[word[[k]], x]) - (jj /. 
        myword[x___] :> myword[-1, x])], {k, 1, Length@word}]
  , With[{hh = readfirstnotinpos[List @@ word, removelist, 1]},
   Which[hh === 0, word,
    Length[word] === hh, 0,
    True, (-1)^hh Total[
      myword @@@ (Prepend[#, word[[hh + 1]]] & /@ 
         Shuffle[List @@ word[[hh + 2 ;;]], 
          Reverse[List @@ word[[;; hh]]]])]]]]

regword[word_myword, above_, below_] := 
  regwordbelow[word, below] /. aaa_myword :> regwordabove[aaa, above];

(* 
use a special Möbius transformation z/(1+z) to convert
G({a1,...,an},infty) to G({...},1)'s.
*)

prespecialmobiustrans[
  x_myword] := (If[# === -1, 0, myword[#/(1 + #)]] - myword[1] & /@ 
    x) //. {myword[y___, myword[p_] + q_, w___] :> 
    myword[y, p, w] + myword[y, q, w], 
   myword[y___, -myword[p_], w___] :> -myword[y, p, w]}

specialmobiustrans[x_myword] := 
  regword[x, Infinity, {0}] /. myword[y__] :> prespecialmobiustrans[myword[y]] /. 
   myword[yy__] :> G[Simplify /@ {yy}, 1];

(*
We will face two kinds of divergance (t>0, t->0), 
    G({a1 t^k1,...,an t^kn},1) and G({1-b1 t^l1,...,1-bn t^ln},1).
They can be related by the identity 
    G({1-c1,...,1-cn},1) = (-1)^n G({cn,...,c1},1),
however, when 0 <= ci <= 1, one should revert the branch.
*)

(* from -ie -> +ie *)
revertallbranchG[z_, y_, FitValues_ : {}] := Which[
  MatchQ[Last /@ z, {1 ..}], G[First /@ z, y],
  y === 0, 0,
  z === {}, 1,
  Last@First[z] === 1,
  With[{hh = headone[Last /@ z]},
   G[First /@ z[[;; hh]], y] revertallbranchG[z[[hh + 1 ;;]], y, 
      FitValues]
    - Total[
     revertallbranchG[#, y, FitValues] & /@ 
      Shufflep[z[[;; hh]], z[[hh + 1 ;;]]]]],
  Last@First[z] === -1,
  revertallbranchG[Prepend[Rest[z], {First@First[z], 1}], y, FitValues]
   - (* if +ie -> -ie, plus here *)
   If[Variables[{z, y} /. FitValues] === {} && 
     Element[First@First[z] /. FitValues, Reals] && 
     If[y === Infinity, (First@First[z] /. FitValues) >= 
       0, ((0 <= First@First[z]/y <= 1) /. FitValues)], 
    If[(First@First[z] /. FitValues) === 
        0 || (First@First[z] === y /. FitValues), Pi I, 
      2 Pi I] revertallbranchG[Rest[z], First@First[z], FitValues], 0]
  ]

preregGinf[z_] := If[z === 0, 0,
  If[Last[z] === {0, 0}, 
   regwordbelow[myword @@ z, {{0, 0}}] /. 
    myword[x___] :> preregGinf[{x}], 
   With[{revminpos = 
      First@FirstPosition[Reverse[First /@ z], 
        Min[First /@ DeleteCases[z, {0, 0}]]]}, 
    If[revminpos === 1, 
     G[((If[First[#] > 0, 0, Last[#]] & /@ 
         Transpose[{(First /@ z - First@Last[z]), Last /@ z}])), 
      Infinity], 
     preregGinf[z[[;; -revminpos]]] preregGinf[
        z[[-revminpos + 1 ;;]]] - 
      Total[preregGinf[#] & /@ 
        Shufflep[z[[;; -revminpos]], z[[-revminpos + 1 ;;]]]]]]]]

regGinf[G[z_, Infinity]] := specialmobiustrans[myword @@ z]

regGallnear0[z_] := 
 preregGinf[z] /. G[zz_, Infinity] :> regGinf[G[zz, Infinity]]

regGallnear1[z_, FitValues_ : {}] :=
 (-1)^Length[z] preregGinf[Reverse@z] /. {G[zz_, y_] :> 
     revertallbranchG[(Table[
          If[i =!= Length[#] && #[[i]] === 0, {#[[i]], 
            1}, {#[[i]], -1}], {i, Length@#}] &@(zz)), y, 
      FitValues]} /. G[zz_, Infinity] :> regGinf[G[zz, Infinity]]

normGvar0[z_, var_, FitValues_ : {}] :=
 With[{nonvarFitValues = DeleteCases[FitValues, var -> _]},
  Which[
   z === {}, 1,
   AnyTrue[DeleteCases[z /. nonvarFitValues, 0], 
    Limit[1/#, var -> 0] === 0 &], 0,
   Last[z] === 0,
   Expand[
    With[{kk = tailzero[z], len = Length[z]}, 
     1/kk (-Sum[
         normGvar0[
          Join[z[[1 ;; m]], {0}, 
           z[[m + 1 ;; len - kk - 1]], {z[[len - kk]]}, 
           ConstantArray[0, kk - 1]], var, FitValues], {m, 0, 
          len - kk - 1}])]],
   First[z] === 1,
   Expand[
    With[{kk = headone[z], len = Length[z]}, 
     If[len == 1, 0, 
      1/kk (-Sum[
          normGvar0[
           Join[ConstantArray[1, kk - 1], z[[kk + 1 ;; m]], {1}, 
            z[[m + 1 ;;]]], var, FitValues], {m, kk + 1, len}])]]],
   Limit[First[z] /. nonvarFitValues, var -> 0] =!= 1 && 
    Limit[Last[z] /. nonvarFitValues, var -> 0] =!= 0, 
   G[z, 1] /. var -> 0,
   Limit[First[z] /. nonvarFitValues, var -> 0] === 1,
   With[{hh = headone[z /. nonvarFitValues /. var -> 0]}, 
    With[
      {kk = regGallnear1[Function[deg, 
            If[deg === 0, {0, 1 - # /. var -> 0}, {deg, 
              SeriesCoefficient[1 - #, {var, 0, deg}]}]][
           minideg[1 - # /. nonvarFitValues, var]] & /@ z[[;; hh]], 
        FitValues]}, 
     kk normGvar0[z[[hh + 1 ;;]], var, FitValues] - 
      Total[(normGvar0[#, var, FitValues] & /@ 
         Shufflep[z[[;; hh]], z[[hh + 1 ;;]]])]
     ]],
   Limit[Last[z] /. nonvarFitValues, var -> 0] === 0,
   With[{hh = tailzero[z /. nonvarFitValues /. var -> 0]},
    With[{kk = 
       regGallnear0[
        Function[deg, 
            If[deg === 0, {0, # /. var -> 0}, {deg, 
              SeriesCoefficient[#, {var, 0, deg}]}]][
           minideg[# /. nonvarFitValues, var]] & /@ z[[-hh ;;]]]}, 
     kk normGvar0[z[[;; -hh - 1]], var, FitValues] - 
      Total[(normGvar0[#, var, FitValues] & /@ 
         Shufflep[z[[;; -hh - 1]], z[[-hh ;;]]])]
     ]]
   ]]

(* Newton-Leibniz reduction *)

islinearreducible[rationalfunc_, var_] := 
 With[{hh = 
     Rationalize@FactorList[rationalfunc]}, {#, If[#, hh, {}]} &[
    NoneTrue[First /@ hh, D[#, {var, 2}] =!= 0 &]]] /; FreeQ[{x}, var]

linearfactorize[func_, var_] := 
 With[{hh = FactorList[func]}, 
  Total[#[[2]] mylog[#[[1]]] & /@ hh] /. 
    mylog[x_] /; ! FreeQ[x, var] && 
       x =!= var :> (mylog[var D[x, var]/(x /. var -> 0) + 1] + 
       mylog[(x /. var -> 0)]) //. {mylog[aa_] bb_Integer /; 
      FreeQ[aa, var] :> mylog[aa^bb], 
    mylog[aa_] + mylog[bb_] /; FreeQ[{aa, bb}, var] :> mylog[aa bb], 
    mylog[aa_] - mylog[bb_] /; FreeQ[{aa, bb}, var] :> mylog[aa/bb]}]

ddG[y_, z_, var_] := If[Length[y] === 1, dlog[] G[y, z],
   -dlog[Last[y]] G[Most[y], z] + dlog[z - First[y]] G[Rest[y], z] + 
    Sum[dlog[
       y[[i]] - y[[i + 1]]] (G[Delete[y, i + 1], z] - 
        G[Delete[y, i], z]), {i, 1, Length[y] - 1}]] /. 
  dlog[x__] :> 0 /; FreeQ[{x}, var]

myGmoveG[G[x_, z_], var_, FitValues_ : {}] /; FreeQ[z, var] := 
 myGmoveG[G[x, z], var, 
   FitValues] = (Expand[
     Which[FreeQ[{x, z}, var], G[x, z], Length[x] === 1, 
      myGlastGmove[G[x, z], var, FitValues], Length[x] > 1, 
      normGvar0[x/z, var, FitValues] + 
         Expand[ddG[x, z, var] /. 
              dlog[kk_] :> 
               Total[(#1[[2]] dlog[#1[[1]]] &) /@ (If[First[#1], 
                    Last[#1], Message[myGmoveG::notlinearred, kk];
                    Abort[];] &)[islinearreducible[kk, var]]] /. 
             dlog[kk_] :> 0 /; FreeQ[kk, var] /. 
            dlog[xx_] /; ! FreeQ[xx, var] :> 
             dlog[var + (xx /. var -> 0)/D[xx, var]] /. 
           G[xx__] :> myGmoveG[G[xx], var, FitValues]] //. 
        dlog[var + aa_.] G[xx_, var] :> G[Prepend[xx, -aa], var] //. 
       dlog[var + aa_.] :> G[{-aa}, var]]] /. 
    G[{1, xx___}, 
      1] :> (regwordabove[myword[1, xx], {1}] /. 
       myword[zz__] :> G[{zz}, 1]))

myGlastGmove[G[{x_}, z_], var_, FitValues_ : {}] := 
 If[FreeQ[x, var], G[{x}, z], 
   With[{hh = islinearreducible[1 - z/x, var]}, 
    If[hh[[1]], 
     With[{jj = 
        Expand[linearfactorize[1 - z/x, 
           var] //. {mylog[aa_ + bb_. var] :> 
            G[{-(aa/bb)}, var] + mylog[aa], 
           mylog[var] -> G[{0}, var]}]}, 
      If[Variables[z/x //. FitValues] =!= {}, jj, 
         jj - Rationalize[
          N[(jj - Log[1 - z/x])/(Pi I) //. {G[{0}, yy_] :> Log[yy],
               G[{aa_}, yy_] /; aa =!= 0 :> Log[1 - yy/aa], 
              mylog -> Log} //. Rationalize[FitValues, 0], 1000], 
          0] (Pi I)]], Message[myGmoveG::notlinearred, 1 - z/x]; 
     Abort[];]]] /. {G[{}, _] :> 1, mylog[-1] -> Pi I}
myGmoveG::notlinearred = "`1` is not linear reducible!";

movevar=myGmoveG;

movevarall[x_, var_, FitValues_ : {}] := 
 Expand[x /. 
     G[_, 0] :> 
      0 //. {G[xx_, y_] /; ((! FreeQ[xx, var]) && FreeQ[y, var]) :> 
      movevar[G[xx, y], var, FitValues], 
      G[z_,y_]/;!MatchQ[z,{0..}]&&Last[z]===0&&(! FreeQ[y, var])&&y=!=var:> Expand[
    With[{kk = tailzero[z], len = Length[z]}, 
     1/kk (G[{0},y] G[Most[z],y] - Sum[
         G[
          Join[z[[1 ;; m]], {0}, 
           z[[m + 1 ;; len - kk - 1]], {z[[len - kk]]}, 
           ConstantArray[0, kk - 1]], y], {m, 0, 
          len - kk - 1}])]],
     G[xx_, y_] /; (Last[xx]=!=0&&(! FreeQ[xx, var]) && ((! FreeQ[y, var]) || (! 
            FreeQ[y, var] && y =!= var))) :> 
      movevar[G[xx/y, 1], var, FitValues],
      G[xx_,y_]/;MatchQ[xx,{0..}]&&!FreeQ[y,var]&&y=!=var:>
      (Length[xx]!)^(-1)(G[{1/(1-y)},1])^Length[xx]
      }] /. mylog -> Log

preautoGint[x_, var_, FitValues_ : {}] := 
 FixedPoint[
  Expand[# //. 
     G[xx_, var] G[yy_, var] :> 
      Total[G[#, var] & /@ Shuffle[xx, yy]]] &, 
  movevarall[x, var, FitValues]]

GIntegrate::notlinearred = "`1` is not linear reducible!";
preGIntegrate[x_, var_] /; FreeQ[x, var] := x var
preGIntegrate[c_ x_, var_] /; FreeQ[c, var] := c preGIntegrate[x, var]
preGIntegrate[x_ + y_, var_] := 
 preGIntegrate[x, var] + preGIntegrate[y, var]
preGIntegrate[dlog[x_] G[y_, var_], var_] := 
 With[{hh = islinearreducible[x, var]}, 
  If[First[hh], 
   Expand[(Total[#[[2]] dlog[#[[1]]] & /@ Last[hh]] /. 
         dlog[xx_] :> 0 /; FreeQ[xx, var] /. 
        dlog[aa_. var + bb_.] :> dlog[var + bb/aa]) G[y, var]] /. 
    dlog[var + aa_.] G[y, var] :> 
     G[Prepend[y, -aa], var], 
   Message[GIntegrate::notlinearred, x];]]
preGIntegrate[dlog[x_],var_] := preGIntegrate[dlog[x]G[{},var],var]

GIntegrate[x_, var_, FitValues_ : {}] := 
 preGIntegrate[preautoGint[x, var, FitValues], var]
