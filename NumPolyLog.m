(* ::Package:: *)

BeginPackage["NumPolyLog`"];

AllCases::usage = "AllCases[exp,head] gives all the subexpressions of exp with head head.";
Shuffle::usage = "Shuffle[s1,s2] gives the shuffle product of s1 and s2.";
Shufflep::usage = "Shufflep[s1,s2] gives the shuffle product of s1 and s2 without the first term.";
GetAlphabet::usage = "GetAlphabet[x] gives the alphabet of x.";
GetkthEntries::usage = "GetkthEntries[k][s] gives the k-th entries of s.";
EnableFactorRoot::usage = "EnableFactorRoot[] enables the factorization of the roots in the G function.";
DisableFactorRoot::usage = "DisableFactorRoot[] disables the factorization of the roots in the G function.";
GetRoots::usage = "GetRoots[] gives the roots used for G functions.";
ClearRoots::usage = "ClearRoots[] clears the roots used for G functions.";
HPLToG::usage = "HPLToG[exp] converts HPL to G functions.";
PolyLogToG::usage = "PolyLogToG[exp] converts PolyLog to G functions.";
GIntegrate::usage = "GIntegrate[exp, var] integrates the G function with respect to var.";
MoveVar::usage = "MoveVar[exp, var] moves the var to the first position of the G function.";
ChernMoveVar::usage = "ChernMoveVar[exp, var] moves the var to the first position of the G function.";
ToSymbol::usage = "ToSymbol[exp] converts the expression to the symbol form.";
SymbolMap::usage = "SymbolMap[exp] converts the expression to the symbol form.";
GetWeight::usage = "GetWeight[a] gives the weight of a.";
TakeWeight::usage = "TakeWeight[k][exp] gives the terms with weight k in exp.";
UpliftSymbol::usage = "UpliftSymbol[exp] uplifts the symbol to the G function.";
FastCollect::usage = "FastCollect[exp, head] collects the terms with head.";
MPLG::usage = "MPLG[z, y] gives the multiple polylogarithm.";
numMZV::usage = "numMZV[m] gives the numerical value of the multiple zeta value.";
numLi::usage = "numLi[m, x] gives the numerical value of the multiple polylogarithm.";
Tensor::usage = "head of symbol.";
G::usage = "multiple polylogarithm.";
dlog::usage = "dlog[x] is the logarithmic derivative of x.";

Begin["`Private`"];

(* basic functions*)
AllCases[exp_,head_]:=Union[Cases[exp,head,All]]
shorthand[vec_]:=Module[{nowm=1,mlist={}},Do[If[mem===0,nowm++;,AppendTo[mlist,nowm];nowm=1;],{mem,vec}];If[nowm==1,{mlist,#},{Append[mlist,nowm],#}]&@DeleteCases[vec,0]]
shorthand[vec_]:=With[{hh=SparseArray[vec]},{Differences@Prepend[Flatten[hh["ColumnIndices"]],0],hh["ExplicitValues"]}]
longhand[v_,w_]:=With[{av=Accumulate[v]},Normal@SparseArray[Thread[Rule[av,w]],Last@av]]
RobustMemberQ[list_,mem_]:=If[Head[mem]===List,MemberQ[list,mem],AnyTrue[list-mem,PossibleZeroQ]]
readfirstnotinpos[list_,sublist_,direction_]:=Which[direction===1,If[Length[list]>0&&RobustMemberQ[sublist,First[list]],readfirstnotinpos[Rest[list],sublist,direction]+1,0],direction===-1,If[Length[list]>0&&RobustMemberQ[sublist,Last[list]],readfirstnotinpos[Most[list],sublist,direction]+1,0],True,0]
tailzero[list_]:=readfirstnotinpos[list,{0},-1]
headone[list_]:=readfirstnotinpos[list,{1},1]
Shuffle[{},{}]:={}
Shuffle[s1_,s2_]:=With[{p=Transpose[Permutations[Join[(1&)/@s1,(0&)/@s2]]]},With[{tp=BitXor[p,1]},Transpose[First@Outer[Part,{Join[s1,s2]},Accumulate[p] p+(Accumulate[tp]+Length[s1]) tp,1]]]]
Shufflep[_,{}]:={}
Shufflep[{},_]:={}
Shufflep[s1_,s2_]:=With[{p=Transpose[Rest@Permutations[Join[(1&)/@s1,(0&)/@s2]]]},With[{tp=BitXor[p,1]},Transpose[First@Outer[Part,{Join[s1,s2]},Accumulate[p] p+(Accumulate[tp]+Length[s1]) tp,1]]]]
(*minideg[f_,var_]:=minideg[f,var]=If[FreeQ[f,var],0,If[Limit[f,var->0]===0,minideg[f/var,var]+1,0]];*)
minideg[f_,var_]:=minideg[f,var]=If[FreeQ[f,var],0,Which[Chop@Limit[1/f,var->0]===0,-minideg[1/f,var],Chop@Limit[f,var->0]===0,minideg[f/var,var]+1,True,0]]
deglead[f_,var_]:=With[{hh=minideg[f,var]},{hh,SeriesCoefficient[f,{var,0,hh}]}]
CoeffsList[exp_,vars_]:=Normal[Prepend[Transpose@{vars,#[[2]]},{1,#[[1]]}]]&@CoefficientArrays[exp,vars]
FastCollect[exp_,head_]:=DeleteCases[With[{tensors=AllCases[exp,head]},If[tensors==={},{{1,exp}},CoeffsList[exp,tensors]]],{_,0}]
poorsum[mm_,prezz_,preyy_,prec_]:=With[{zz=N[Rationalize[prezz,0],2prec],yy=N[Rationalize[preyy,0],2prec],bound=Ceiling@With[{numK=Count[mm,1],lambda=1-Max[Abs[preyy/prezz]]},(Log[lambda]-prec Log[10]-numK Log[2]-If[numK===0,0,numK Log[numK]]+numK)/Log[1-lambda]]+10,len=Length[mm]},(-1)^len Last@Fold[Accumulate[#1(Table[(If[#2===1,yy,zz[[#2-1]]]/zz[[#2]])^(j+len-#2)(j+len-#2)^(-mm[[#2]]),{j,bound}])]&,1,Range[Length[mm],1,-1]]]
poorNG[{mm_Integer},{zz_},y_,prec_:50]:=-PolyLog[mm,y/zz]
poorNG[{mm__Integer},{zz__},y_,prec_:50]:=poorsum[{mm},{zz},y,prec]
poorNG[z_List,y_,prec_:50]:=poorNG[z,y,prec]=With[{hh=Chop[z]},If[AnyTrue[DeleteCases[hh,0],Abs[y/#]>1&],0,poorNG[Sequence@@(shorthand[hh]),y,prec]]]
(*
(* use Levin's transformation to acc series : not so efficient *)
levincc[j_,k_,n_]:=levincc[j,k,n]=(n+j+1)^(k-1)/(n+k+1)^(k-1)
levintrans[n_,k_,list_,partialsum_]:=Sum[(-1)^j Binomial[k,j]levincc[j,k,n]partialsum[[n+j]]/list[[n+j+1]],{j,0,k}]/Sum[(-1)^j Binomial[k,j]levincc[j,k,n]/list[[n+j+1]],{j,0,k}]
levinsum[mm_,prezz_,preyy_,prec_]:=N[With[{zz=N[Rationalize[prezz,0],5prec],yy=N[Rationalize[preyy,0],5prec],bound=Floor@Max[250,1/2 prec/Log[10,Abs[Min[Abs[prezz]]/preyy]]],len=Length[mm]},-levintrans[Floor[bound]-Floor[2 bound/3]-1,Floor[2bound/3],#[[1]],#[[2]]]&@({#,Accumulate@#}&[Table[(yy/zz[[1]])^(j+len-1)(j+len-1)^(-mm[[1]]),{j,bound}]*Fold[Accumulate[#1(Table[(zz[[#2-1]]/zz[[#2]])^(j+len-#2)(j+len-#2)^(-mm[[#2]]),{j,bound}])]&,1,Range[Length[mm],2,-1]]])],2prec]
(*poorNG[z_List,y_,prec_:50]:=With[{hh=Chop[z]},With[{jj=Min[Abs[DeleteCases[hh,0]/y]],kk=shorthand[hh]},If[Length[kk]<3,poorsum[Sequence@@kk,y,prec],Which[jj<=1,0,jj\[GreaterEqual]1.2,levinsum[Sequence@@kk,y,prec],True,poorsum[Sequence@@kk,y,prec]]]]]*)
*)

(*some symbol calculation*)

GetAlphabet[x_]:=AllCases[x,Tensor[y__]:>y]
tensor[___,1|-1,___]:=0
tensor[x___,1/y_,w___]:=-tensor[x,y,w]
tensor[x___,y_^a_Integer,w___]:=a tensor[x,y,w]
tensor[x___,y_,w___]/;y=!=0&&y===First@Sort[{-y,y}]:=tensor[x,-y,w]
expandTensor[exp_]:=Expand[exp/.Tensor->tensor,_tensor]/.tensor->Tensor
ExpandTensor[exp_]:=With[{hh=Dispatch[DeleteCases[(#1->Factor[#1]&)/@GetAlphabet[exp],Rule[xx_,xx_]]]},expandTensor[exp/. aa_Tensor:>Replace[aa,hh,1]/. Tensor[x___]:>Distribute[Tensor[x],Times,Tensor,Plus]]]

GetkthEntries[k_List][s_] := GetkthEntries[#][s] & /@ k
GetkthEntries[k_][s_] /; Element[k, Integers] := 
 Which[k === 0, {}, k > 0, 
  Union[Cases[s, 
    Tensor[Sequence @@ ConstantArray[_, k - 1], y_, ___] :> y, 
    All]], k < 0, 
  Union[Cases[s, 
    Tensor[___, y_, Sequence @@ ConstantArray[_, -k - 1]] :> y, 
    All]]]

Options[dlogfactor] = {"FactorRoot" -> False, "Roots" -> {}};

dlogfactor[dlog[xx_]] := 
 dlogfactor[dlog[xx]] = 
  With[{hh = FactorList[xx]}, Total[dlog[#[[1]]] #[[2]] & /@ hh] /. 
    dlog[1 | -1 | 0] -> 0] /. dlog[x_] :> dlog[Last[Sort[{x, -x}]]]
totalD[x_ + y_] := totalD[x] + totalD[y]
totalD[x_ y_] := totalD[x] y + totalD[y] x
totalD[x_^n_Integer] := n x^(n - 1) totalD[x]
totalD[G[a_, z_]] := 
 totalD[G[a, z]] = 
  Total@Array[G[Delete[a, #], z] Which[Length[a] == 1, 
       dlog[a[[#]] - z] - dlog[a[[#]] - 0], # == 1, 
       dlog[a[[#]] - z] - dlog[a[[#]] - a[[# + 1]]], # == Length[a], 
       dlog[a[[#]] - a[[# - 1]]] - dlog[a[[#]] - 0], True, 
       dlog[a[[#]] - a[[# - 1]]] - dlog[a[[#]] - a[[# + 1]]]]&, 
      Length[a]] /. dlog[xx_] :> dlogfactor[dlog[xx]] /. G[{}, _] :> 1
totalD[Tensor[a___, b_]] := 
 Tensor[a] dlogfactor[dlog[b]] /. Tensor[] -> 1
totalD[x_] /; Length[Variables[x]] === 0 := 0
totalD[y_ dlog[x_List]] := 
 Expand[dlog[x] totalD[y]] /. 
  dlog[xx_] dlog[yy_List] :> dlog[Prepend[yy, xx]]
totalD[x_, n_Integer /; n > 0] := 
 If[n === 1, totalD[x] /. dlog[u_] :> dlog[{u}], 
  totalD[Expand@totalD[x, n - 1]]]

(*
ExpandTensor[exp_] := 
 With[{hh = 
    Expand[exp, _Tensor] //. 
     Tensor[a___, 0, c___] :> Tensor[a, $zero$, c]}, 
  NestWhile[
     Expand[Expand[
        If[Head[#] === Plus, totalD /@ #, 
         totalD[#]], _dlog], _Tensor] &, 
     Expand[Expand[
        If[Head[hh] === Plus, totalD /@ (hh), 
         totalD[hh]], _dlog], _Tensor] /. 
      dlog[x_] :> dlog[List[x]], ! FreeQ[#, _Tensor] &] /. 
    dlog[x_] :> Tensor @@ x /. $zero$ -> 0]
*)

SymbolMap[exp_] := 
 With[{hh = Expand[exp, _G]}, 
  NestWhile[
    Expand[Expand[
       If[Head[#] === Plus, totalD /@ #, totalD[#]], _dlog], _G] &, 
    Expand[Expand[
       If[Head[hh] === Plus, totalD /@ (hh), 
        totalD[hh]], _dlog], _G] /. 
     dlog[x_] :> dlog[List[x]], ! FreeQ[#, _G] &] /. 
   dlog[x_] :> Tensor @@ x]

(* to symbol *)
preGtoSymbol[GT[{}, _, Tensor[b___]]] := Tensor[b]
preGtoSymbol[GT[a_, z_, Tensor[b___]]] := 
 Total@Array[preGtoSymbol[
   GT[Delete[a, #], z, 
    Tensor[Which[Length[a] == 1, (a[[#]] - z)/(a[[#]] - 0), # == 1, (
      a[[#]] - z)/(a[[#]] - a[[# + 1]]), # == Length[a], (
      a[[#]] - a[[# - 1]])/(a[[#]] - 0), True, (a[[#]] - a[[# - 1]])/(
      a[[#]] - a[[# + 1]])], b]]]&, Length[a]]
slowGtoSymbol[G[a_, z_]] := preGtoSymbol[GT[a, z, Tensor[]]]

generateGtosymbol[
  weight_] := (G[
     Table[ToExpression["$a" <> ToString[i] <> "_"], {i, 
       weight}], $zz_] -> 
    ExpandTensor[
     slowGtoSymbol[
      G[Table[ToExpression["$a" <> ToString[i]], {i, 
         weight}], $zz]]]) /. Rule -> RuleDelayed

$tosymbolGstored = {4, Table[generateGtosymbol[i], {i, 4}]};

removetailzero[anyG[z_, y_]] := 
 Which[z === {}, 1, PossibleZeroQ[Last[z]], 
  Expand[With[{zz = Most[z]}, 
    With[{kk = tailzero[z], len = Length[z]}, 
     1/kk (If[y === 1, 0, Log[y] removetailzero@anyG[zz, y]] - 
        Total@Array[removetailzero@
          anyG[Join[z[[1 ;; # - 1]], {0}, 
            z[[# ;; len - kk - 1]], {z[[len - kk]]}, 
            ConstantArray[0, kk - 1]], y]&, len - kk])]]], 
  True, anyG[z, y]]

GtoSymbol[exp_] := 
 With[{maxlen = 
    Max[Length /@ Union@Cases[exp, G[x_, _] :> x, All]]}, 
  If[maxlen > First@$tosymbolGstored, 
   $tosymbolGstored = {maxlen, 
     Join[Last@$tosymbolGstored, 
      Table[generateGtosymbol[w], {w, 1 + First@$tosymbolGstored, 
        maxlen}]]};
   exp /. G[x__] :> removetailzero[anyG[x]] /. anyG -> G /. 
    Last@$tosymbolGstored, 
   exp /. G[x__] :> removetailzero[anyG[x]] /. anyG -> G /. 
    Last@$tosymbolGstored]]

PolyLogToG[exp_] := 
 exp /. {Log[x_] :> G[{0}, x], 
   PolyLog[k_, x_] :> -G[Append[ConstantArray[0, k - 1], 1], x]}

HPLToG[exp_] := 
 exp /. HPL[x_, 
    y_] :> (-1)^Length[x] G[longhand[x, ConstantArray[1, Length@x]], 
     y]

ToSymbol[exp_] := 
 With[{hh = GtoSymbol@PolyLogToG@exp}, 
  ExpandTensor@FixedPoint[
   Expand[# /. Pi->0 /. {Tensor[a___] Tensor[b___] :> 
         Total[Tensor @@@ Shuffle[{a}, {b}]], 
        Tensor[a___]^b_Integer /; b >= 2 :> 
         Tensor[a]^(b - 2) Total[Tensor @@@ Shuffle[{a}, {a}]]} /. 
      Tensor[___, 1 | -1, ___] :> 0] &, hh /. Log[x_] :> Tensor[x]]]

(* graded structure *)

GetWeight[a_Rationals]:=0
GetWeight[a_Integers]:=0
GetWeight[a_ b_] := GetWeight[a] + GetWeight[b]
GetWeight[Power[a_, b_Integer]] := b GetWeight[a]
GetWeight[Pi] := 1
GetWeight[Zeta[a_]] := a
GetWeight[Log[a_]] := 1
GetWeight[PolyLog[a_, b_]] := a
GetWeight[Tensor[a__]] := Length[{a}]
GetWeight[G[x_, y_]] := Length[x]
GetWeight[MPLG[x_, y_]] := Length[x]
GetWeight[a_Plus] := 
 If[SameQ @@ (GetWeight /@ (List @@ a)), GetWeight[First[a]], -1]
GetWeight[a_List] := GetWeight /@ a
GetWeight[
   a_] /; (Head[a] =!= G && Head[a] =!= MPLG && Head[a] =!= Tensor && 
    Head[a] =!= Log && Head[a] =!= PolyLog && Head[a] =!= Zeta && 
    a =!= Power && a =!= Plus && a =!= List && a =!= Pi) := 0
TakeWeight[k_][exp_] := Select[Expand[exp], GetWeight[#] === k &]
TakeWeight[k_List][exp_] := Select[Expand[exp], MemberQ[k,GetWeight[#]] &]

(* 
extendedG is the extended G function introduced in the section 5.3 of 0410259 :
    extendedG[y1,{b1,...,br},{z1,...,zn},y2,k] = int_0^y1 ds1/(s1-b1) ... int_0^s(r-1) dsr/(sr-br) G(z1,...,z(k-1),sr,z(k+1),...,zn;y2),
where k is the position of integral variable. For k=0, there's no integral variable, so
    extendedG[y1,{b1,...,br},{z1,...,zn},y2,k] = G(b1,...,br;y1)*G(z1,...,zn;y2).
It's clear that
    extendedG[_,{},{z1,...,zn},y2,0] = G(z1,...,zn;y2).
*)

(* all zero, power of log *)
extendedG[y1_,b_,z_,y2_,0]/;MatchQ[z,{0..}]:=If[b==={},1,extendedG[0,{},b,y1,0]]Log[y2]^Length[z]/Length[z]!;
extendedG[y1_,b_,{0..},0,0]:=ComplexInfinity
extendedG[y1_,b_,z_,0,0]/;!MatchQ[z,{0..}]:=0
(* ini : be careful FirstPosition*)
extendedG[y1_,b_,z_,y_,0]/;(Last[z]=!=0):=(If[b==={},1,extendedG[0,{},b,y1,0]]*If[!AnyTrue[DeleteCases[z,0],Abs[#]<Abs[y]&],goodG[z/y,1],With[{pos=First@First@Position[Abs[Chop[z]],Min[Abs@DeleteCases[Chop[z],0]],1]},extendedG[z[[pos]],{},ReplacePart[z,pos->0],y,pos]]])
(* remove tail zero *)
extendedG[y1_,b_,{zz___,0},y2_,w_]/;(w=!=Length[{zz,0}]):=(extendedG[y1,b,{zz,0},y2,w]=Expand[With[{z={zz,0}},With[{kk=If[Length[z]-#<w,Length[z]-w,#]&@tailzero[z],len=Length[z]},1/kk (If[y2===1,0,Log[y2]extendedG[y1,b,{zz},y2,w]]-Total@Array[extendedG[y1,b,Join[z[[1;;#-1]],{0},z[[#;;len-kk-1]],{z[[len-kk]]},ConstantArray[0,kk-1]],y2,If[w!=0&&#-1<w,w+1,w]]&,len-kk])]]])
(* special values, assuming dG[1]=log[0]->0*)
(* almost all zero, Li *)
extendedG[y1_,b_,z_,y_,0]/;MatchQ[Most[z],{0..}]:=-If[b==={},1,extendedG[0,{},b,y1,0]]*PolyLog[Length[z],y/Last[z]];
extendedG[y1_,b_,{z_},y_,0]:=If[b==={},1,goodG[b,y1]]*If[y===z,0,Log[(-y+z)/z]];
extendedG[y1_,b_,{z1_,z2_},y_,0]/;(z2=!=0):=If[z1===y,-extendedG[y1,b,{z2,z1},y,0],If[b=={},1,goodG[b,y1]]*(-PolyLog[2,y/(y-z1)]-PolyLog[2,y/z2]+PolyLog[2,y (z1-z2)/((-y+z1) z2)])]
(* tail integral var *)
branchextendedG[a_,b_,z_,y_,w_,branch_]/;(MatchQ[z,{0..}]&&w===Length[z]):=branchextendedG[a,b,z,y,w,branch]=Expand@If[Length[z]===w===1,branchextendedG[0,{},Append[b,y],a,0,branch]+If[branch===-1,Log[-y]-2*Pi*I,Log[-y]] If[b=={},1,branchextendedG[0,{},b,a,0,branch]]-branchextendedG[0,{},Append[b,0],a,0,branch],If[b=={},1,branchextendedG[0,{},b,a,0,branch]](-Zeta[w]+branchextendedG[y,{0},ConstantArray[0,w-1],y,w-1,branch])-branchextendedG[a,Append[b,0],ConstantArray[0,w-1],y,w-1,branch]]
extendedG[a_,b_,z_,y_,w_]/;(MatchQ[z,{0..}]&&w===Length[z]):=branchextendedG[a,b,z,y,w,Sign[Im[a]]]/.branchextendedG[p__,q_]:>extendedG[p]
extendedG[y1_,b_,z_,y2_,w_]/;((!MatchQ[z,{0..}])&&w===Length[z]):=(extendedG[y1,b,z,y2,w]=Expand@With[{tz=tailzero[z]},(extendedG[0,{},z[[;;w-tz]],y2,0]extendedG[y1,b,ConstantArray[0,tz],y2,tz])-Total[extendedG[y1,b,(#/.Infinity->0),y2,First[FirstPosition[#,Infinity]]]&/@Shufflep[z[[;;w-tz]],longhand[{tz},{Infinity}]]]])
(* integral var in other pos *)
extendedG[y1_,b_,z_,y2_,w_]/;(w!=0&&w!=Length[z]):=(extendedG[y1,b,z,y2,w]=If[w===1,extendedG[y1,b,z,y2,0]+extendedG[y1,Append[b,y2],Delete[z,w],y2,0]+extendedG[y1,Append[b,z[[w+1]]],Delete[z,w+1],y2,w]-extendedG[y1,Append[b,z[[w+1]]],Delete[z,w],y2,0],extendedG[y1,b,z,y2,0]-extendedG[y1,Append[b,z[[w-1]]],Delete[z,w-1],y2,w-1]+extendedG[y1,Append[b,z[[w-1]]],Delete[z,w],y2,0]+extendedG[y1,Append[b,z[[w+1]]],Delete[z,w+1],y2,w]-extendedG[y1,Append[b,z[[w+1]]],Delete[z,w],y2,0]])
(* goodG, G functions which can be evaluated by series expansion, assuming dG[1]=log[0]->0 *)
goodG[z_,y_]:=If[y===0,0,goodG[z/y]];
(*goodG[z_,1]:=With[{kk=headone[z],len=Length[z]},If[len==1,dG[1],1/kk (dG[1]goodG[Rest[z],1]-Sum[goodG[Join[ConstantArray[1,kk-1],z[[kk+1;;m]],{1},z[[m+1;;]]],1],{m,kk+1,len}])]]/;First[z]===1;*)
goodG[z_List]/;(First[z]===1):=With[{kk=headone[z],len=Length[z]},If[len==1,0,1/kk (-Sum[goodG[Join[ConstantArray[1,kk-1],z[[kk+1;;m]],{1},z[[m+1;;]]]],{m,kk+1,len}])]];
goodG[z_List]/;(MatchQ[Most[z],{0..}]&&Last[z]=!=0):=-PolyLog[Length[z],1/Last[z]];
goodG[z_List]/;Length[z]===2:=-PolyLog[2,1/(1-z[[1]])]-PolyLog[2,1/z[[2]]]+PolyLog[2,(z[[1]]-z[[2]])/((-1+z[[1]]) z[[2]])];

(* acc G, use Hölder convolution to accelerate convergence *)
accG[{z_},prec_:50]:=Log[(-1+z)/z];
accG[{z1_,z2_},prec_:50]:=-PolyLog[2,1/(1-z1)]-PolyLog[2,1/z2]+PolyLog[2,(z1-z2)/((-1+z1) z2)];
accG[hh_, prec_ : 50] := 
 accG[hh, prec] = 
  With[{z = Rationalize[hh, 0]}, 
   If[AnyTrue[DeleteCases[z, 0], Abs[#] <= 1.05 &], 
    accG[2 z, prec] + (-1)^Length[z] accG[2 (1 - Reverse[z]), prec] + 
     Total@Array[(-1)^# accG[2 (1 - Reverse[z[[1 ;; #]]]), prec] accG[
          2 z[[# + 1 ;;]], prec] &, Length[z] - 1], 
    If[AllTrue[DeleteCases[z, 0], Abs[#] > 1 &], poorNG[z, 1, prec], 
     extendedG[0, {}, Rationalize[z, 10^(-prec - 5)], 1, 0]]]]
(* define MPLG *)
SetAttributes[MPLG, NumericFunction]
MPLG[{}, _]  := 1
MPLG[z_, 0] /; (! MatchQ[z, {0 ..}]) := 0
MPLG[{0 ..}, 0] := ComplexInfinity
MPLG[{a_ /; a =!= 0}, b_] := Log[1 - b/a]
MPLG[z_, y2_] /; MatchQ[z, {0 ..}] && (y2 =!= 0) := Log[y2]^Length[z]/Length[z]!;
MPLG[z_, y2_] /; (MatchQ[Most[z],{0..}]&&Last[z]=!=0) := -PolyLog[Length[z],y2/Last[z]];
MPLG[zzz_, y_ /; y =!= 0] /; 
  AllTrue[Append[zzz, y], NumberQ] && 
   AnyTrue[Append[zzz, y], InexactNumberQ] := 
 With[{prec = Ceiling@N@Precision[Append[zzz, y]], z = zzz, 
   zy = zzz/y}, 
  If[PossibleZeroQ[Last[z]], 
   Expand[With[{zz = Most[z]}, 
     With[{kk = tailzero[z], len = Length[z]}, 
      1/kk   (If[y === 1, 0, Log[y]   MPLG[zz, y]] - 
         Total@Array[
           MPLG[Join[z[[1 ;; # - 1]], {0}, 
              z[[# ;; len - kk - 1]], {z[[len - kk]]}, 
              ConstantArray[0, kk - 1]], y] &, len - kk])]]], 
   N[If[Rationalize[First@zy, 10^(-prec - 5)] === 1, ComplexInfinity, 
     extendedG[0, {}, Rationalize[zy, 10^(-prec - 5)], 1, 0] /. 
       goodG[x_] :> goodG[Rationalize[x, 0]] //. {goodG[x_] :> 
        accG[x, prec]}], prec]]]
numLi[m_, x_, prec_ : 50] := N[(-1)^Length[m] MPLG[longhand[m, Rest[FoldList[#1/#2 &, 1, x]]], 1], prec]
numMZV[m_, prec_ : 50] := numLi[m, ConstantArray[1, Length[m]], prec]

(*
branchMPLG[z_, y_] := With[{lp = lastpos[z, {_, -1}]},
  If[lp === 0, MPLG[First /@ z, y],
   branchMPLG[ReplacePart[z, lp -> z[[lp]] {1, -1}], y] - 
    2 Pi I MPLG[First /@ z[[lp + 1 ;;]], 
      First[z[[lp]]]] branchMPLG[{#[[1]] - First[z[[lp]]], 
         If[(#[[2]] === -1) && (#[[1]] <= First[z[[lp]]]), 
          1, #[[2]]]} & /@ z[[;; lp - 1]], y - First[z[[lp]]]]]]
*)

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
                                      -dlog(an)G({a1,...,an-1},z),    ........... (1)
Finally, we reduce it to 
    G({an},z) = log(1-z/an) = log(c) + sum_i n_i log(1-t/c_i) 
                            = log(c) + sum_i n_i G(ci,t), 
and then we can calculate all remaining integral 
    int dlog(t1-b1)dlog(t2-b1)...dlog(t(n-1)-b(n-1))G(ci,t) = G({b1,...,b(n-1),ci},t)
from the definition of G function. 

However, G({a1(0),...,an(0)},z) usually diverges when a1(0)=1 or an(0)=0, we use the 
shuffle regularization used in [1403.3385] to get the finite result. On the other hand,
the integration of eq.(1) usually depands on the branch you choice, otherwise we can 
only get a funtion with the same symbol. The other steps are all algebraic, so if (1) 
is correct (on a given region), the whole reduction is correct (on the given region). 
In our realization, one could add fitting values to support numerical checks of eq.(1) 
in the recursion, otherwise it will not check (1).
*)

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
  Total@Array[((-1)^(# - 1) With[{jj = 
       If[# === {}, myword[], Total[myword @@@ #]] &@(Shuffle[
          ConstantArray[-1, 
           # - 1], (List @@ word)[[# + 1 ;;]]])}, (jj /. 
        myword[x___] :> myword[word[[#]], x]) - (jj /. 
        myword[x___] :> myword[-1, x])])&, Length@word],
  With[{hh = readfirstnotinpos[List @@ word, removelist, 1]},
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

mobiusinftoone[
  x_myword] := (If[# === -1, 0, myword[#/(1 + #)]] - myword[1] & /@ 
    x) //. {myword[y___, myword[p_] + q_, w___] :> 
    myword[y, p, w] + myword[y, q, w], 
   myword[y___, -myword[p_], w___] :> -myword[y, p, w]}

specialmobiustrans[x_myword] := 
  regword[x, Infinity, {0}] /. myword[y__] :> mobiusinftoone[myword[y]] /. 
   myword[yy__] :> G[Simplify /@ {yy}, 1];

(*
We will face two kinds of divergance (t>0, t->0), 
    G({a1 t^k1,...,an t^kn},1) and G({1-b1 t^l1,...,1-bn t^ln},1).
They can be related by the identity 
    G({1-c1,...,1-cn},1) = (-1)^n G({cn,...,c1},1),
however, when 0 <= ci <= 1, one should reverse the branch. 
Here, we can calculate the result G({cn,...,c1},1) first and then
set all G({d1,...,dk},1) -> (-1)^k G({1-dk,...,1-d1},1) in the
result. The Möbius transformation  z/(1+z) used in the calculation 
of G({cn,...,c1},1) takes a + I e to a/(1+a) + I e/(1+a)^2, 
which keeps the branch.
*)

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
 preregGinf[z] /. G[zz_, Infinity] :> regGinf[G[zz, Infinity]] /. 
  G[zz_, 1] :> (-1)^Length[zz] G[Reverse[1 - zz], 1]

regGallnear1[z_] :=
  (-1)^Length[z] preregGinf[Reverse@z] /. 
   G[zz_, Infinity] :> regGinf[G[zz, Infinity]] /. 
  G[zz_, 1] :> (-1)^Length[zz] G[Reverse[1 - zz], 1]

lastpos[list_, pat_] := 
 With[{hh = FirstPosition[Reverse[list], pat]}, 
  If[hh === Missing["NotFound"], 0, 1 + Length[list] - First@hh]]

(* we assume that t>0 and t=t-i0 such that G({a..},t-i0)=G({a..},t) *)
BranchLead[func_, var_, range_, OptionsPattern[{"FitValue"->{}}]] := 
 With[{nonvarFitValue = DeleteCases[OptionValue["FitValue"], var -> _], 
   md = minideg[func /. DeleteCases[OptionValue["FitValue"], var -> _], var]},
  With[{lead = SeriesCoefficient[func, {var, 0, md}], 
    numlead = 
     SeriesCoefficient[func /. nonvarFitValue, {var, 0, md}]},
   Which[
    FreeQ[func, var], {0, func, 1},
    ! NumberQ[numlead], {md, lead, 1},
    md == 0 && ! Element[numlead, Reals], {0, lead, 1},
    md == 0 && ! (First[range] < numlead < Last[range]), {0, lead, 1},
    md == 0 && First[range] < numlead < Last[range],
    With[{subdeglead = deglead[func - lead /. nonvarFitValue, var]},
     {0, lead, If[Last[subdeglead] <= 0, 1, -1]}],
    True, {md, lead, 1}
    ]]]

branchG[z_, y_, opts : OptionsPattern[{"FitValue"->{}}]] := 
 With[{lp = lastpos[z, {_, -1}]}, 
  If[lp === 0, G[First /@ z, y] /. G[{}, _] :> 1, 
   branchG[ReplacePart[z, lp -> z[[lp]] {1, -1}], y, opts] - 
    2 Pi I If[z[[lp + 1 ;;]] === {}, 1, 
      regwordabove[
        myword @@ (First /@ z[[lp + 1 ;;]]), {First[z[[lp]]]}] /. 
       myword[x__] :> 
        G[{x}, First[z[[lp]]]]] branchG[{#[[1]] - First[z[[lp]]], 
         Which[
           ! NumberQ[(First[z[[lp]]] - #[[1]]) /. OptionValue["FitValue"]], 1, 
           ! Element[(First[z[[lp]]] - #[[1]]) /. OptionValue["FitValue"], Reals], 1, 
           (#[[2]] === -1) && ((First[z[[lp]]] - #[[1]] /. OptionValue["FitValue"]) >= 0), 1,
          True, #[[2]]]} & /@ 
       z[[;; lp - 1]], y - First[z[[lp]]], opts]]]

normGvar0[z_, var_, opts : OptionsPattern[{"FitValue"->{}}]] := 
 With[{nonvarFitValue = DeleteCases[OptionValue["FitValue"], var -> _]},
  Which[
   z === {}, 1,
   AnyTrue[DeleteCases[z /. nonvarFitValue, 0], PossibleZeroQ[Limit[1/#, var -> 0]] &], 0, 
   PossibleZeroQ[Last[z]] || PossibleZeroQ[First[z] - 1], 
   regword[myword @@ z, {1}, {0}] /. myword[xx__] :> normGvar0[{xx}, var, opts], 
   (* TODO: keep divergent part *)
   True, 
   With[{firstlimit = Together[First[z] /. nonvarFitValue] /. var -> 0, 
     lastlimit = Together[Last[z] /. nonvarFitValue] /. var -> 0}, 
    Which[(! PossibleZeroQ[firstlimit - 1]) && (! PossibleZeroQ[lastlimit]), 
     branchG[If[#[[1]] > 0, {0, 1}, Rest[#]] & /@ (BranchLead[#, var, {0, 1}, opts] & /@ z), 1, 
      opts], (* be careful *)
    PossibleZeroQ[lastlimit], 
     With[{hh = 
        tailzero[Rationalize@Chop[Together[z /. nonvarFitValue] /. var -> 0]]}, 
      With[{kk = 
         regGallnear0[
          Most[BranchLead[#, var, {0, 1}, opts]] & /@ z[[-hh ;;]]]}, 
       If[Length[z] === hh, kk, 
        kk If[kk === 0, 0, normGvar0[z[[;; -hh - 1]], var, opts]] - 
         Total[(normGvar0[#, var, opts] & /@ 
            Shufflep[z[[;; -hh - 1]], z[[-hh ;;]]])]]]], 
     PossibleZeroQ[firstlimit - 1], 
     With[{hh = 
        headone[Rationalize@Chop[Together[z /. nonvarFitValue] /. var -> 0]]}, 
      With[{kk = 
         regGallnear1[
          Most[BranchLead[#, var, {0, 1}, opts]] & /@ (1 - 
             z[[;; hh]])]}, 
       If[Length[z] === hh, kk, 
        kk If[kk === 0, 0, normGvar0[z[[hh + 1 ;;]], var, opts]] - 
         Total[(normGvar0[#, var, opts] & /@ 
            Shufflep[z[[;; hh]], z[[hh + 1 ;;]]])]]]]]]]]

NormGVar0[z_, y_, var_, opts : OptionsPattern[{"FitValue" -> {}}]] :=
With[{nonvarFitValue = DeleteCases[OptionValue["FitValue"], var -> _]},
 Which[
  z === {}, 1,
  y === 1, normGvar0[z, var, opts],
  AllTrue[z, PossibleZeroQ], (normGvar0[{Simplify[1/(1 - y)]}, var, opts]^Length[z])/Length[z]!,
  PossibleZeroQ@Last[z], 
  Expand[With[{kk = tailzero[z], len = Length[z]}, 
    1/kk (NormGVar0[Most[z], y, var, opts] normGvar0[{1/(1 - y)}, var, opts] - 
       Total@Array[NormGVar0[
         Join[z[[1 ;; # - 1]], {0}, 
          z[[# ;; len - kk - 1]], {z[[len - kk]]}, 
          ConstantArray[0, kk - 1]], y, var, opts]&, 
         len - kk])]],
  True, normGvar0[z/y, var, opts]]]

(* Newton-Leibniz reduction *)

MoveVar::notlinearred = "`1` is not linear reducible!";

dlogfactor[x_dlog + y_dlog, var_, opts : OptionsPattern[]] := 
  dlogfactor[x, var, opts] + dlogfactor[y, var, opts];
dlogfactor[x_dlog - y_dlog, var_, opts : OptionsPattern[]] := 
  dlogfactor[x, var, opts] - dlogfactor[y, var, opts];
dlogfactor[a_ x_dlog, var_, opts : OptionsPattern[]] := 
  a dlogfactor[x, var, opts];

(* 
TODO: it could be wrong when recursively using it, since it will find the roots 
of polynomials like x^2-root$12123, but root$12123 can also depend on x.
*)
dlogfactor[exp_, var_, opts : OptionsPattern[]] := 
 dlogfactor[exp, var, opts] = 
  With[{hh = 
     exp /. dlog[xx_] :> 
         Total[#[[2]]  dlog[#[[1]]] & /@ FactorList[xx]] /. 
       dlog[xx_] :> 0 /; FreeQ[xx, var] /. 
      dlog[xx_ /; PolynomialQ[xx, var]] :> 
       dlog[Collect[xx/Coefficient[xx, var^Exponent[xx, var]], var]]},
    If[! OptionValue["FactorRoot"], 
    With[{jj = 
       Select[(AllCases[hh, _dlog] /. 
          dlog -> Identity), ! (PolynomialQ[#, var] && 
            Exponent[#, var] === 1) &]}, 
     If[Length[jj] > 0, Message[MoveVar::notlinearred, First[jj]];
      Abort[]; hh, hh]], 
    hh /. dlog[xx_ /; PolynomialQ[xx, var]] :> 
      With[{deg = Exponent[xx, var]}, 
       If[deg === 1, dlog[xx], 
        If[! MemberQ[First /@ OptionValue["Roots"], 
           Factor /@ CoefficientList[xx, var]],
         With[{kk = 
            If[Length@OptionValue["Roots"] === 0, 1, 
             1 + Max@Union@
                Cases[OptionValue["Roots"], root[a_, _] :> a, 
                 All]]},
          With[{jj = Array[root[kk, #]&, deg]}, 
           SetOptions[dlogfactor, 
            "Roots" -> 
             Append[OptionValue[
               "Roots"], (Factor /@ CoefficientList[xx, var]) -> 
               jj]];
           Total@Array[dlog[var - jj[[#]]]&, deg]]], 
         With[{jj = 
            Factor /@ CoefficientList[xx, var] /. 
             OptionValue["Roots"]}, 
          Total@Array[dlog[var - jj[[#]]]&, deg]]]]]]]

dlogfactor2[exp_, var_, opts : OptionsPattern[]] := 
   With[{hh = exp /. dlog[xx_] :> 
                 Total[#[[2]] dlog[#[[1]]] & /@ FactorList[xx]] /. 
             dlog[xx_] :> 0 /; FreeQ[xx, var] /. 
           dlog[xx_ /; PolynomialQ[xx, var]] :> 
       dlog[Collect[xx/Coefficient[xx, var^Exponent[xx, var]], var]]}, 
     hh]

preMoveVar[G[y_, z_], var_, opts : OptionsPattern[{"FitValue" -> {}}]] := 
 preMoveVar[G[y, z], var, opts] = NormGVar0[y, z, var, opts] +
    If[Length[y] === 1, 
     dlogfactor[dlog[First[y] - z] - dlog[First[y]], var] /. 
      dlog[x_] :> G[{-x /. var -> 0}, var], 
     Expand[-dlogfactor[dlog[Last[y]], var] preMoveVar[G[Most[y], z], 
           var, opts] + 
         dlogfactor[dlog[z - First[y]], var] preMoveVar[G[Rest[y], z],
            var, opts] + 
         Total@Array[dlogfactor[dlog[y[[#]] - y[[# + 1]]], 
            var] (preMoveVar[G[Delete[y, # + 1], z], var, opts] - 
             preMoveVar[G[Delete[y, #], z], var, opts]) &, 
           Length[y] - 1]] /. 
       dlog[x_] G[s1_, var] :> G[Prepend[s1, -x /. var -> 0], var] /. 
      dlog[x_] :> G[{-x /. var -> 0}, var]] /. {G[_, 0] :> 0, 
    G[{0 ..}, 1] :> 0, G[{1/2}, 1] -> I Pi}

EnableFactorRoot[] := (SetOptions[dlogfactor, "FactorRoot" -> True];)
DisableFactorRoot[] := (SetOptions[dlogfactor, "FactorRoot" -> False];)
GetRoots[] := 
 With[{hh = Options[dlogfactor, "Roots"][[1, 2]]}, 
  If[hh === {}, {}, 
   Flatten[(Table[#1[[2, i]] -> root[#1[[1]], i], {i, 
         Length[#1[[2]]]}] &) /@ hh]]]
ClearRoots[] := (DownValues[dlogfactor] = DownValues[dlogfactor][[-5 ;;]];
   SetOptions[dlogfactor, "Roots" -> {}];)

(*
revbranch[G[x_, var_], FitValue_ : {}] := 
 With[{revbranchx = 
     Which[(! NumberQ[var /. FitValue]) || (! 
           NumberQ[# /. FitValue]), {#, 1}, ! 
         Element[# /. FitValue, Reals], {#, 1}, (0 < # < var) /. 
         FitValue, {#, -1}, True, {#, 1}] & /@ x}, 
   branchG[revbranchx, var, FitValue]] //. 
  G[pp_, qq_ /; ! FreeQ[qq, var] && qq =!= var && 
      D[qq, var] === 1] :> (preMoveVar[G[pp, qq], var, FitValue])
*)

(* only for debug now *)
oldMoveVar[exp_, var_, opts : OptionsPattern[{"FitValue"->{}}]] := 
 (Simplify /@exp) //. G[xx_, zz_] /; ((! FreeQ[{xx, zz}, var]) && zz =!= var) :> 
   preMoveVar[G[xx, zz], var, opts]

(* only for UT pure function *)
MoveVar[x_, var_, opts : OptionsPattern[{"FitValue" -> {}}]] := 
 If[GetWeight[x] > 
   0, (x /. {G[y_, z_] :> NormGVar0[y, z, var, opts]}) + 
   With[{hh = totalD[x] /. dlog[y_] :> dlogfactor[dlog[y], var] /. _totalD :> 0}, 
    If[hh === 0, 0, 
     With[{dlogs = AllCases[hh, _dlog]}, 
       Expand[(MoveVar[#, var, opts] & /@ 
             Normal@Last@CoefficientArrays[hh, dlogs]) . dlogs] /. 
         dlog[xx_] G[s1_, var] :> 
          G[Prepend[s1, -xx /. var -> 0], var] /. 
        dlog[xx_] :> G[{-xx /. var -> 0}, var]] /. {G[_, 0] :> 0, 
       G[{0 ..}, 1] :> 0, G[{1/2}, 1] -> I Pi}]], x]


(* allow chern iterated rep *)
preChernMoveVar[x_, var_, opts : OptionsPattern[{"FitValue" -> {}}]] :=
  If[GetWeight[x] > 
   0, (x /. {G[y_, z_] :> NormGVar0[y, z, var, opts]}) + 
   With[{hh = 
      FastCollect[
       totalD[x] /. dlog[y_] :> dlogfactor2[dlog[y], var] /. _totalD :>
          0, _dlog]}, 
    If[hh === 0, 
     0, (Expand[
          Total[#[[1]] preChernMoveVar[#[[2]], var, opts] & /@ hh]] /. 
         dlog[xx_] ChernG[s1_, var] :> ChernG[Prepend[s1, xx], var] /. 
        dlog[xx_] :> ChernG[{xx}, var]) /. {G[_, 0] :> 0, 
       G[{0 ..}, 1] :> 0, G[{1/2}, 1] -> I Pi}]], x]
ChernMoveVar[x_, var_, opts : OptionsPattern[{"FitValue" -> {}}]] := 
 preChernMoveVar[x, var, opts] /. 
  ChernG[a_, var] :> 
   If[AllTrue[a, Exponent[#, var] === 1 &], G[-a /. var -> 0, var], 
    ChernG[a, var]]

GIntegrate::notlinearred = "`1` is not linear reducible!";
preGIntegrate[x_, var_] /; FreeQ[x, var] := x var
preGIntegrate[c_ x_, var_] /; FreeQ[c, var] := c preGIntegrate[x, var]
preGIntegrate[x_ + y_, var_] := 
 preGIntegrate[x, var] + preGIntegrate[y, var]
preGIntegrate[dlog[x_] G[y_, var_], var_] := 
 With[{hh = 
     Expand[G[y, 
        var] (Total[#[[2]] dlog[#[[1]]] & /@ FactorList[x]] /. 
          dlog[xx_] :> 0 /; FreeQ[xx, var] /. 
         dlog[xx_ /; PolynomialQ[xx, var]] :> 
          dlog[xx/Coefficient[xx, var^Exponent[xx, var]]])]}, 
   With[{jj = 
      Select[(AllCases[hh, _dlog] /. 
         dlog -> Identity), ! (PolynomialQ[#, var] && 
           Exponent[#, var] === 1) &]}, 
    If[Length[jj] > 0, Message[GIntegrate::notlinearred, First[jj]];
     Abort[];, hh]]] /. 
  dlog[xx_] G[yy_, var] :> G[Prepend[yy, -xx /. var -> 0], var]
preGIntegrate[dlog[x_],var_] := preGIntegrate[dlog[x]G[{},var],var]

combGvar[x_, var_] := 
 FixedPoint[
  Expand[# //. {G[xx_, var] G[yy_, var] :> 
       Total[G[#, var] & /@ Shuffle[xx, yy]], 
      G[xx_, var]^k_Integer /; k > 1 :> 
       G[xx, var]^(k - 2) Total[G[#, var] & /@ Shuffle[xx, xx]]}] &, 
  x]

GIntegrate[x_, var_, opts : OptionsPattern[{"FitValue" -> {}}]] := 
 With[{hh = 
    Expand[combGvar[
      Total[#[[1]] MoveVar[#[[2]], var, opts] & /@ 
        FastCollect[x, _dlog]], var]]}, 
  If[Head[hh] === Plus, preGIntegrate[#, var] & /@ hh, 
   preGIntegrate[hh, var]]]

(* the integral is assumed to be converged *)
GIntegrate[x_, {var_, a_, b_}, opts : OptionsPattern[{"FitValue" -> {}}]] := 
  (With[{hh = 
        GIntegrate[x, var, opts]}, (hh /. var -> b) - (hh /. 
         var -> a)] /. G[zz_, Infinity] :> regGinf[G[zz, Infinity]]) /. 
   G[{xx_, xxx___}, 
     xx_] :> (regwordabove[myword @@ {xx, xxx}, {xx}] /. 
      myword[zz__] :> G[{zz}, xx]) /. {G[_, 0] :> 0, 
   G[{0 ..}, 1] :> 0, G[{1/2}, 1] -> I Pi}

newgint[poly_, G[y_, var_], var_] := 
 If[y === {}, Integrate[poly, var], 
  With[{hh = Integrate[(poly /. var -> var + First[y]), var]}, 
   Expand[hh /. var -> var - First[y], var] G[y, 
      var] - (hh /. var -> 0) G[y, var] - 
    ngint[Expand[(hh - (hh /. var -> 0))/var, var] /. 
      var -> var - First[y], G[Rest[y], var], var]]]

newgint[inv[var_, x_, deg_], G[y_, var_], var_] :=
 If[deg === 1, G[Prepend[y, x], var],
  1/(1 - deg) If[y === {}, 1/(var - x)^(deg - 1), If[First[y] === x,
     1/(var - x)^(deg - 1) G[y, var] - 
      ngint[inv[var, x, deg], G[Rest[y], var], var],
     1/(var - x)^(deg - 1) G[y, var] - 
      1/(First[y] - x)^(deg - 1) G[y, var] + 
      Total@Array[1/(First[y] - x)^(#) ngint[inv[var, x, deg - #], 
         G[Rest[y], var], var] &, deg - 1]]]]

(* TODO: need a function to apart rational functions *)

(* uplift symbol *)
UpliftSymbol[exp_, vars_] := 
 With[{hh = Select[vars, MemberQ[Variables[GetAlphabet[exp]], #] &], 
   weights = 
    Union@Cases[exp, Tensor[x___] :> Length[{x}], All]},
  Which[
    hh === {}, exp,
    Length[weights] =!= 1, Print["not unit weight"]; Abort[],
    First[weights] == 1 , exp /. Tensor[x_] :> G[{0}, x],
    True, 
    With[{jj = 
       GIntegrate[
        If[Head[#] === Plus, 
           First[AllCases[#, _dlog]] UpliftSymbol[# /. _dlog :>
                  1, vars] & /@ #, 
           First[AllCases[#, _dlog]] UpliftSymbol[# /. _dlog :> 
               1, vars]] &@
         Collect[exp /. Tensor[x___, y_] :> Tensor[x] dlog[y] /. 
           dlog[x_] :> 0 /; FreeQ[x, First[hh]], _dlog], First[hh]]},
     jj + UpliftSymbol[Expand[ExpandTensor[exp - SymbolMap[jj]]], vars]]] /. 
   Pi -> 0]

End[];
EndPackage[];