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
poorsum[mm_,prezz_,preyy_,prec_]:=N[With[{zz=N[Rationalize[prezz,0],2prec],yy=N[Rationalize[preyy,0],2prec],bound=Max[250,2 prec/Log[10,Abs[Min[Abs[prezz]]/preyy]]],len=Length[mm]},(-1)^len Last@Fold[Accumulate[#1(Table[(If[#2===1,yy,zz[[#2-1]]]/zz[[#2]])^(j+len-#2)(j+len-#2)^(-mm[[#2]]),{j,bound}])]&,Accumulate@Table[(zz[[-2]]/zz[[-1]])^j j^(-mm[[-1]]),{j,bound}],Range[Length[mm]-1,1,-1]]],prec]
poorNG[{mm_Integer},{zz_},y_,prec_:50]:=-PolyLog[mm,y/zz]
poorNG[{mm__Integer},{zz__},y_,prec_:50]:=poorsum[{mm},{zz},y,prec]
poorNG[z_List,y_,prec_:50]:=With[{hh=Chop[z]},If[AnyTrue[DeleteCases[hh,0],Abs[y/#]>1&],0,poorNG[Sequence@@(shorthand[hh]),y,prec]]]


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
myG[y1_,b_,z_,y2_,0]:=If[b==={},1,myG[0,{},b,y1,0]]mylog[y2]^Length[z]/Length[z]!/;MatchQ[z,{0..}];
(* ini *)
myG[y1_,b_,z_,y_,0]:=(If[b==={},1,myG[0,{},b,y1,0]]*If[!AnyTrue[DeleteCases[z,0],Abs[#]<Abs[y]&],goodG[z/y,1],With[{pos=First@FirstPosition[Abs[z],Min[Abs[DeleteCases[z,0]]]]},myG[z[[pos]],{},ReplacePart[z,pos->0],y,pos]]])/;Last[z]=!=0
(* remove tail zero *)
myG[y1_,b_,{zz___,0},y2_,w_]:=(myG[y1,b,{zz,0},y2,w]=Expand[With[{z={zz,0}},With[{kk=If[Length[z]-#<w,Length[z]-w,#]&@tailzero[z],len=Length[z]},1/kk (If[y2===1,0,mylog[y2]myG[y1,b,{zz},y2,w]]-Sum[myG[y1,b,Join[z[[1;;m]],{0},z[[m+1;;len-kk-1]],{z[[len-kk]]},ConstantArray[0,kk-1]],y2,If[w!=0&&m<w,w+1,w]],{m,0,len-kk-1}])]]])/;w=!=Length[{zz,0}]
(* special values, assuming dG[1]=log[0]\[Rule]0*)
(* almost all zero, Li *)
myG[y1_,b_,z_,y_,0]:=-If[b==={},1,myG[0,{},b,y1,0]]*myLi[Length[z],y/Last[z]]/;MatchQ[Most[z],{0..}];
myG[y1_,b_,{z_},y_,0]:=If[b==={},1,goodG[b,y1]]*If[y===z,0,mylog[(-y+z)/z]];
myG[y1_,b_,{z1_,z2_},y_,0]:=If[z1===y,-myG[y1,b,{z2,z1},y,0],If[b=={},1,goodG[b,y1]]*(-myLi[2,y/(y-z1)]-myLi[2,y/z2]+myLi[2,y (z1-z2)/((-y+z1) z2)])]/;z2=!=0
(* tail integral var *)
branchmyG[a_,b_,z_,y_,w_,branch_]:=(branchmyG[a,b,z,y,w,branch]=Expand@If[Length[z]===w===1,branchmyG[0,{},Append[b,y],a,0,branch]+mylog[-y,branch]If[b=={},1,branchmyG[0,{},b,a,0,branch]]-branchmyG[0,{},Append[b,0],a,0,branch],If[b=={},1,branchmyG[0,{},b,a,0,branch]](-myzeta[w]+branchmyG[y,{0},ConstantArray[0,w-1],y,w-1,branch])-branchmyG[a,Append[b,0],ConstantArray[0,w-1],y,w-1,branch]])/;MatchQ[z,{0..}]&&w===Length[z]
myG[a_,b_,z_,y_,w_]:=(branchmyG[a,b,z,y,w,Sign[Im[a/y]]]/.branchmyG[p__,q_]:>myG[p])/;MatchQ[z,{0..}]&&w===Length[z]
myG[y1_,b_,z_,y2_,w_]:=(myG[y1,b,z,y2,w]=Expand@With[{tz=tailzero[z]},(myG[0,{},z[[;;w-tz]],y2,0]myG[y1,b,ConstantArray[0,tz],y2,tz])-Total[myG[y1,b,(#/.Infinity->0),y2,First[FirstPosition[#,Infinity]]]&/@Shufflep[z[[;;w-tz]],longhand[{tz},{Infinity}]]]])/;(!MatchQ[z,{0..}])&&w===Length[z]
(* integral var in other pos *)
myG[y1_,b_,z_,y2_,w_]:=(myG[y1,b,z,y2,w]=If[w===1,myG[y1,b,z,y2,0]+myG[y1,Append[b,y2],Delete[z,w],y2,0]+myG[y1,Append[b,z[[w+1]]],Delete[z,w+1],y2,w]-myG[y1,Append[b,z[[w+1]]],Delete[z,w],y2,0],myG[y1,b,z,y2,0]-myG[y1,Append[b,z[[w-1]]],Delete[z,w-1],y2,w-1]+myG[y1,Append[b,z[[w-1]]],Delete[z,w],y2,0]+myG[y1,Append[b,z[[w+1]]],Delete[z,w+1],y2,w]-myG[y1,Append[b,z[[w+1]]],Delete[z,w],y2,0]])/;w!=0&&w!=Length[z]
(* goodG, G functions which can be evaluated by series expansion, assuming dG[1]=log[0]\[Rule]0 *)
goodG[z_,y_]:=goodG[z/y];
(*goodG[z_,1]:=With[{kk=headone[z],len=Length[z]},If[len==1,dG[1],1/kk (dG[1]goodG[Rest[z],1]-Sum[goodG[Join[ConstantArray[1,kk-1],z[[kk+1;;m]],{1},z[[m+1;;]]],1],{m,kk+1,len}])]]/;First[z]===1;*)
goodG[z_]:=With[{kk=headone[z],len=Length[z]},If[len==1,0,1/kk (-Sum[goodG[Join[ConstantArray[1,kk-1],z[[kk+1;;m]],{1},z[[m+1;;]]]],{m,kk+1,len}])]]/;First[z]===1;
goodG[z_]:=-myLi[Length[z],1/Last[z]]/;MatchQ[Most[z],{0..}]/;Last[z]=!=0;
(* acc G, use Hölder convolution to accelerate convergence *)
accG[{z_},prec_:50]:=mylog[(-1+z)/z];
accG[{z1_,z2_},prec_:50]:=-myLi[2,1/(1-z1)]-myLi[2,1/z2]+myLi[2,(z1-z2)/((-1+z1) z2)];
accG[hh_,prec_:50]:=accG[hh,prec]=With[{z=Rationalize[hh,0]},If[AnyTrue[DeleteCases[z,0],Abs[#]<=1.05&],accG[2z,prec]+(-1)^Length[z]accG[2(1-Reverse[z]),prec]+Sum[(-1)^j accG[2(1-Reverse[z[[1;;j]]]),prec]accG[2z[[j+1;;]],prec],{j,1,Length[z]-1}],poorNG[z,1,prec]]];
numG[z_,y_,prec_:50]:=N[If[Rationalize[First[z]/y,0]===1,ComplexInfinity,myG[0,{},Rationalize[z,0],Rationalize[y,0],0]//.{goodG[x_]:>accG[x,prec],myLi->PolyLog,mylog->Log,myzeta->Zeta}],prec];
numLi[m_,x_,prec_:50]:=(-1)^Length[m]numG[longhand[m,Rest[FoldList[#1/#2&,1,x]]],1,prec]
numMZV[m_,prec_:50]:=numLi[m,ConstantArray[1,Length[m]],prec]