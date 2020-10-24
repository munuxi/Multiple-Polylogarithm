# Multiple Polylogarithm
Numerical Multiple Polylogarithm (or Generalized Polylogarithm, Goncharov Polylogarithm) in Mathematica

## License

[The MIT License (MIT)](https://raw.githubusercontent.com/munuxi/Generalized-Polylogarithm/master/LICENSE)

## How to use this code

### Numerical evaluations of multiple polylogarithms

A numerical realization of multiple polylogarithm (or Goncharov polylogarithm, generalized polylogarithm) in pure Mathematica based on the algorithm given in this paper [0410259](https://arxiv.org/abs/hep-ph/0410259). These polylogarithms are widely used in the calculation of Feynman integrals and amplitudes.

This short code provides a function `numG` to numerically calculate multiple polylogarithms. For example, G_{1,1,1}(2,5.1212,-1,2+I) is given by
```Mathematica
In[1]:= numG[{2,5.1212,-1},2+I]
Out[1]= -0.22414260773807870769808034254340050458793786499014 + 
         0.19078434730044807965215134847688913260135197911168 I
```
A related function `numLi` can be used to calculate multiple Li functions Li_{a1,...,an}(z1,...,zn), for example 
```Mathematica
In[2]:= numLi[{4,3},{10,-5}]
Out[2]= - 2.9589260121255572590640327182307418000466293019986040673168 + 
         22.6122376480634386402336378167074133584999533678250847235297 I

(* check an identity *)

In[3]:= numLi[{4},{10}]numLi[{3},{-5}]-(numLi[{4,3},{10,-5}]+numLi[{3,4},{-5,10}]+numLi[{7},{-50}])
Out[3]= 0.*10^-58 + 0.*10^-58 I
```
and Multiple Zeta Value `numMZV[{m1,...,mn}]` is simply given by `numLi[{m1,...,mn},{1,...,1}]`.

The default precision of `numG` and `numLi` is 50, and one can get a higher precision by adding it manually to functions, for example,
```Mathematica
In[4]:= numG[{2,5.1212,-1},2+I,100]
Out[4]= -0.22414260773807870769808034254340050458793786499014
           17236003391038022863773587694654849571042358585353 + 
         0.19078434730044807965215134847688913260135197911168
           20844226004116650659596789737133041661049519961099 I
```
However, the determination of the bound of the series (according to a given precision) is based on an empirical formula, and its correctness is not proven.

### One-dimensional Integral

Suppose we have a function G({a1(t),...,an(t)},z), we want to rewrite it into a sum of 
constants and G functions with the from
    G({b1,...,bn},t),
where bi is free of t. Then we can calcluate the 1d integral 
```
  int dt/(t-b0) G({a1(t),...,an(t)},z)
```
from the definition of G function. 

This reduction can be done if z-a1, ai-ai+1, an, an-z are all linear reducible in t,
i.e. they are products of linear functions of t. The algorithm is based on the 
Newton-Leibniz formula
```
  G({a1(t),...,an(t)},z) = G({a1(0),...,an(0)},z) + int_0^t dt1 partial_t1 
                                                           G({a1(t1),...,an(t1)},z)
```
and (from the definition of G function)
```
  dt1 partial_t1 G({a1(t1),...,an(t1)},z) 
                                  = dlog(z-a1)G({a2,...,an},z)+...+
                                    dlog(ai-ai+1)G({a1,...,\hat{ai+1},...,an},z)-
                                    dlog(ai-ai+1)G({a1,...,\hat{ai},...,an},z)+...+
                                    -dlog(an)G({a1,...,an-1},z),
```
Finally, we reduce it to 
```
  G({an},z) = log(1-z/an) = log(c) + sum_i n_i log(1-t/c_i) 
                          = log(c) + sum_i n_i G(ci,t), ....................... (1)
```
and then we can calculate all remaining integral 
```
  int dlog(t1-b1)dlog(t2-b1)...dlog(t(n-1)-b(n-1))G(ci,t) = G({b1,...,b(n-1),ci},t)
```
from the definition of G function. 

However, G({a1(0),...,an(0)},z) usually diverges when a1(0)=1 or an(0)=0, we use the 
shuffle regularization used in [1403.3385](https://arxiv.org/abs/1403.3385) to get the finite result. On the other hand,
eq.(1) usually depands on the branch you choice, otherwise we can only get a 
funtion with the same symbol. The other steps are all algebraic, so if (1) is correct 
(on a given region), the whole reduction is correct (on the given region). In our 
realization, one could add fitting values to support numerical checks of eq.(1) 
in the recursion, otherwise it will not check (1).

In the code, this is done by a function `MoveVar[Gfuncs,var,FitValues]`. For example,
```Mathematica
In[5]:= MoveVar[G[{a, b}, 1/t] + G[{1 - c t}, 1], t]

Out[5]= -I Pi+G[{0},t]-I Pi G[{0},t]+I Pi G[{1/a},t]-G[{1/c},t]+G[{0,0},t]-G[{0,1/b},t]
        -G[{1/a,0},t]+G[{1/a,1/b},t]-G[{a/(1+a),1},1]+G[{a/(1+a),b/(1+b)},1]+
         G[{b/(1+b),1},1]-G[{0},t] Log[1/b]+G[{1/a},t] Log[1/b]+Log[c]

In[6]:= MoveVar[G[{a,b},1/t]+G[{1-c t},1],t,{t->10,c->-1,a->3,b->1/5}]

Out[6]= -I Pi+G[{0},t]+I Pi G[{0},t]-I Pi G[{1/a},t]-G[{1/c},t]+G[{0,0},t]-G[{0,1/b},t]
        -G[{1/a,0},t]+G[{1/a,1/b},t]-G[{a/(1+a),1},1]+G[{a/(1+a),b/(1+b)},1]+
         G[{b/(1+b),1},1]-G[{0},t] Log[1/b]+G[{1/a},t] Log[1/b]+Log[c]
```
`FitValues` are very important for the choice of branches. If there's no `FitValues`, 
one can get a result, but it is usually not correct.



## Notes

It's not a very efficient realization. We could calculate some examples by Ginac (via Ginsh) as a comparison. 

Platform: Mathematica (12.1.1.0) on Windows 10 x86-64 (Build 20201), and Ginsh on WSL 1. They use the same CPU (i7-8700). Ginsh will take a short time on IO.

- `numG[{1, 2, 3, 4, 5}, 6, 100]` will take ~1.2s, and Ginac will take ~1.3s
- `numG[{5, 4, 3, 2, 1}, 6, 100]` will take ~1.2s, and Ginac will take ~64s (???)
- `numG[{1, 2, 3, 4, 5, 6}, 7, 100]` will take ~3.9s, and Ginac will take ~7s 
- `numG[{1, 2, 3, 4, 5, 6, 7}, 8, 100]` will take ~10s, and Ginac will take ~40s

It's much slower when there're non-rational numbers, but Ginac doesn't care it. It's really important to speed up the sum of lots of float numbers for the series calculation.

It's possible to speed up recursions. For example, `numG[{1, 2, 3, 4, 5}, 6, 100]` and `numG[{1, 2, 3, 4, 5}, 6, 100]` share the same recursions (with different numbers), so a more efficient code should learn to recognize it.

## Related Packages

It seems that [Ginac](https://ginac.de/) (in C++) is the only software provides numerical evaluations of all known polylogarithms.

[PolyLogTools](https://arxiv.org/abs/1904.07279) use Ginac as its backend to support numerical evaluations.

For harmonic polylogarithms, [HPL](https://arxiv.org/abs/hep-ph/0507152) is a very useful package in Mathematica.

[HyperInt](https://bitbucket.org/PanzerErik/hyperint/wiki/Home) in Maple is another well-known and powerful package in Feynman integrals calculation and integraltions of polylogarithm, but it cannot do numerical evaluations.
