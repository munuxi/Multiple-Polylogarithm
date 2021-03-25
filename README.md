# Multiple Polylogarithm
Numerical Multiple Polylogarithm (or Generalized Polylogarithm, Goncharov Polylogarithm) in Mathematica

## License

[The MIT License (MIT)](https://raw.githubusercontent.com/munuxi/Generalized-Polylogarithm/master/LICENSE)

## How to use this code

### Numerical evaluations of multiple polylogarithms

A numerical realization of multiple polylogarithm (or Goncharov polylogarithm, generalized polylogarithm) in pure Mathematica based on the algorithm given in this paper [0410259](https://arxiv.org/abs/hep-ph/0410259). These polylogarithms are widely used in the calculation of Feynman integrals and amplitudes.

This short code provides a function `MPLG` to numerically calculate multiple polylogarithms. For example,
```Mathematica
In[1]:= MPLG[{2,5,-1},2+I]
Out[1]= MPLG[{2,5,-1},2+I]

In[2]:= MPLG[{2,5.1212,-1},2+I]
Out[2]= -0.224143+0.190784 I

In[3]:= N[MPLG[{2,5,-1},2+I],50]
Out[3]= -0.23167350662300578240105093305732823163512296305387
        +0.19529344255704520149638632931648075752227244885098 I

(* we can even do numerical integration *)

In[4]:= NIntegrate[MPLG[{0,1,0},x]/(x-Pi),{x,1/3,1/2},WorkingPrecision->20]
Out[4]= -0.079243361725535382729

In[5]:= N[MPLG[{Pi, 0, 1, 0}, 1/2] - MPLG[{Pi, 0, 1, 0}, 1/3], 20]
Out[5]= -0.079243361725535382729
```

However, the determination of the bound of the series (according to a given precision) in this code is based on an empirical formula, and its correctness is not proven.

A related function `numLi` can be used to calculate multiple Li functions Li_{a1,...,an}(z1,...,zn), for example 
```Mathematica
In[6]:= numLi[{4,3},{10,-5}]
Out[6]= - 2.9589260121255572590640327182307418000466293019986040673168 + 
         22.6122376480634386402336378167074133584999533678250847235297 I

(* check an identity *)

In[3]:= numLi[{4},{10}]numLi[{3},{-5}]-(numLi[{4,3},{10,-5}]+numLi[{3,4},{-5,10}]+numLi[{7},{-50}])
Out[3]= 0.*10^-48+0.*10^-48 I
```
and Multiple Zeta Value `numMZV[{m1,...,mn}]` is simply given by `numLi[{m1,...,mn},{1,...,1}]`.

The default precision of `numLi` is 50, and one can get a higher precision by adding it manually to functions, for example,
```Mathematica
In[7]:= numLi[{4,3},{10,-5},100]
Out[7]= - 2.9589260121255572590640327182307418000466293019986
            0406731684237589601496921051562174171870886557715
        + 22.612237648063438640233637816707413358499953367825
           08472352973908023876385168646607931361692977597799 I
```

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

However, G({a1(0),...,an(0)},z) usually diverges when a1(0)=z or an(0)=0, we use the 
shuffle regularization used in [1403.3385](https://arxiv.org/abs/1403.3385) to get the finite result. 

What's more, we can first assume that t is a very small positive number such that 
the integral will never meet nonzero singularities. After getting the answer, we could
use analytic continuation to fix the answer in other regions, where one should add 
option fitting values `"FitValue"` to tell the code the region.

In this code, this is done by a function `MoveVar[Gfuncs,var,"FitValue"->{something}]`. 
`"FitValue"` are very important for the choice of branches. If there's no `"FitValue"`, 
one can get a result, but it is usually not correct. For example,
```Mathematica
(* an example with and without FitValue *)

In[8]:= MoveVar[G[{1/2-a t},1],t]

Out[8]= I Pi+G[{-(1/(2 a))},t]-G[{1/(2 a)},t]

In[9]:= MoveVar[G[{1/2-a t},1],t,"FitValue"->{a->-2}]

Out[9]= -I Pi+G[{-(1/(2 a))},t]-G[{1/(2 a)},t]

(* check *)

In[10]:= (%8 - G[{1/2-a t},1])/.{t->10,a->-2}/.G->MPLG//N

Out[10]= -2.35922*10^-16+6.28319 I

In[11]:= (%9 - G[{1/2-a t},1])/.{t->10,a->-2}/.G->MPLG//N[#,50]&

Out[11]= 0.*10^-99
```

One-dimensional integrals are simply done by `GIntegrate`:
```Mathematica
In[12]:= temp = 1/3 Pi^2 G[{w/v}, 1] + G[{-1}, v] G[{0}, w] G[{w/v}, 1] - 
                G[{0}, v] G[{0}, w] G[{w/v}, 1] + G[{w/v}, 1] G[{-1, 0}, v] - 
                G[{w/v}, 1] G[{0, -1}, v] + G[{0}, v] G[{0, -w}, 1] + 
                G[{0}, w] G[{0, -w}, 1] - G[{-1}, v] G[{w/v, 0}, 1] + 
                G[{0}, v] G[{w/v, 0}, 1] - G[{0}, v] G[{w/v, -w}, 1] - 
                G[{0}, w] G[{w/v, -w}, 1] + G[{0, 0, -w}, 1] - G[{0, -w, 0}, 1] -
                 G[{w/v, 0, -w}, 1] + G[{w/v, -w, 0}, 1] /. {w -> w, v -> v/t} //
               Simplify;
         result = GIntegrate[temp dlog[t], {t, 0, 1}, "FitValue"->{v -> 1/10, w -> 1/20}]

Out[13]= G[{0}, w] G[{-w}, 1] G[{0, -v}, 1] + 
         G[{1/(1 - v)}, 1] G[{-w}, 1] G[{0, -v}, 1] + 
         1/3 Pi^2 G[{0, v/w}, 1] + G[{1/(1 - v)}, 1]^2 G[{0, v/w}, 1] - 
         G[{0}, w] G[{-w}, 1] G[{0, v/w}, 1] - 
         G[{1/(1 - v)}, 1] G[{-w}, 1] G[{0, v/w}, 1] + 
         2 G[{0, 1}, 1] G[{0, v/w}, 1] - 
         2 G[{0, 1/(1 - v)}, 1] G[{0, v/w}, 1] + 
         G[{0, -v}, 1] G[{0, -w}, 1] - 2 G[{0, v/w}, 1] G[{0, -w}, 1] - 
         2 G[{0, v/w}, 1] G[{1/(1 - v), 1}, 1] - G[{0}, w] G[{0, 0, -v}, 1] - 
         G[{1/(1 - v)}, 1] G[{0, 0, -v}, 1] - G[{-w}, 1] G[{0, -v, 0}, 1] + 
         G[{-w}, 1] G[{0, v/w, 0}, 1] + G[{0}, w] G[{0, v/w, -v}, 1] + 
         G[{1/(1 - v)}, 1] G[{0, v/w, -v}, 1] - G[{0, 0, 0, -v}, 1] + 
         G[{0, 0, -v, 0}, 1] + G[{0, v/w, 0, -v}, 1] - G[{0, v/w, -v, 0}, 1]

In[14]:= NIntegrate[N[D[Log[t],t](temp/.{v->1/10, w->1/20}/.G->MPLG)], {t,10^-10,1-10^-10}]

Out[14]= -2.24909 + 7.87923*10^-13 I

In[15]:= result /. {v -> 1/10, w -> 1/20} /. G -> MPLG // N

Out[15]= -2.24909
```
(The above example comes form the calculation of a 2D double-pentagon integral.)

## Notes

### Performance

It's not a very efficient realization. We could calculate some examples by Ginac (via Ginsh) as a comparison. 

Platform: Mathematica (12.1.1.0) on Windows 10 x86-64 (Build 20201), and Ginsh on WSL 1. They use the same CPU (i7-8700). Ginsh will take a short time on IO.

- `N[MPLG[{1, 2, 3, 4, 5}, 6], 100]` will take ~1.2s, and Ginac will take ~1.3s
- `N[MPLG[{5, 4, 3, 2, 1}, 6], 100]` will take ~1.2s, and Ginac will take ~64s (???)
- `N[MPLG[{1, 2, 3, 4, 5, 6}, 7], 100]` will take ~3.9s, and Ginac will take ~7s 
- `N[MPLG[{1, 2, 3, 4, 5, 6, 7}, 8], 100]` will take ~10s, and Ginac will take ~40s

It's much slower when there're non-rational numbers, but Ginac doesn't care it. It's really important to speed up the sum of lots of float numbers for the series calculation.
It's also possible to speed up recursions. For example, `MPLG[{1, 2, 3, 4, 5}, 6, 100]` and `MPLG[{1, 2, 3, 4, 5}, 7, 100]` share the same recursions (with different numbers), so a more efficient code should learn to recognize it.

### Cross the Branch Cut

In our realization of `MoveVar`, we consider the choice of branch by assuming the variable t to be a positive number with a infinitesimal negative imaginary part. If `t-i0 -> t+i0` doesn't cross the branch cut of the function, the result of `MoveVar` doesn't care about the infinitesimal imaginary part. Otherwise, the result of `MoveVar` is on the `t-i0` side. For example, 
```Mathematica
In[16]:= MoveVar[G[{t}, 2], t]

Out[16]= -G[{0}, t] - G[{2/3}, 1] + G[{2}, t]

In[17]:= %16 /. t -> (1/10) /. G -> MPLG // N

Out[17]= 2.94444 - 3.14159 I

In[18]:= G[{t}, 2] /. t -> (1/10) /. G -> MPLG // N

Out[18]= 2.94444 + 3.14159 I

In[19]:= G[{t}, 2] /. t -> (1/10-10^-50I) /. G -> MPLG // N

Out[19]= 2.94444 - 3.14159 I
```
It's not wrong and rare in practice, but also annoying if someone doesn't notice it.

## Related Packages

It seems that [Ginac](https://ginac.de/) (in C++) is the only software provides numerical evaluations of all known polylogarithms.

[PolyLogTools](https://arxiv.org/abs/1904.07279) use Ginac as its backend to support numerical evaluations.

For harmonic polylogarithms, [HPL](https://arxiv.org/abs/hep-ph/0507152) is a very useful package in Mathematica.

[HyperInt](https://bitbucket.org/PanzerErik/hyperint/wiki/Home) in Maple is another well-known and powerful package in Feynman integrals calculation and integrations of polylogarithm, but it cannot do numerical evaluations.
