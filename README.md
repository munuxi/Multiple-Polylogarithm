# Multiple Polylogarithm
Numerical Multiple Polylogarithm (or Generalized Polylogarithm, Goncharov Polylogarithm) in Mathematica

## License

[The MIT License (MIT)](https://raw.githubusercontent.com/munuxi/Generalized-Polylogarithm/master/LICENSE)

## How to use this code

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
Out[2]= -2.95892601212555725906403271823074180004662930199860407
        +22.6122376480634386402336378167074133584999533678250847235297390802388 I

(* check an identity *)

In[3]:= numLi[{4},{10}]numLi[{3},{-5}]-(numLi[{4,3},{10,-5}]+numLi[{3,4},{-5,10}]+numLi[{7},{-50}])
Out[3]= 0.*10^-54+0.*10^-68 I
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

## Notes

It's not a very efficient realization. We could calculate some examples by Ginac (via Ginsh) as a comparison. 

Platform: Mathematica (12.1.1.0) on Windows 10 x86-64 (Build 20201), and Ginsh on WSL 1. They use the same CPU (i7-8700).

- `numG[{1, 2, 3, 4, 5}, 6, 100]` will take ~2.5s, and Ginac will take ~1.3s
- `numG[{5, 4, 3, 2, 1}, 6, 100]` will take ~2.5s, and Ginac will take ~64s (???)
- `numG[{1, 2, 3, 4, 5, 6}, 7, 100]` will take ~13s, and Ginac will take ~7s 
- `numG[{1, 2, 3, 4, 5, 6, 7}, 8, 100]` will take ~60s, and Ginac will take ~40s

Usually, recursions are much faster than massive numerical evaluations of series, so it's important to speed up series evaluations in a more efficient realization.

## Related Packages

It seems that [Ginac](https://ginac.de/) (in C++) is the only software provides numerical evaluations of all known polylogarithms.

[PolyLogTools](https://arxiv.org/abs/1904.07279) use Ginac as its backend to support numerical evaluations.

For harmonic polylogarithms, [HPL](https://arxiv.org/abs/hep-ph/0507152) is a very useful package in Mathematica.

[HyperInt](https://bitbucket.org/PanzerErik/hyperint/wiki/Home) in Maple is another well-known and powerful package in Feynman integrals calculation, but I don't know whether it can do numerical evaluations.
