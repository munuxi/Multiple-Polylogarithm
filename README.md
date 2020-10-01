# Generalized-Polylogarithm
Generalized Polylogarithm (or Goncharov Polylogarithm) in Mathematica

## License

[The MIT License (MIT)](https://raw.githubusercontent.com/munuxi/Generalized-Polylogarithm/master/LICENSE)


## How to use this code

A numerical realization of generalized polylogarithm (or Goncharov polylogarithm, multiple polylogarithm) in Mathematica based on the algorithm given in this paper [0410259](https://arxiv.org/abs/hep-ph/0410259). These functions are widely used in the calculation of Feynman integrals and amplitudes.

This short code provides a function `numG` to numerically calculate G functions. For example, G_{1,1,1}(2,5.1212,-1,2+I) is given by
```Mathematica
In[1]:= numG[{2,5.1212,-1},2+I]
Out[1]= 4.43252302557497865258394344607843885003788443327544
       +0.38186916230883509304289240286441275884630922141447 I
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

The default precision of `numG` and `numLi` is 50, and one can get a higher precision by adding it manually to functions, for example,
```Mathematica
In[4]:= numG[{2,5.1212,-1},2+I,100]
Out[4]= 4.43252302557497865258394344607843885003788443327543
          99501936807897390588056428463630338755491017776579
       +0.38186916230883509304289240286441275884630922141446
          96181750186091259782290786667944828021776319075942 I
```
However, the determination of the bound of the series (according to a given precision) is based on an empirical formula, and its correctness is not proven.

## Notes

Mulitiple zeta values are not supported.