# -*- coding: utf-8 -*-
"""
Created on Fri Mar 31 11:28:26 2023

@author: thanh
"""

from sympy import *
import sympy as sympy
from sympy.plotting import plot


x = symbols('x')
r = symbols('r')
a = symbols('a')
b = symbols('b')
c = symbols('c')

base = 2
step = 1


delta = log(1-2**x,base)
ddelta = diff(delta,x)

realdeltaxr = log(1-2**(x-r),base)
approxdeltaxr = delta - r*ddelta
errdeltaxr = -realdeltaxr + approxdeltaxr 

#Summary: 

# errdeltaxr > 0 for all x, r => errdeltaxr = abs(errdeltaxr)    

# drerrdeltaxr  > 0 for all x, r
# => fix x abs(errdeltaxr) maximum when r = R  (step length)

# dxerrdeltaxR < 0 for all x

#errdeltaxr =0 when x->-inf
#errdelaxr  =0 when x->0  ==>errdeltaxr <0 forall x
#proof errdeltaxr > 0 for all x, r:
    
drerrdeltaxr = diff(errdeltaxr,r) #=0 when r=0
dr2errdeltaxr = diff(drerrdeltaxr,r) 
dr2errdeltaxr = together(dr2errdeltaxr)
numdr2errdeltaxr = simplify(dr2errdeltaxr.args[1]) #<0 => drerrdeltaxr <= 0 for all r

errdeltaxr_r0 = errdeltaxr.subs(r,0) #=0


errdeltaxr_x0= errdeltaxr.subs(x,0) #=0

e1 = diff(errdeltaxr_x0,r)
e1_r0 = e1.subs(r,0) #=0   
de1 = diff(e1,r)  #<0
de1 = together(de1)  #<0
errdeltaxr_x0r0 = errdeltaxr_x0.subs(r,0) #=0


errdeltaxr_xi= errdeltaxr.subs(2**x,0) #=0


#eop


    
   
#proof max error

dxerrdeltaxr = together(diff(errdeltaxr,x))

numderror = expand(dxerrdeltaxr.args[2])

exp = expand(numderror/2**x)  #sign exp = sign derror = sign numderror
exp = collect(exp,2**x)  #sign exp2 = sign derror
exp = exp.subs(r*log(2),a)
e= sympy.E
exp = exp.subs(2**r,e**a) #a=r ln2

#proof exp3 < 0

f1 = a*e**-a + e**-a -1  #a=0, f1=0

df1 = diff(f1) #df1 < 0 for all a => f1<0 for all a

f2 = a + e**-a -1 #a=0, f2=0

df2 = diff(f2) #df2 > 0 for all a => f2>0 for all a

#=>  x -> -inf, exp3>0

exp0 = exp.subs(x,0) #=0 when a =0
dexp0 = diff(exp0) # = -f1 >0 ==>exp0>0 ==>exp>0




  

