# -*- coding: utf-8 -*-
"""
Created on Fri Mar 31 11:28:26 2023

@author: thanh
"""

from sympy import *
import sympy as sympy
from sympy.plotting import plot


x = symbols('x')
X = symbols('X')
Y = symbols('Y')
r = symbols('r')
a = symbols('a')
b = symbols('b')


A = symbols('A')
B = symbols('B')
C = symbols('C')
D = symbols('D')



c = symbols('c')
R = symbols('R')
K = symbols('K')

base = 2
step = 1


delta = log(1+2**x,base)

ddelta = diff(delta,x)

realdeltaxr = log(1+2**(x-r),base)

drrealdeltaxr = diff(realdeltaxr,r)

dxrealdeltaxr = diff(realdeltaxr,x)

approxdeltaxr = delta - r*ddelta

errdeltaxr = realdeltaxr - approxdeltaxr 

errdeltaxr = together(errdeltaxr)

errdeltaxR = errdeltaxr.subs(r,R)

eratio = errdeltaxr/errdeltaxR

up = errdeltaxr.subs(2**x,a)
down = errdeltaxR.subs(2**x,a)
dup = diff(up,a)
ddown = diff(down,a)
k = dup/ddown


#l = lim x->-oo of ratio

dxeratio = together(diff(eratio,x))
# dxeratio = A0 * A1 * A2 * A*3 * A4 * A*5
# Ai = dxeratio.args[i] > 0 for i = 0,1,2,3,5
dxerationum4 = dxeratio.args[4]


er = errdeltaxr.args[2]
der = diff(er,x)
eR = errdeltaxR.args[2]
deR = diff(eR,x)

symnum4 = dxerationum4.subs(er,a).subs(eR,b)


fr =  er/der
fr = fr.subs(2**x,A)

dfr=together(diff(fr,r))
dfr=dfr.subs(2**r,B).subs(r*log(2),log(B))
#dfr = dfr0 * dfr1 * dfr2 * dfr3
#sign drf = sign dfr3
dfr3 = expand(dfr.args[3]) #sign dfr3 = -sign dfr, want to prove dfr<0 -> dfr3>0
dfr3 = factor(dfr3)
dfr = dfr.subs(dfr.args[3],dfr3)
#dfr3 = dfr3i * (X+1) * (2^R-1)  ==> sign dfr3 = sign dfr3i
#dfr3i = dfr3.args[0] * dfr3.args[3] #=0 when X=0

K = -dfr.args[5]
H = -dfr/(-K)
M = H.args[2].args[0]
H = H.subs(M,simplify(M))
H = H.subs(log((A+B)/B), log(A+B) - log(B))
M = H.args[1].args[0]
H = H.subs(M,expand(M))

K = K.subs(log(A/B+1), log(A+B)-log(B))
K = expand(K)


dBK = diff(K,B)
d2BK = together(diff(dBK,B))
d2BK2 = simplify(d2BK.args[2])
d2BK = d2BK.subs(d2BK.args[2],d2BK2)


# Theorem 2


Pmin = eratio.subs(x,0)
Psup = (2**-r - 1 + r*log(2))/(2**-R-1+R*log(2))
F = Psup - Pmin
dF = together(diff(F,r))
dF = dF.subs(2**R,X).subs(R*log(2), log(X))
dF = dF.subs(log(1+1/X), log(X+1)-log(X))
dF5 = collect(expand(dF.args[5]),2**r)
dF = dF.subs(dF.args[5], dF5)

K = dF/dF5

A = dF5.args[0].args[1]
B = dF5 -  dF5.args[0]

dA = diff(A)
d2A = simplify(diff(dA))
dB = diff(B)
d2B =  simplify(diff(dB))

H = B + A*X
dH = diff(H)
d2H = diff(dH)
d3H = simplify(together(diff(d2H)))




G = F.subs(2**R,X).subs(R*log(2), log(X)).subs(2**r,Y).subs(r*log(2), log(Y))



eratiosample = eratio.subs(r,0.2).subs(R,1)


p0 = plot(eratiosample, xlim=(-10,-0.1) ,ylim = (0.04, 0.05),ylabel = "Eratio")

p1 = plot(F.subs(R,1),  xlim=(0,1),ylim = (0, 0.08),ylabel = "F(r)", show=False)

#p0 = plot(D.subs(X,0.1), xlim=(0,1),  show=False)
p1.show()
