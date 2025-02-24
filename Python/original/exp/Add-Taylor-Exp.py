# -*- coding: utf-8 -*-
"""
Created on Fri Mar 31 11:28:26 2023

@author: thanh
"""

from sympy import *
import sympy as sympy
import numpy as np
from sympy.plotting import plot
from matplotlib import pyplot as plt 

x = symbols('x')
r = symbols('r')
base = 2
step = 1



delta = log(1+2**x,base)
ddelta = diff(delta,x)

realdeltaxr = log(1+2**(x-r),base)
approxdeltaxr = delta - r*ddelta
errdeltaxr = realdeltaxr - approxdeltaxr 
  

#Experiment: eps = 2^-10, delta = 2^-3

dt = 2**(-3)
eps = 2**(-10)
dtrat = 2**7
numsam = 3000
EM = errdeltaxr.subs({x:0, r: dt}).evalf()
errorbound = EM + (2+dt)*eps


def roundeps(x,e):
    t = np.mod(x,e)
    if t<e/2:
        return x - np.mod(x,e)
    else:
        return x - np.mod(x,e) + e

def phi(x):
    return np.log2(1+2**x)

def dphi(x):
    return (2**x)/((2**x)+1)




sample =  np.zeros(numsam)
aphi =  np.zeros(numsam)
adphi =  np.zeros(numsam)
phitab =  np.zeros(numsam)
phitabround =  np.zeros(numsam)
dphitab =  np.zeros(numsam)
dphitabround =  np.zeros(numsam)
apnotround = np.zeros(numsam)
apround = np.zeros(numsam)
enotround = np.zeros(numsam)
eround = np.zeros(numsam)
rstepi = np.zeros(numsam)
istepi = np.zeros(numsam)
curphi = 1
curdphi = 1/2

for i in range(numsam):
    x = -i*dt/dtrat
    sample[i]= x
    aphi[i]= phi(x)
    if np.mod(i,dtrat)==0:
        phitab[i] = phi(x)
        dphitab[i]= dphi(x)
        curphi = phi(x)
        curdphi = dphi(x)
    else:
        phitab[i] = curphi
        dphitab[i] = curdphi
    phitabround[i] = roundeps(phitab[i],eps) 
    dphitabround[i] = roundeps(dphitab[i],eps) 
    rstepi[i] = dt*np.mod(i,dtrat)/dtrat
    apnotround[i] = phitab[i] - rstepi[i]*dphitab[i]
    enotround[i] = np.abs(apnotround[i] -  aphi[i])
    roundmul = roundeps(rstepi[i]*dphitabround[i],eps)
    apround[i] = phitabround[i] - roundmul
    eround[i] = np.abs(apround[i] -  aphi[i])
    
plt.plot(sample,eround) 
plt.show()

print(np.max(enotround))
print(EM)
print(np.max(eround))
print(errorbound)
    


