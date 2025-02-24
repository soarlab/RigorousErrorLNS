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



#Experiment: eps = 2^-10, delta = 2^-3
edt = -4
dt = 2**edt
eps = 2**(-8)
dtrat = 2**4
numsam = 3*dtrat*(2**(-edt))
nump = 2**4
prat=1 #dtrat/nump
c = 4



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


def Qsup(r,dt):
    num = 2**(-r) + r*np.log(2) -1
    den = 2**(-dt) + dt*np.log(2) -1
    return num/den
    
def Qmin(r,dt):
    num =  (r-2)*np.log(2) + 2*np.log(1+2**(-r))    
    den = (dt-2)*np.log(2) + 2*np.log(1+2**(-dt)) 
    return num/den

def root(dt):
    x = 2**dt
    lnx1 = np.log(x+1)
    lnx = np.log(x)
    l2 = np.log(2)
    num = -x*(2*lnx1-lnx-2*l2)
    den = 2*x*(lnx1-lnx-l2)+x-1
    return np.log2(num/den)

def Qs(dt):
    rs = root(dt)
    return Qsup(rs,dt) - Qmin(rs,dt)



sample =  np.zeros(numsam)
aphi =  np.zeros(numsam)


phitab =  np.zeros(numsam)
phitabround =  np.zeros(numsam)
dphitab =  np.zeros(numsam)
dphitabround =  np.zeros(numsam)
emaxtab = np.zeros(numsam)
emaxtabround = np.zeros(numsam)
ptab = np.zeros(numsam)
ptabround = np.zeros(numsam)

taylor = np.zeros(numsam)
taylorround = np.zeros(numsam)
etaylor = np.zeros(numsam)
tptab = np.zeros(numsam)

apnotround = np.zeros(numsam)
apround = np.zeros(numsam)
enotround = np.zeros(numsam)
eround = np.zeros(numsam)
etaylor = np.zeros(numsam)
etaylorround = np.zeros(numsam)


rstepi = np.zeros(numsam)

curphi = 1
curdphi = 1/2
curmax = 1

for i in range(numsam):
    x = -i*dt/dtrat
    sample[i]= x
    aphi[i]= phi(x)
    if np.mod(i,dtrat)==0:
        phitab[i] = phi(x)
        dphitab[i]= dphi(x)
        curphi = phi(x)
        curdphi = dphi(x)
        curmax  = np.abs(curphi - dt*curdphi - phi(x-dt))
    else:
        phitab[i] = curphi
        dphitab[i] = curdphi
    phitabround[i] = roundeps(phitab[i],eps) 
    dphitabround[i] = roundeps(dphitab[i],eps)
    emaxtab[i] = curmax
    emaxtabround[i] = roundeps(emaxtab[i],eps)
    rstepi[i] = dt*np.mod(i,dtrat)/dtrat
    taylor[i] = phitab[i] - rstepi[i]*dphitab[i]
    etaylor[i] = np.abs(taylor[i] -  aphi[i])
    tptab[i] = etaylor[i]/emaxtab[i]


for i in range(numsam):
    ri = np.mod(i,dtrat)
    ptab[i] = tptab[c*dtrat + ri - np.mod(ri,prat)]
    ptabround[i] = roundeps(ptab[i],eps)
    
    

for i in range(numsam):    
    ec = emaxtab[i]*ptab[i]
    apnotround[i] = taylor[i] + ec 
    enotround[i] = np.abs(apnotround[i] -  aphi[i])
    roundmul = roundeps(rstepi[i]*dphitabround[i],eps)
    taylorround[i] = phitabround[i] - roundmul
    etaylorround[i] = np.abs(taylorround[i]-aphi[i])
    roundec = roundeps(emaxtabround[i]*ptabround[i],eps)
    apround[i] = taylorround[i] + roundec
    eround[i] = np.abs(apround[i] -  aphi[i])
    
plt.plot(sample,ptab) 
plt.show()

QS =Qs(dt)
PM = ptab[dtrat-1]
dp=dt/nump
PM = np.max(ptabround)
EM = emaxtab[0]
errorboundtaylor = EM + (2+dt)*eps  
errorboundEC = (4+dt)*eps + EM*(QS+1-PM+eps)


print(errorboundtaylor)
print(np.max(etaylorround))


print(errorboundEC)   
print(np.max(eround))

