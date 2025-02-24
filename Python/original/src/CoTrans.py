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






def roundeps(x,e=eps):
    t = np.mod(x,e)
    if t<e/2:
        return x - np.mod(x,e)
    else:
        return x - np.mod(x,e) + e

def phi(x):
    return np.log2(1-2**x)

def dphi(x):
    return -(2**x)/(1-(2**x))

def rphi(x,e=eps):
    return roundeps(phi(x),eps)

def Qinf(r,dt):
    num = 2**(-r) + r*np.log(2) -1
    den = 2**(-dt) + dt*np.log(2) -1
    return num/den
    
def Qmax(r,dt):
    num =  -r*np.log(2) + np.log(2-2**(-r))    
    den = -dt*np.log(2) + np.log(2-2**(-dt)) 
    return num/den

def root(dt):
    x = 2**dt
    ln2x = np.log(2*x-1)
    lnx = np.log(x)
    num = 2*x*lnx - x*ln2x
    den = 2*x*lnx - 2*x*ln2x + 2*x -2
    return np.log2(num/den)

def Qs(dt):
    rs = root(dt)
    return Qmax(rs,dt) - Qinf(rs,dt)


def divf(x,d):
    q, r = np.divmod(x,d)
    if r==0:
        return (q-1)*d, -d
    return q*d, -r

def breakdown(x,da,db,dc):
    if x>= -db:
        return [1,x,0,0]
    if x>= -dc:
        rb, ra = divf(x,db)
        return [2,ra,rb,0]
    rc, rab = divf(x,dc)
    rb, ra = divf(rab,db)
    return [3, ra,rb,rc]    

def taylorbreak(x,d):
    q,r =  np.divmod(x,d)
    if r == 0:
        return q*d, r
    return (q+1)*d, d-r

def apprphiEC(x,d = dt, c = const, dp =  dtb):
    q, r = taylorbreak(x,d)
    ftaylor = apprphiFT(x,d)
    c = -c * dt
    emaxx = -phi(q) + dt*dphi(q) + phi(q-dt)
    emaxp = -phi(c) + dt*dphi(c) + phi(c-dt)
    qp, rp = taylorbreak(r,dp)
    eqp = -phi(c) + qp*dphi(c) + phi(c-qp)
    erat = roundeps(eqp/emaxp)
    errorcorrection = erat*emaxx
    return ftaylor + errorcorrection

def apprphiFT(x,d = dt):
    q, r = taylorbreak(x,d)
    ftaylor = rphi(q)-roundeps(r*roundeps(dphi(q)))
    #print(x,q,r,ftaylor)
    return ftaylor



def cotransphiEC(x):
    case, ra, rb, rc = breakdown(x,da,db,dc)
    if case == 1:
        return rphi(ra)
    if case == 2:
        k = x + rphi(ra) - rphi(rb)
        #print(k,apprphiEC(k) )
        return apprphiEC(k)+ rphi(rb)
    k1 = rb - ra + rphi(ra) - rphi(rb)
    k2 = x + rphi(rb) - rphi(rc) + apprphiEC(k1)    
    return apprphiEC(k2) + rphi(rc)

def cotransphiFT(x):
    case, ra, rb, rc = breakdown(x,da,db,dc)
    if case == 1:
        return rphi(ra)
    if case == 2:
        k = x + rphi(ra) - rphi(rb)
        return apprphiFT(k)+ rphi(rb)
    k1 = rb - ra + rphi(ra) - rphi(rb)
    k2 = x + rphi(rb) - rphi(rc) + apprphiFT(k1)    
    return apprphiFT(k2) + rphi(rc)


def ECT(E, e =eps):
    u = phi(-1-2*e) - phi(-1) + E
    e1 = e + u
    Ek2 =  2*e + u
    e2  =  e + phi(-1-Ek2) - phi(-1) + E
    v = max(e1,e2)
    #print(E,e1,e2)
    return v
    



#Experiment: eps = 2^-10, delta = 2^-3
eps = 2**(-32)
delta = 2^(-6)
deltap = 2^(-10)
const = 4
sizeA = 2**12
sizeB = 2**10
deltaa = eps*sizeA
deltab = deltab*sizeB




da = eps
db = deltaa
dc = deltab
dt = delta
dp = deltap
QS =Qs(dt)
EM = np.abs(phi(-1-dt) - phi(-1) + dt*dphi(-1))
c = const
PM = np.abs(phi(-c*dt-dt+dp) + (dt-dp)*dphi(-c*dt) - phi(-c*dt))
PM=PM/np.abs(phi(-c*dt-dt) + dt*dphi(-c*dt) - phi(-c*dt))
errorboundFT = EM + (2+dt)*eps  
errorboundCTFT = ECT(errorboundFT,eps)


errorboundEC = (4+dt)*eps + EM*(QS+1-PM+eps)
errorboundCTEC = ECT(errorboundEC,eps)


