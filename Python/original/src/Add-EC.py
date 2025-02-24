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


delta = 2**(-5)
eps = 2**(-8)
deltap = 2^(-7)
c = 4


dt = delta
QS =Qs(dt)
dp=deltap
PM = np.abs(phi(-c*dt-dt+dp) + (dt-dp)*dphi(-c*dt) - phi(-c*dt))
PM=PM/np.abs(phi(-c*dt-dt) + dt*dphi(-c*dt) - phi(-c*dt))
PM = roundeps(PM,eps)
EM = np.abs(phi(-delta)-(phi(0)-delta*dphi(0)))
errorboundEC = (4+dt)*eps + EM*(QS+1-PM+eps)


