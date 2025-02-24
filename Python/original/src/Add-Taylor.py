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


def phi(x):
    return np.log2(1+2**x)

def dphi(x):
    return (2**x)/((2**x)+1)


delta = 2**(-3)
eps = 2**(-10)
EM = np.abs(phi(-delta)-(phi(0)-delta*dphi(0)))
errorbound = EM + (2+dt)*eps


    


