import numpy as np
from typing import Callable, TypeAlias
from enum import Enum

Value: TypeAlias = np.ndarray | float
Rounding: TypeAlias = Callable[[Value], Value]

# Enumeration with rounding modes

class RoundingMode(Enum):
    FLOOR = 'floor'
    CEIL = 'ceil'
    NEAREST = 'nearest'
    FAITHFUL = 'faithful'

def max_err(exact: Value, approx: Value) -> float:
    return np.max(np.abs(exact - approx))

def avg_abs_err(exact: Value, approx: Value) -> float:
    return np.average(np.abs(exact - approx))

def avg_err(exact: Value, approx: Value) -> float:
    return np.abs(np.average(exact - approx))

def fix_rnd(prec: float, mode: RoundingMode = RoundingMode.NEAREST) -> Rounding: 
    match mode:
        case RoundingMode.FLOOR:
            return lambda xs: np.floor(xs * (1 / prec)) * prec
        case RoundingMode.CEIL:
            return lambda xs: np.ceil(xs * (1 / prec)) * prec
        case RoundingMode.NEAREST:
            return lambda xs: np.round(xs * (1 / prec)) * prec
        case RoundingMode.FAITHFUL:
            # Use floor for the faithful rounding
            return lambda xs: np.floor(xs * (1 / prec)) * prec
        case _:
            raise ValueError(f'fix_rnd: unknown rounding mode {mode}')

# Φp and Φm and their derivatives

def phi_add(xs: Value) -> Value:
    return np.log2(1 + 2 ** xs)

def dphi_add(xs: Value) -> Value:
    return 2 ** xs / (2 ** xs + 1)

def phi_sub(xs: Value) -> Value:
    return np.log2(1 - 2 ** xs)

def dphi_sub(xs: Value) -> Value:
    return 2 ** xs / (2 ** xs - 1)

# First-order taylor approximations

def taylor_add(delta: float, xs: Value) -> Value:
    if np.any(xs > 0):
        raise ValueError('taylor_add: xs > 0')
    ns = np.ceil(xs / delta) * delta
    rs = ns - xs
    return phi_add(ns) - rs * dphi_add(ns)

# ΦTp_fix
def taylor_add_rnd(rnd: Rounding, delta: float, xs: Value) -> Value:
    if np.any(xs > 0):
        raise ValueError('taylor_add_rnd: xs > 0')
    ns = np.ceil(xs / delta) * delta
    rs = ns - xs
    return rnd(phi_add(ns)) - rnd(rs * rnd(dphi_add(ns)))

# Ep
def taylor_add_err(i: Value, r: Value) -> Value:
    return phi_add(i - r) - phi_add(i) + r * dphi_add(i)

# Ep_fix
def taylor_add_err_rnd(rnd: Rounding, i: Value, r: Value) -> Value:
    return phi_add(i - r) - rnd(phi_add(i)) + rnd(r * rnd(dphi_add(i)))

def taylor_add_err_bound(delta: float) -> float:
    return taylor_add_err(0, delta)

def taylor_sub(delta: float, xs: Value) -> Value:
    if np.any(xs > -1):
        raise ValueError('taylor_sub: xs > -1')
    ns = np.ceil(xs / delta) * delta
    rs = ns - xs
    return phi_sub(ns) - rs * dphi_sub(ns)

# ΦTm_fix
def taylor_sub_rnd(rnd: Rounding, delta: float, xs: Value) -> Value:
    if np.any(xs > -1):
        raise ValueError('taylor_sub_rnd: xs > -1')
    ns = np.ceil(xs / delta) * delta
    rs = ns - xs
    return rnd(phi_sub(ns)) - rnd(rs * rnd(dphi_sub(ns)))

# Em
def taylor_sub_err(i: Value, r: Value) -> Value:
    return -phi_sub(i - r) + phi_sub(i) - r * dphi_sub(i)

# Em_fix
def taylor_sub_err_rnd(rnd: Rounding, i: Value, r: Value) -> Value:
    return phi_sub(i - r) - rnd(phi_sub(i)) + rnd(r * rnd(dphi_sub(i)))

def taylor_sub_err_bound(delta: float) -> float:
    return taylor_sub_err(-1, delta)

# Error-correction techniques

# Qp
def q_add(delta: float, i: Value, r: Value) -> Value:
    return taylor_add_err(i, r) / taylor_add_err(i, delta)

# Qp_lo
def q_add_lo(delta: float, r: Value) -> Value:
    return q_add(delta, 0, r)

# Qp_hi
def q_add_hi(delta: float, r: Value) -> Value:
    return (2 ** -r + r * np.log(2) - 1) / (2 ** -delta + delta * np.log(2) - 1)

# Rp_opt
def r_add_opt(delta: float) -> float:
    x = 2 ** delta
    return np.log2(x * (2 * np.log(x + 1) - np.log(x) - 2 * np.log(2)) / (-2 * x * (np.log(x + 1) - np.log(x) - np.log(2)) - x + 1))

# QRp
def q_add_range_bound(delta: float) -> float:
    r = r_add_opt(delta)
    return q_add_hi(delta, r) - q_add_lo(delta, r)

# QIp
def q_add_approx_bound(delta: float, delta_p: float) -> float:
    return 1 - q_add_lo(delta, delta - delta_p)

# ΦECp_fix
def ec_add_rnd(rnd: Rounding, delta: float, delta_p: float, c: float, xs: Value) -> Value:
    if np.any(xs > 0):
        raise ValueError('ec_add_rnd: xs > 0')
    ns = np.ceil(xs / delta) * delta
    rs = ns - xs
    ec = rnd(rnd(taylor_add_err(ns, delta)) * rnd(q_add(delta, c, np.floor(rs / delta_p) * delta_p)))
    return rnd(phi_add(ns)) - rnd(rs * rnd(dphi_add(ns))) + ec

# Co-transformations

def ind(delta: float, xs: Value) -> Value:
    return (np.ceil(xs / delta) - 1) * delta

def rem(delta: float, xs: Value) -> Value:
    return ind(delta, xs) - xs

def kval(delta: float, xs: Value) -> Value:
    return xs - phi_sub(ind(delta, xs)) + phi_sub(rem(delta, xs))

def k_rnd(rnd: Rounding, delta: float, xs: Value) -> Value:
    return xs - rnd(phi_sub(ind(delta, xs))) + rnd(phi_sub(rem(delta, xs)))

def cotrans2(delta: float, da: float, xs: Value) -> Value:
    return phi_sub(ind(da, xs)) + taylor_sub(delta, kval(da, xs))

def cotrans2_rnd(rnd: Rounding, delta: float, da: float, xs: Value) -> Value:
    return rnd(phi_sub(ind(da, xs))) + taylor_sub_rnd(rnd, delta, k_rnd(rnd, da, xs))

def cotrans3(delta: float, da: float, db: float, xs: Value) -> Value:
    return phi_sub(ind(db, xs)) + taylor_sub(delta, kval(db, xs))

def cotrans3_rnd(rnd: Rounding, delta: float, da: float, db: float, xs: Value) -> Value:
    rab = rem(db, xs)
    res = np.zeros(len(xs))
    special = rab >= -da
    incl = rab < -da
    rab, xs, ys = rab[incl], xs[incl], xs[special]
    rb = ind(da, rab)
    k1 = k_rnd(rnd, da, rab)
    k2 = xs + rnd(phi_sub(rb)) + taylor_sub_rnd(rnd, delta, k1) - rnd(phi_sub(ind(db, xs)))
    res[incl] = rnd(phi_sub(ind(db, xs))) + taylor_sub_rnd(rnd, delta, k2)
    res[special] = cotrans2_rnd(rnd, delta, db, ys)
    return res


