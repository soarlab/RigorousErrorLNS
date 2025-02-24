### Formal proofs of rigorous error bounds for Logarithmic Number Systems

This repository contains [Lean4](https://docs.lean-lang.org/lean4/doc/quickstart.html) proofs of error bounds for Logarithmic Number Systems (LNS) presented in the arXiv preprint [*Rigorous Error Analysis for Logarithmic Number Systems*](https://arxiv.org/abs/2401.17184).

### Proof files

All proof files are located in the [LNS](LNS) directory.

#### Main definitions and results

[`Definitions.lean`](LNS/Definitions.lean) All definitions which are used in the main results.  
[`Audit.lean`](LNS/Audit.lean) All main results in one file. See [`ErrTaylor.lean`](LNS/ErrTaylor.lean), [`Theorem68.lean`](LNS/Theorem68.lean) and [`Cotransformation.lean`](LNS/Cotransformation.lean) for other important results.

#### General results

[`Tactic.lean`](LNS/Tactic.lean) A tactic for computing derivatives.  
[`Common.lean`](LNS/Common.lean) Some general lemmas.  
[`BasicRounding.lean`](LNS/BasicRounding.lean) Basic properties of fixed-point rounding and approximations of functions.  
[`BasicIxRx.lean`](LNS/BasicIxRx.lean) Basic properties of index functions `Iₓ`, `Rₓ`, `ind` and `rem`.  
[`BasicPhi.lean`](LNS/BasicPhi.lean) Basic properties of `Φ⁺` and `Φ⁻`.  

#### Formal proofs of error bounds of first-order Taylor approximations

[`BasicErrTaylor.lean`](LNS/BasicErrTaylor.lean) Basic properties of first-order Taylor error functions `Ep` and `Em` and their error bounds.  
[`ErrTaylor.lean`](LNS/ErrTaylor.lean) Total error bounds of rounded first-order Taylor approximations of `Φ⁺` and `Φ⁻`.

#### Formal proofs of the error correction technique

[`BasicErrCorrection.lean`](LNS/BasicErrCorrection.lean) Basic properties of error correction functions `Qp` and `Qm` and related functions.  
[`Lemma61.lean`](LNS/Lemma61.lean) Limits of `Qp` and `Qm`.  
[`Lemma62.lean`](LNS/Lemma62.lean) Monotonicity of `Qp`.  
[`Lemma63.lean`](LNS/Lemma63.lean) An upper bound of the range of `Qp`.  
[`Lemma64.lean`](LNS/Lemma64.lean) An error bound of the index error of `Qp`.  
[`Lemma65.lean`](LNS/Lemma65.lean) Monotonicity of `Qm`.  
[`Lemma66.lean`](LNS/Lemma66.lean) An upper bound of the range of `Qm`.  
[`Lemma67.lean`](LNS/Lemma67.lean) An error bound of the index error of `Qm`.  
[`Theorem68.lean`](LNS/Theorem68.lean) Total error bounds of rounded error correction approximations of `Φ⁺` and `Φ⁻`.

#### Formal proofs of the cotransformation technique

[`BasicCotrans.lean`](LNS/BasicCotrans.lean) Basic properties of the cotransformation technique.  
[`Cotransformation.lean`](LNS/Cotransformation.lean) Total error bounds of rounded cotransformation approximations of `Φ⁻`.



