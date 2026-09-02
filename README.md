# lean-csp-prover

A translation of [CSP-Prover](https://github.com/yoshinao-isobe/CSP-Prover) — an interactive theorem prover for refinement proofs in the process algebra CSP — from Isabelle/HOL to **Lean 4 + Mathlib**.

CSP-Prover was developed by Yoshinao Isobe (AIST, Japan) and Markus Roggenbach (Swansea University, UK). It targets refinement proofs for infinite state systems, which may also involve infinite non-determinism. This repository rewrites its theory files (`CSP`, `CSP_T`, `CSP_F`, `FNF_F`, `DFP`, and the example developments) in Lean.

## Contents

The directory layout of the Isabelle version is preserved: each theory `X.thy` corresponds to `LeanCspProver/<dir>/X.lean`.

| Directory | Contents |
| --- | --- |
| `LeanCspProver/CSP/` | The semantics-independent core: traces, CPOs, complete metric spaces, fixed points, CSP syntax |
| `LeanCspProver/CSP_T/` | Instantiation for the traces model T (semantics, monotonicity, continuity, algebraic laws, tactics) |
| `LeanCspProver/CSP_F/` | Instantiation for the stable-failures model F |
| `LeanCspProver/FNF_F/` | Full normalisation for F |
| `LeanCspProver/DFP/` | Deadlock freedom proofs (the Roscoe–Dathi theory) |
| `LeanCspProver/ep2/` | Example: the ep2 electronic payment system |
| `LeanCspProver/DM/` | Example: the Dining Mathematicians |
| `LeanCspProver/SA_Kung/` | Example: Kung's systolic array (on top of DFP) |
| `LeanCspProver/NBuff/` | Example: n one-buffers linked together |
| `LeanCspProver/UCD/` | Example: the Uniform Candy Distribution puzzle |
| `LeanCspProver/Test/` | Small examples and sanity checks |

`LeanCspProver.lean` is the root module; it imports everything from `CSP` through `DFP` along with most of the examples. `Test`, `UCD`, and `NBuff/NBuff.lean` are not reachable from the root module, so build them individually if you need them.

No `sorry` remains in the translated proofs.

## Building

With [elan](https://github.com/leanprover/elan) installed, the toolchain is resolved automatically from `lean-toolchain` (currently `leanprover/lean4:v4.29.0-rc4`).

```console
$ lake exe cache get   # fetch prebuilt Mathlib artifacts — you want this
$ lake build
```

Because the project depends on Mathlib, a first build without the cache takes a very long time.

To check a single file:

```console
$ lake build LeanCspProver.CSP_F.CSP_F_law_basic
```

## Usage

As in the Isabelle version, you rewrite refinement relations using the algebraic laws of `CSP_T` / `CSP_F` together with the `cspT_*` / `cspF_*` tactics (`LeanCspProver/CSP_T/CSP_T_tactic.lean`, `LeanCspProver/CSP_F/CSP_F_tactic.lean`). The developments under `LeanCspProver/Test/`, `LeanCspProver/DM/`, and `LeanCspProver/ep2/` are the best starting points for seeing how a proof is put together.

For the theory behind CSP-Prover and the general proof methodology, see the original [User Guide CSP-Prover](https://staff.aist.go.jp/y-isobe/CSP-Prover/CSP-Prover-5-0-2009/User-Guide-5-0.pdf) and the references below.

## X-symbols

The Isabelle version expresses the conventional CSP operators using X-symbols, and separates their declarations into `CSP_*_xsymbols` so that they do not cause syntax warnings elsewhere. That split is carried over here: `CSP_Main` / `CSP_T_Main` / `CSP_F_Main` hold the definitions and theorems, while `CSP` / `CSP_T` / `CSP_F` add the notation on top of them.

## Licence

This repository is a derivative work of CSP-Prover and is distributed under the same **CSP-Prover licence agreement**, a licence similar to the LGPL. The full text is in [LICENSE](LICENSE). You have to agree with the licence before using this software.

As required by section 3 of that licence, the original licence providers, the nature of the modification, and its date are recorded in [NOTICE](NOTICE).

- Original: CSP-Prover 5-1-2020 — Yoshinao Isobe (AIST, Japan), Markus Roggenbach (Swansea University, UK)
  - <https://github.com/yoshinao-isobe/CSP-Prover>
  - <https://staff.aist.go.jp/y-isobe/CSP-Prover/CSP-Prover.html>
- Licence providers: National Institute of Advanced Industrial Science and Technology (AIST) and University of Wales Swansea (UWS)
- Modification: translation to Lean 4, from March 2026 onwards, by Yuki Kokubun

Any copyright arising from the translation is placed under the same licence, following section 3 (3) of the agreement.

## References

1. Y. Isobe and M. Roggenbach: A generic theorem prover of CSP refinement, TACAS 2005, LNCS 3440, Springer, pp.108–123, 2005.
2. Y. Isobe and M. Roggenbach: A complete axiomatic semantics for the CSP stable-failures model, CONCUR 2006, LNCS 4137, Springer, pp.158–172, 2006.
3. Y. Isobe and M. Roggenbach: CSP-Prover — a Proof Tool for the Verification of Scalable Concurrent Systems, Journal of Computer Software (JSSST), Vol.25, No.4, pp.85–92, 2008.
4. Y. Isobe, M. Roggenbach, and S. Gruner: Extending CSP-Prover by deadlock-analysis — Towards the verification of systolic arrays, FOSE 2005, pp.257–266, Kindai-kagaku-sha, 2005.
5. A. W. Roscoe: *The Theory and Practice of Concurrency*, Prentice Hall, 1998.
6. A. W. Roscoe and N. Dathi: The pursuit of deadlock freedom, *Information and Computation*, Vol.75, No.3, pp.289–327, 1987.
