<h1 align="center">The plane quartic of Furio and Lombardo has exactly four rational points</h1>

<p align="center">
  <a href="https://github.com/mt0-svg/furio-lombardo-quartic/actions/workflows/ci.yml"><img alt="CI" src="https://github.com/mt0-svg/furio-lombardo-quartic/actions/workflows/ci.yml/badge.svg"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

Furio and Lombardo conjectured ([Proc. Lond. Math. Soc. 2026](https://doi.org/10.1112/plms.70193); [arXiv:2507.17967](https://arxiv.org/abs/2507.17967), Conjecture 1.6) that the plane quartic

```math
C:\ x^4 + 3x^3y - 3x^2yz - 3x^2z^2 + 6xy^3 - 6xy^2z + 3xyz^2 - 2xz^3 + 4y^4 + 2y^3z - 5yz^3 = 0,
```

the twist $`X_{E_3}`$ of the Klein quartic left open in their classification of the $`7`$-adic images of Galois for elliptic curves over $`\mathbb{Q}`$, has exactly the four rational points $`[0:0:1]`$, $`[1:1:1]`$, $`[2:0:1]`$, $`[-1:0:1]`$. We prove it, with a descent over a number field of degree $`21`$ and Stoll's Selmer group Chabauty at one $`2`$-adic place, applied to the Jacobians of genus $`2`$ curves that are the Prym varieties of two étale double covers of $`C`$.

```lean
theorem FurioLombardo.conjecture_1_6 : FurioLombardo.Conjecture
```

## What is checked

- **Lean 4**: the theorem, with Mathlib, no `sorry`, no `native_decide`, and only the axioms `propext`, `Classical.choice` and `Quot.sound`. Every finite computation of the proof, from the class number certificate to the boxes that cover the $`2`$-adic points of $`C`$, is checked by the Lean kernel, mostly with `decide +kernel`, so no compiled code is trusted. Comparator replays the proof in the Lean kernel and checks the theorem against the statement of `FurioLombardo/Challenge.lean`, which imports only Mathlib. The paper names the Lean declaration of each numbered statement.
- **Computation**: the certificates that the kernel checks were written by PARI/GP scripts and by Lean programs run outside the proof (`code/`). To guard against a bug in the PARI/GP programs that first computed the local group at the $`2`$-adic place and the covering of $`C(\mathbb{Q}_2)`$, a second program written separately in Sage recomputes the logarithms, the lattice and its saturation, the leading classes at the 104 centres and the bounds on the boxes, and agrees at every centre and every box. It takes the exact data, the local points, the list of boxes, the local Selmer image and one matrix of the logarithm from the first programs, and it does not redo the independence of the local points. Another Sage program redoes the descent over the field of degree $`21`$ and finds the same two classes. The details are in section 9 of the paper and in `code/README.md`.

The workflow `ci.yml` checks the Lean part at each push, on GitHub's runners: it builds the package from source, prints the axioms of `FurioLombardo.conjecture_1_6` and of `FurioLombardo.Discharge.M4Box.onlyFourPoints` and fails on any axiom other than these three, scans the sources for `sorry`, `admit` and `native_decide`, and runs Comparator. On a tag, `release.yml` runs the same checks and attaches the PDF, the logs of the checks and the build archive to the release only if they all pass.

## Layout

| Path                                                                         | Content                                                                                                                                                                                                                                                            |
| ---------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `FurioLombardo/`                                                             | the Lean proof (Lean and Mathlib `v4.34.1`): `Main.lean` proves the theorem; `Vendor/` holds the modules copied from other projects (Built on lists them, with the files adapted from them elsewhere) and, in `Vendor/Toolbox/`, 16 modules written for this proof |
| `FurioLombardo/Statement.lean`                                               | the definitions of the statement, its open part `OnlyFourPoints` and their equivalence                                                                                                                                                                             |
| `FurioLombardo/Challenge.lean`, `FurioLombardo/Solution.lean`, `config.json` | the statement with `sorry`, its proof, and the Comparator configuration                                                                                                                                                                                            |
| `paper/`                                                                     | the TeX source and `small_checks.gp`                                                                                                                                                                                                                               |
| `code/`                                                                      | the programs that wrote the certificates, the second implementations and the earlier PARI/GP computations, each with its recorded output; `code/README.md` maps each directory to the part of the paper it serves                                                  |

The vendored extensions of the Mathlib API keep their Mathlib namespaces (`IsDedekindDomain`, `Valuation`, `Polynomial`, ...), as in their sources, so that dot notation works.

## Check and reuse

Fast check, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -f .lake/build/lib/lean/FurioLombardo/Challenge.* .lake/build/ir/FurioLombardo/Challenge.*
# then Comparator, as .github/workflows/ci.yml runs it
```

Full check, from source:

```sh
lake exe cache get && lake build
```

Some check modules need several GB of memory each while they build; `code/formal-proof/clean_build.sh` builds the package in dependency order with these modules a few at a time, as `ci.yml` does (its header lists its settings).

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "furio-lombardo-quartic"
git = "https://github.com/mt0-svg/furio-lombardo-quartic"
rev = "v1.0"
```

then `lake update furio-lombardo-quartic`, `lake exe cache get` and `lake build`, which downloads the build archive of the release.

The computations: `code/README.md` gives the command of each script and its recorded running time.

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and [landrun](https://github.com/zouuup/landrun): the check of the statement in CI.
- [EllipticCurves](https://github.com/MichaelStollBayreuth/EllipticCurves) of Michael Stoll (Apache 2.0), commit `1e4709496a2c0cb3da66b400efbb15939358d444`: fractional ideals, $`S`$-integers and Selmer groups in `FurioLombardo/M1/Vendor/Stoll/` (copies of `EllipticCurves/Mathlib/{Basic,FractionalIdeal,SIntegers,SelmerGroup}.lean`, module paths and namespaces renamed, no other change); the factorization of fractional ideals in `FurioLombardo/M3b/Factorization.lean` (adapted from `EllipticCurves/Mathlib/FractionalIdeal.lean`, declarations renamed, two lemmas added); formal group laws and their logarithms in `FurioLombardo/Vendor/Toolbox/Stoll/Mathlib/Chabauty/` (15 files, copies of `EllipticCurves/Mathlib/Chabauty/`, which Stoll took from his Chabauty project; module paths and the namespace `ChabautyColeman` renamed, no proof changed).
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (Apache 2.0): local fields (uniformizers, normalized valuations, squares, finite extensions) in `FurioLombardo/Vendor/Toolbox/TauCeti/` (35 files of commit `b5174264c00450f3f38976fe8b4a6fc573811c5e`, same paths under `TauCeti/`; namespace renamed, three data instances scoped, three lemmas renamed with a prime, no proof changed); the integral closedness of the coordinate ring in `FurioLombardo/M3a/CoordRing.lean` and `FurioLombardo/M3a/Dedekind.lean` (adapted from `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/CoordinateRing.lean` of commit `ae983b7a7f37dab9ee586c432db940e69248cb97`, from Weierstrass equations to $`Y^2=f`$).
- [AINTLIB](https://github.com/CBirkbeck/AINTLIB) of Chris Birkbeck (Apache 2.0), commit `8ad96111e05bb40552614d08c52eaa6b047b54e6`: the completed Dedekind zeta function, used in the proof of Zimmert's bound, in `FurioLombardo/Vendor/AINTLIB/CompletedZeta/` (the 16 files of `projects/DedekindResidue/DedekindResidue/CompletedZeta/`; module paths and the namespace `DedekindResidue` renamed, no other change).
- [Lean Pool](https://github.com/Vilin97/lean-pool) (Apache 2.0), commit `504c1718290248c7eba3e05b3e71624fa7cee7fc`: contour integrals over rectangles, used in the proof of Zimmert's bound, in `FurioLombardo/Vendor/LeanPool/RectangleIntegral.lean` (a copy of `LeanPool/Odlyzko/FromPrimeNumberTheoremAnd/RectangleIntegral.lean`, a file of the FLT Project adapted from `ResidueCalcOnRectangles.lean` of the PNT+ project of Kontorovich and Tao; module renamed, no other change).
- [PARI/GP](https://pari.math.u-bordeaux.fr/) and [SageMath](https://github.com/sagemath/sage): the certificates, the second implementations and the small checks.

## Citation

```bibtex
@misc{furio-lombardo-quartic,
  title     = {The plane quartic of {F}urio and {L}ombardo has exactly four rational points},
  author    = {{mt0-svg}},
  year      = {2026},
  url       = {https://github.com/mt0-svg/furio-lombardo-quartic}
}
```

## Contact

Questions and corrections: [open an issue](https://github.com/mt0-svg/furio-lombardo-quartic/issues/new/choose).

## License

Apache 2.0 (`LICENSE`, `NOTICE`).
