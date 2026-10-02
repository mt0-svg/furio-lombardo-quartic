<h1 align="center">The plane quartic of Furio and Lombardo has exactly four rational points</h1>

<p align="center">
  <a href="https://zenodo.org/records/23098205/files/furio-lombardo-quartic.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.23049094"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23049094.svg"></a>
  <a href="https://mt0-svg.github.io/furio-lombardo-quartic/run.html"><img alt="Lean Proved" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ffurio-lombardo-quartic%2Fbadges%2Flean.json"></a>
  <a href="https://mt0-svg.github.io/furio-lombardo-quartic/run.html"><img alt="Lean Comparator" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ffurio-lombardo-quartic%2Fbadges%2Fcomparator.json"></a>
  <a href="https://mt0-svg.github.io/furio-lombardo-quartic/run.html"><img alt="Computation Certificates" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ffurio-lombardo-quartic%2Fbadges%2Fcertificates.json"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

Furio and Lombardo conjectured that the plane quartic curve

```math
x^4 + 3x^3y - 3x^2yz - 3x^2z^2 + 6xy^3 - 6xy^2z + 3xyz^2 - 2xz^3 + 4y^4 + 2y^3z - 5yz^3 = 0,
```

a twist of the Klein quartic that arises in their classification of the $`7`$-adic images of Galois for elliptic curves over $`\mathbb{Q}`$, has exactly four rational points. We prove this. A descent over a number field of degree $`21`$ lifts every rational point to one of two étale double covers of the curve. The Prym varieties of these covers are Jacobians of genus $`2`$ curves, and Stoll's Selmer group Chabauty at one $`2`$-adic place, applied to them, leaves only the four known points. The proof is formalized in Lean 4 with Mathlib. With the work of Furio and Lombardo, it completes the classification of the $`7`$-adic images.

This is Conjecture 1.6 of Furio and Lombardo ([Proc. Lond. Math. Soc. 2026](https://doi.org/10.1112/plms.70193); [arXiv:2507.17967](https://arxiv.org/abs/2507.17967)). The four points are

```math
[0:0:1],\qquad [1:1:1],\qquad [2:0:1],\qquad [-1:0:1].
```

```lean
theorem FurioLombardo.conjecture_1_6 : FurioLombardo.Conjecture
```

## What is checked

- **Lean 4.** `FurioLombardo.conjecture_1_6` has no hypothesis and uses only the axioms `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no `native_decide`. The kernel checks every finite computation of the proof, from the class number certificate to the boxes that cover $`C(\mathbb{Q}_2)`$, so no compiled code is trusted. Comparator checks the theorem against `FurioLombardo/Challenge.lean`, which imports only Mathlib, and nanoda, an implementation of the Lean kernel written separately, checks the whole proof again (timed alone on a GitHub hosted runner with 4 CPUs, on tag v1.1.0, whose Lean code is that of this version up to comments: 1 min 26 s for the export it reads, 56 min 52 s for nanoda; the job logs and `comparator_time.out` are in `code/formal-proof`). Each proof of the paper that rests on Lean ends with the name of its main declaration; [`STATEMENTS.md`](STATEMENTS.md) gives, for each numbered statement, its Lean declarations, and for each section that reports a computation, its scripts and recorded outputs.
- **Second programs.** The certificates were written by PARI/GP scripts and Lean programs (`code/`). Two programs written separately in Sage redo parts of them. One redoes the descent over the field of degree $`21`$ and finds the same two classes. The other recomputes the $`2`$-adic logarithms, the lattice and its saturation, the leading classes at the 104 centres and the bounds on the boxes, and agrees everywhere; it starts from the exact data, the local points, the boxes and the local Selmer image of the first programs, and does not redo the independence of the local points. Details: section 9 of the paper and `code/README.md`.

`ci.yml` starts from an earlier build when one is available, the last one in its cache or else the one attached to the latest release, and compiles only the modules that changed since and those that import them; the Lean kernel checked each declaration when its module was compiled, in this run or in an earlier one. It fails on any axiom other than these three, scans the sources for `sorry`, `admit` and `native_decide`, and runs Comparator, which has every declaration that the main theorem depends on, those of Mathlib included, checked again by nanoda. This happens in every run that builds the development, whatever earlier build it started from, and in this configuration (`config.json`, `lean_kernel` false) the Lean kernel does not check these declarations a second time. `release.yml` makes the release of a tagged commit that has a green CI run started by hand: it attaches the PDF, which `paper.yml` compiles from the tagged sources, and, taken from that CI run without compiling the Lean code again, the logs of the checks and the Lake build that Comparator checked. A run started by hand on `main` writes the three badges above from its jobs: the hypotheses and axioms of the main theorem (`code/formal-proof/facts.lean`), the Comparator check, and the jobs that rerun the computations (the Sage second implementations, `code/second-implementations/rerun.sh`). A build of the development from an empty build directory, on the machine of the paper, is recorded in `code/formal-proof` (`clean_build.out`, summarized in `clean_build_summary.out`; see `code/README.md`).

## Layout

| Path                                                                         | Content                                                                                                                                                                                                                                                            |
| ---------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `FurioLombardo/`                                                             | the Lean proof (Lean and Mathlib `v4.34.1`): `Main.lean` proves the theorem; `Vendor/` holds the modules copied from other projects (Built on lists them, with the files adapted from them elsewhere) and, in `Vendor/Toolbox/`, 16 modules written for this proof |
| `FurioLombardo/Statement.lean`                                               | the definitions of the statement, its open part `OnlyFourPoints` and their equivalence                                                                                                                                                                             |
| `FurioLombardo/Challenge.lean`, `FurioLombardo/Solution.lean`, `config.json` | the statement with `sorry`, its proof, and the Comparator configuration                                                                                                                                                                                            |
| `paper/`                                                                     | the TeX source, `small_checks.gp` (the search of the introduction) and `statement_map.sh` (which writes `STATEMENTS.md`)                                                                                                                                           |
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
rev = "v1.2.0"
```

then `lake update furio-lombardo-quartic`, `lake exe cache get` and `lake build`, which downloads the build archive of the release.

The computations: `code/README.md` gives the command of each script and its recorded running time.

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and [landrun](https://github.com/zouuup/landrun): the check of the statement in CI.
- [nanoda](https://github.com/ammkrn/nanoda_lib) of Chris Bailey (Apache 2.0), commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`: the second implementation of the Lean kernel, built by the CI, which Comparator runs to check again every declaration the theorem depends on.
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
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23049094},
  url       = {https://doi.org/10.5281/zenodo.23049094}
}
```

## Contact

Questions and corrections: [open an issue](https://github.com/mt0-svg/furio-lombardo-quartic/issues/new/choose).

## License

Apache 2.0 (`LICENSE`, `NOTICE`).
