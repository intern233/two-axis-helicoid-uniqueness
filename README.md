# Uniqueness of the two-axis genus-one helicoid

**English** | [简体中文](README.zh-CN.md)

This repository contains the paper on uniqueness of the two-axis genus-one helicoid and its accompanying Lean 4 formalization.
The `two-axis-helicoid-uniqueness/` directory containing this file is the GitHub repository root.
The complete manuscript entry point is [`TwoAxisHelicoidManuscript.lean`](TwoAxisHelicoidManuscript.lean), with **8,419 project modules** and approximately **4.11 GiB** of source code.
The many `TraceData*.lean` files contain computational certificates checked by the Lean kernel and are part of the proof source.

## Background

Matthias Weber, David Hoffman and Michael Wolf proved embedded existence in *An embedded genus-one helicoid*, *Annals of Mathematics* **169** (2009), 347–448 ([DOI](https://doi.org/10.4007/annals.2009.169.347), [publisher PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v169-n2-p01.pdf)). Their Theorem 1 and Conjecture 1 on p. 351 give the existence result and state the corresponding embedded uniqueness conjecture; their definition (1) on p. 350 includes a vertical axis and a horizontal straight line.

This project addresses that uniqueness problem with both axes retained and with the explicit single-sheeted C¹ helicoidal graph-end condition in Section 1 of the accompanying paper. See [Entry points and theorem scope](#entry-points-and-theorem-scope) for the precise formal hypotheses.

## Paper

*Uniqueness of the two-axis genus-one helicoid*

| File | Contents |
| --- | --- |
| [Paper PDF](paper/two-axis-helicoid-uniqueness.pdf) | Complete typeset paper, 22 pages |
| [Paper Markdown](paper/two-axis-helicoid-uniqueness.md) | Readable and editable manuscript source |

The English paper is included in `paper/` alongside the formalization. Section 9 explains the correspondence between the mathematical statements, Lean definitions, verification results, and their scope. Appendix A describes the computational certificates and reproduction procedure. This is a working manuscript; author and final citation information remain to be supplied.

## Environment

| Component | Pinned version |
| --- | --- |
| Lean | `4.35.0`, specified by `lean-toolchain` |
| Lean compiler commit | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Transitive mathlib dependencies | Pinned by `lake-manifest.json` |

The project has been verified on Linux x86-64. You need Git, [elan](https://github.com/leanprover/elan), and network access to GitHub and the mathlib cache service.
Lean, mathlib, third-party sources, and compilation caches are downloaded by the build tools and are not bundled in this directory.
Allow additional disk space and memory for dependencies and build outputs; the 4.11 GiB figure refers only to project source code.

## Build and audit

Clone the repository, then build and audit it:

```bash
git clone https://github.com/intern233/two-axis-helicoid-uniqueness.git
cd two-axis-helicoid-uniqueness
elan toolchain install leanprover/lean4:v4.35.0
lake exe cache get
lake build
lake env lean tools/StatementCheck.lean
lake env lean tools/Audit.lean
```

`lake exe cache get` downloads precompiled mathlib dependencies; `lake build` compiles this project.
The default build includes both root modules, `TwoAxisHelicoid` and `TwoAxisHelicoidManuscript`, and their recursive dependencies. Numerical certificates do not need to be regenerated.
Keep the committed `lake-manifest.json` when reproducing the build; running `lake update` is unnecessary.
The project does not require the original workspace, a VPN, a server account, or machine-specific absolute paths.

If the curl executable used by `cache get` reports an OpenSSL certificate-file path error, set `CURL_CA_BUNDLE` to an existing system CA certificate file. For example, on a RHEL/CentOS system where this file exists:

```bash
CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt lake exe cache get
```

`StatementCheck.lean` checks the complete types of five main conclusions and prints their axiom dependencies.
`Audit.lean` visits every declaration in the `TwoAxisHelicoid` namespace imported by the manuscript entry point. It checks that their axiom dependencies are limited to
`propext`, `Classical.choice`, and `Quot.sound`, and that 617 manuscript witness declarations exist and are neither axioms nor unsafe declarations.
A failed check causes Lean to return a nonzero exit code.

## Entry points and theorem scope

| Source file | Contents |
| --- | --- |
| [`TwoAxisHelicoidManuscript.lean`](TwoAxisHelicoidManuscript.lean) | Unified entry point for the manuscript, original-path interval certificates, and appendices |
| [`TwoAxisHelicoid/ManuscriptGeometricTheoremOneOne.lean`](TwoAxisHelicoid/ManuscriptGeometricTheoremOneOne.lean) | Geometric main theorem, `TwoAxisHelicoid.manuscript_geometric_theorem_one_one` |
| [`TwoAxisHelicoid/ManuscriptTheoremOneOne.lean`](TwoAxisHelicoid/ManuscriptTheoremOneOne.lean) | Main uniqueness theorem in normalized and physical coordinates |
| [`tools/StatementCheck.lean`](tools/StatementCheck.lean) | Checks of the main statements, an embedded representative, and spherical Gauss fibers on the same cap |
| [`tools/Audit.lean`](tools/Audit.lean) | Axiom audit of all imported project declarations and manuscript witness checks |
| [`source_inventory.json`](source_inventory.json) | Paths, sizes, SHA-256 hashes, and project imports for all 8,419 proof modules |

The main theorem concerns the surface class explicitly specified in Sections 1 and 2.2 of the original proof draft: smooth, properly embedded minimal surfaces containing two complete straight axes, with the topology of a once-punctured torus and a single-sheeted C¹ helicoid normal graph outside compact sets.
The types and proofs can be inspected directly in the Lean files above.
Some end-structure reductions for broader surface classes, and the full geometric compactness theorem in Appendix B.3, still appear with explicit literature inputs or hypotheses. The alternative compactness route in Appendix B.3 is not a dependency of the main uniqueness theorem.

## Source snapshot

This directory contains the complete dependency graph of the manuscript entry point, with module and namespace names based on the mathematical subject. After a file-by-file check of the uniform renaming, a full server rebuild found an unfinished additive simplification. An explicit `add_assoc` was added in `SpinGeneratorCoreRetraction.lean`, and the module was successfully recompiled. Mathematical definitions and theorem statements were unchanged.
`source_inventory.json` covers the 8,419 proof modules, excluding the two standalone check files.
Historical experiments, unused older certificate modules, logs, build outputs, and machine configuration from the original workspace are not included.
Build outputs and local caches are listed in `.gitignore`.

On 27 November 2026, all 8,419 project modules were compiled from source under the publication names using standard Lake on a Linux server. The build started with an empty project output directory; resumed runs reused only project outputs produced during that build. mathlib used its pinned precompiled dependency cache.
The five main statement checks, the axiom audit of 368,507 project declarations, and all 617 manuscript witness checks subsequently passed, using only the three standard axioms above. A final `lake --no-build build` confirmed that all targets were up to date.
Use the commands above to reproduce the checks. Concurrency can be set with `LEAN_NUM_THREADS`; the later stages of the recorded build used 64 worker threads.

## Publication metadata

No open-source license has yet been specified for this snapshot. Before a formal release, the rights holder should determine the license, authorship, and citation information.
Third-party dependencies retain their respective licenses.
