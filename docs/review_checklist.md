# Phase 4 internal technical review

**Disposition: technical review completed. The lead closed the final figure-label defect in the sign-off below.** This is an independent internal QA handoff, not external peer review, blanket human manuscript signoff, author-eligibility determination, or lead verification. No Lake builds were run during this review. Lead verification is to be appended separately.

Reviewed the revised eight-page [manuscript PDF](../paper/main.pdf), modified 2026-11-27 11:50:47 Asia/Shanghai, SHA-256 `bc11f4627dc024d1ad0fb107599ce2a1dbc2b112466ed66acbfc31baec8157b1`; current [main.tex](../paper/main.tex) SHA-256 `54ba6a694b1fc5af8bf435c9b31b5cbec175a858e6b33ea2720a3daf4b292413`. The PDF is newer than the source and the previously reviewed 11:44 PDF. If files change, lead verification must identify the new hashes.

## Finding for D/F and lead

- [ ] **Figure 2, page 3:** the filled first product cell is drawn over the end of the label `A(B) C(B) =`, hiding the closing characters. Its two input labels also touch their cells. Move the label anchor left of the left edge of the widest cell, or shift the rows right, and re-render the figure. The coefficient entries themselves are now separated and readable. This is a diagram legibility defect; it does not change the checked arithmetic. Evidence: [figure source](../paper/figures/packing.tex) and the PDF page 3. The TeX overfull-box log does not detect this TikZ overlap.

## Resolution of first-pass findings

- [x] **Text collisions:** prior long identifiers, height sum, runner-up integer and gain fraction no longer overlap columns or margins in the revised PDF. Inspected all eight pages; the current build log reports no overfull boxes. The Figure 2 label issue above remains.
- [x] **Benchmark methods:** the revised paper states that host background activity was uncontrolled and unrecorded, each module bar is one command, and timing variation has no established cause. Figure 4's caption no longer calls distinct-command differences repeated-run variation. The direct baseline is described as unrolled source with different representation and reduction paths, without general scaling or full-size direct-verifier claims. [Main](../paper/main.tex) · [timing figure](../paper/figures/timing.tex) · [raw index](../benchmarks/results/20261127T033045Z/measurements.jsonl).
- [x] **Product-only trials:** the paper's median 8.14 s, range 4.30–8.70 s and largest RSS 954.3 MiB agree with the five `ProductOnly` rows; the five matched import controls are separately reported. These are whole fresh Lean processes with prebuilt imports, not isolated kernel-arithmetic times. [Raw trials](../paper/validation/product-only.jsonl).
- [x] **Parent provenance:** independently fetched the [official node](https://csd.aon.network/proposal/0x61ac9b0230694a2da6c369e7518c7ad186d2613659f85b1ae9c2b6f1f8f13b7e); its response contains `After Blob` and the ArDrive ID recorded in [parent-provenance.json](../paper/validation/parent-provenance.json). The direct ArDrive response was 25,942 bytes, SHA-256 `89916aefb6c59e745f1efa224e11f26c663bc5e002384beff15064891caba686`, matching the local archived parent. This establishes the observed record/data linkage and the literal lineage note, not an independent reconstruction of the full search history.
- [x] **Human contribution disclosure:** revised closing section records the user's reported research contributions, line-by-line review of `Spec` and `Main`, and execution of build/replay. This is not a claim of blanket human manuscript signoff; this review does not decide author eligibility.

## Mathematical and verification boundaries checked

- [x] Both offline verifiers passed on the certificate. Exact $U=2462273619527794579322422405079/6465103708838880000000000000000$; parent minus $U=2468195140225859198307/2155034569612960000000000000000$. [Certificate](../certificate.json) · [direct audit](../audit_verify.py).
- [x] 9,408 heights; 18,815 encoded interior coefficients and 18,817 vertices including zero endpoints. For `g(x−s)`, lag −2284 gives shift −571/1176; plus-shift reverses the sign. Direct Python checks uniqueness; Lean proves the all-shift bound and attaining value, not exhaustive uniqueness. [Numerical](../Overlap/Numerical.lean) · [Main](../Overlap/Main.lean) · [audit](../audit_verify.py).
- [x] Base $2^{128}$; the actual Lean sufficient hypothesis is $N^2D^2<B$ (118 bits); $ND^2$ (105 bits) is the tighter descriptive bound. [Algebra](../Overlap/Algebra.lean) · [metrics](../paper/generated/metrics.json).
- [x] `witness_supremum_exact` and `continuous_upper_bound` are unconditional in the stated Lean setting; `discrete_upper_bound_of_white` has both `hc` and `WhiteBridge`. The latter already states convergence to `continuousConstant`; its correspondence to the published result is mathematical interpretation, not a Lean proof of the external theorem. [Spec](../Overlap/Spec.lean) · [Main](../Overlap/Main.lean) · [axiom capture](../paper/validation/axioms.txt).
- [x] Fresh-process `leanchecker` invokes Lean's own kernel with compiled imports; it is not an independent kernel. The concrete product is axiom-free, `peak_digit` uses `propext`, and the headline results use the recorded standard Lean axioms. The conditional premise is a theorem argument, so it need not appear in the printed axiom list.
- [x] The worked-example arithmetic, sample counts, parent-lift example, runner-up and cited numerical tables were checked against current data and logs. The new [toy example](../scripts/PearlExample.lean) and [recorded axiom output](../paper/validation/toy-example.txt) support the new source claim; no fresh Lake build was run.
- [x] Fifteen bibliography entries were inventoried; accessible sources and relevant passages were spot-checked. White's journal title is correct even though its linked arXiv preprint has a different title. The Erdős original, Bloom catalogue and full Haugland 1996 text could not be fetched by the web reader; Haugland metadata and abstract were available via search. This is not an exhaustive independent mathematical verification of every cited publication.

## Lead handoff

Fix the Figure 2 label and verify the resulting PDF and hashes. The current TeX log also includes acmart reference-format/CCS and balance warnings; venue-specific submission formatting remains outside this technical review. No commits or publication were performed.

## Lead verification of the delivery

The final diagram places all three row labels to the left of their cells. A full-page render and a magnified render of page 3 show all three equal signs and the first coefficient of each row. The remaining internal review finding is closed.

The extracted reviewer archive produced an eight-page PDF in a clean TeX build. Every page has the same extracted text as the delivered manuscript. Both builds resolved all 15 bibliography entries, with zero overfull boxes, unresolved citations or unresolved references. The anonymous SIGPLAN settings retain class notices about publication metadata, vertical spacing and last-page balance. The final pages were visually inspected. The figures, main text and auxiliary sources in the archive match the repository byte for byte.

A separate clean project build from the packaged proof sources passed using the pinned, previously fetched dependencies, followed by successful replay of each of the eight core modules, both Python verifiers and regeneration checks for the static paper metrics. The proof and certificate inputs used for that rehearsal match the final archive by exact byte comparison. The independent digit controls and the miniature worked example passed on this toolchain.

| File | SHA-256 |
| --- | --- |
| `paper/main.pdf` | `55d1fd3d4655a595036a81735711efbb714145505900eed893f69bc962cc4df8` |
| `paper/main.tex` | `54ba6a694b1fc5af8bf435c9b31b5cbec175a858e6b33ea2720a3daf4b292413` |
| `paper/figures/packing.tex` | `f3bbca003d2681a34f7a26ffb584eb4169292815aa350f7209f5e1f18674b44a` |
| `paper/reviewer-supplement.zip` | `e337172a3f923b35184aa0dc118caef7a299a9d6fa4a3c36a8e98b157dfee2fc` |

The human contribution statement records the contributor's account of their own work. This sign-off covers the technical package and typeset manuscript. Selection of an open call and submission of the manuscript remain with the author.
