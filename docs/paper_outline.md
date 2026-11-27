# Paper architecture

This outline records the original Proof Pearl design. The regular-paper revision, including the convergence proof and matched Linux benchmarks, is in the [current manuscript](../paper/main.tex).
## Editorial decision

Prepare an anonymous, two-column ACM SIGPLAN Proof Pearl, aimed at an audience that knows proof checking but may not know minimum overlap. The operative question is how a cheaply checked equality between three natural numbers can certify a supremum taken over real shifts. State the theorem for one witness before discussing the discrete application. The numerical improvement is a provenance check. The CPP 2027 call specifies 10-point review copy and a limit of 12 body pages. Aim for 8–10 pages overall. The [CPP call](https://popl27.sigplan.org/home/CPP-2027) is a formatting reference for a later submission. See the venue and human authorship notes in [the reproduction guide](../paper/REPRODUCE.md).

## Evidence informing the design

The [proof audit](audit_report.md) distinguishes the axiom-free ground product from the index lookup and the real analysis theorems. [Static measurements](../paper/generated/metrics.json) give different actual lengths for the two operands, and 118 bits suffice for the deliberately loose formal coefficient bound. The [bibliography](../paper/references.bib) places the contribution between search, fast multiplication, and reflection. The measured run separates import costs, clean builds, ground decision procedures and selected-module replay. Only the finished measurement logs may supply timings. A small slice is meaningful only if it contains nonzero products.

## Manuscript plan

1. **Problem and result.** Start at the proof obligation. Specify the mass-one convention on a support interval of length two. Distinguish the witness supremum, the infimum over admissible profiles, and the limit of discrete minima.
2. **Certificate contract.** Give the sign convention, reversed complement, units and exterior zeros. Derive the event index from the exponents. Explain why balanced trees are useful and which operations still occur outside the one principal multiplication.
3. **Soundness and a falsification example.** Pair the product equality with equal digit count and bounds on both lists. Explain the padding ambiguity with a worked example. State the uniform bound used in Lean and the tighter elementary bound separately. Use actual operand and product lengths only as descriptive data.
4. **Returning to real shifts.** Integrate two half-open indicators and derive the two surviving diagonals at a fractional shift. Cover endpoints and shifts outside support, floor decomposition for negative shifts, general signed heights, and admissibility. Use an explicit line between the unconditional continuous result and the two convergence premises.
5. **Evaluation and replay.** Provide commands and measured clean build, individual module checks, RSS, replay scope, a nondegenerate small instance, paired direct/packed baseline where available, and the wrong-digit and padded-length rejection tests. Distinguish checking a declaration from checking imported dependencies and the shared kernel implementation. Include independent Python enumeration and the sign/uniqueness boundary.
6. **Related work, limits and disclosure.** Reference the actual parent, the continuous equivalence, standard packing and reflection. Outline the reusable pieces and the small remaining device-specific work for another profile. Distinguish the human contributor’s reported specification review and independent replay from the machine-generated proof scripts and manuscript drafting.

## Scope decision

Prefix experiments and falsification controls help identify costs and validate preconditions with little new theory. They justify deeper evaluation within a pearl. A regular-paper expansion would need a broader workload or independently verified general-purpose tooling. Formalizing the whole limit bridge would be a separate mathematical development. Neither extension is required for the unconditional continuous result. The current manuscript does not claim an asymptotic implementation comparison, Lean-verified uniqueness, a new convolution algorithm, or a solved open problem.
